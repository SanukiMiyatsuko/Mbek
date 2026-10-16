import Std.Data.HashMap
import Mbek.TableAnalysis.Core

/-!
# 表解析ツール: 検査と推定

* 表（CSV）の読み込み
* 順序同型の検査（単調性・全対比較）
* 基本列の同期（FS 同期）の解析とオフセット `k` の推定
* FS 閉包：同期している行から派生対応 `(a[n], b[n+k])` を生成し、表と矛盾しないか確かめる
* 対応先の推定：類推（編集の転写）と FS 逆算（極限の候補を作り同期/交互性で検証）
-/

namespace TA
open TreeLike OTSys

variable {A B : Type} [OTSys A] [OTSys B]

/-! ## 表の読み込み -/

def parseCSVLine (line : String) : List String := Id.run do
  let cs := line.toList.toArray
  let mut fields : Array String := #[]
  let mut cur := ""
  let mut inQ := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if inQ then
      if c == '"' then
        if i + 1 < cs.size && cs[i+1]! == '"' then
          cur := cur.push '"'
          i := i + 1
        else
          inQ := false
      else
        cur := cur.push c
    else if c == '"' then
      inQ := true
    else if c == ',' then
      fields := fields.push cur
      cur := ""
    else
      cur := cur.push c
    i := i + 1
  return (fields.push cur).toList

structure Row (A B : Type) where
  /-- シート上の行番号（1 始まり） -/
  line : Nat
  a : A
  b : B
  /-- 3 列目（`予想1` など）。空でない行は「予想」として扱い、知識には入れない -/
  note : String

instance : Inhabited (Row A B) := ⟨⟨0, zero, zero, ""⟩⟩

def Row.trusted (r : Row A B) : Bool := r.note.trimAscii.toString.isEmpty

structure Table (A B : Type) where
  rows : Array (Row A B)
  /-- 読めなかった（空でない）行 -/
  skipped : Array (Nat × String)

def loadTable (content : String) : Table A B := Id.run do
  let mut rows : Array (Row A B) := #[]
  let mut skipped : Array (Nat × String) := #[]
  let lines := content.splitOn "\n"
  for (raw, i) in indexed lines do
    let line := raw.replace "\r" ""
    let fs := parseCSVLine line
    let f0 := (fs.getD 0 "").trimAscii.toString
    let f1 := (fs.getD 1 "").trimAscii.toString
    let f2 := (fs.getD 2 "").trimAscii.toString
    if f0.isEmpty && f1.isEmpty then continue
    match parse? f0, parse? f1 with
    | some a, some b => rows := rows.push ⟨i + 1, a, b, f2⟩
    | _, _ => skipped := skipped.push (i + 1, line)
  return ⟨rows, skipped⟩

/-! ## 知識（確定した対応の集合） -/

abbrev KB (A B : Type) := Array (A × B)

def lookA (K : KB A B) (x : A) : Option B := (K.find? (·.1 == x)).map (·.2)
def lookB (K : KB A B) (y : B) : Option A := (K.find? (·.2 == y)).map (·.1)

/-- `x ↦ y` を加えても順序同型が崩れないか -/
def consistent (K : KB A B) (x : A) (y : B) : Bool :=
  K.all fun (a, b) => ltB a x == ltB b y && ((a == x) == (b == y))

/-! ## 基本列の同期 -/

structure Sync where
  /-- `a[n] = a_i`（知識に載っている） -/
  hitsA : List (Nat × Nat)
  /-- `b[m] = b_j` -/
  hitsB : List (Nat × Nat)
  /-- 同じ対応に落ちた `(n, m)` から得たオフセット `m - n` -/
  offsets : List Int

/-- 知識 `K` の添字で、`a`・`b` の基本列がどこに着地するか -/
def syncOf (K : KB A B) (N : Nat) (a : A) (b : B) : Sync := Id.run do
  let fa := (List.range N).map (fund a)
  let fb := (List.range N).map (fund b)
  let idxA (x : A) := K.findIdx? (·.1 == x)
  let idxB (y : B) := K.findIdx? (·.2 == y)
  let hitsA := (List.range N).filterMap fun n => (idxA (fa.getD n zero)).map (n, ·)
  let hitsB := (List.range N).filterMap fun m => (idxB (fb.getD m zero)).map (m, ·)
  let offs := hitsA.flatMap fun (n, i) =>
    hitsB.filterMap fun (m, j) => if i == j then some ((m : Int) - n) else none
  return ⟨hitsA, hitsB, offs.eraseDups⟩

/-- FS 閉包の 1 ラウンド。オフセットが一意な行について、種（n = 0）を除いた
    `(a[n], b[n+k])` を知識に加える。矛盾した派生は `conflicts` に記録する。 -/
def closeOnce (src : Array (A × B)) (N : Nat) (K : KB A B) :
    KB A B × Array (A × B × A × B) := Id.run do
  let mut K := K
  let mut conflicts := #[]
  for (a, b) in src do
    let s := syncOf K N a b
    if let [k] := s.offsets then
      for n in [1:N] do
        let m : Int := n + k
        if m ≥ 1 ∧ m < N then
          let x := fund a n
          let y := fund b m.toNat
          if (lookA K x).isNone && (lookB K y).isNone then
            if consistent K x y then K := K.push (x, y)
            else conflicts := conflicts.push (a, b, x, y)
  return (K, conflicts)

def closure (src : Array (A × B)) (N : Nat) (rounds : Nat := 3) :
    KB A B × Array (A × B × A × B) :=
  (List.range rounds).foldl (fun (K, cs) _ =>
    let (K', cs') := closeOnce src N K
    (K', cs ++ cs')) (src, #[])

/-! ## 類推（編集の転写）

既知の二つの対応 `(a₁,b₁)`, `(a₂,b₂)` の差分を「同じ変形」とみなし、
`a₃ → x` が同じ変形なら `b₃` に B 側の変形を施して `x` の対応先の候補とする。 -/

abbrev EditTable (B : Type) := Std.HashMap String (Array (Edit B))

def buildEdits (K : KB A B) : EditTable B := Id.run do
  let mut m : EditTable B := {}
  for (a1, b1) in K do
    for (a2, b2) in K do
      if let some ea := editOf a1 a2 then
        if let some eb := editOf b1 b2 then
          let key := editKey ea
          let arr := m.getD key #[]
          if !(arr.contains eb) then m := m.insert key (arr.push eb)
  return m

/-- 類推による候補と、その候補を支持する独立な根拠の数 -/
def analogy (K : KB A B) (E : EditTable B) (x : A) : List (B × Nat) := Id.run do
  let mut votes : Std.HashMap String (B × Nat) := {}
  for (a3, b3) in K do
    if let some e := editOf a3 x then
      for eb in E.getD (editKey e) #[] do
        -- 「挿入 ↔ 挿入」のように形のそろった変形を重く数える
        let w := if (e.u == zero) == (eb.u == zero) then 2 else 1
        for y in applyEdit b3 eb do
          if consistent K x y then
            let key := fmt y
            let (_, c) := votes.getD key (y, 0)
            votes := votes.insert key (y, c + w)
  return (votes.toList.map (·.2)).mergeSort (fun p q => p.2 ≥ q.2)

/-! ## 像（基本列の各項の対応先） -/

inductive Source | table | succ | analogy
deriving BEq

def Source.tag : Source → String
  | .table => "表"
  | .succ => "後者"
  | .analogy => "類推"

/-- 確実な像（知識・0・後者）。`useAnalogy` なら、一意に最多票の類推も使う -/
partial def image (K : KB A B) (E : EditTable B) (useAnalogy : Bool) (x : A) :
    Option (B × Source) :=
  match lookA K x with
  | some y => some (y, .table)
  | none =>
    if x == zero then some (zero, .table)
    else if isSucc x then
      (image K E useAnalogy (fund x 0)).map fun (y, s) => (succ y, if s == .analogy then .analogy else .succ)
    else if useAnalogy then
      match analogy K E x with
      | (y, v) :: rest =>
        if v ≥ 3 && rest.all (·.2 < v) then some (y, .analogy) else none
      | [] => none
    else none

/-! ## FS 逆算：極限の候補 -/

def prefixes (p : List Nat) : List (List Nat) := (List.range (p.length + 1)).map p.take

def atoms : List B := [zero, atom 0, atom 1, atom 2, atom 3]

/-- 同じ位置から取り出した増加列 `us` の極限の候補 -/
def localCands (us : List B) : List B := Id.run do
  let mut out : List B := atoms
  if let some ul := us.getLast? then
    let s := summands ul
    -- 和の途中で打ち切って、原子・直前の単項の複製・直前の単項 × ω を置く
    for j in [0:s.length + 1] do
      let pre := s.take j
      for e in atoms do
        out := out ++ [ofSummands (pre ++ [e])]
      if let some w := pre.getLast? then
        out := out ++ [ofSummands (pre ++ [w])]
        if let some w' := omegaMul w then
          out := out ++ [ofSummands (pre.dropLast ++ [w']), ofSummands (pre ++ [w'])]
  -- 反復 u_{i+1} = S[u_i] の極限 S^j[原子]
  for (u, v) in us.zip us.tail do
    for r in occ v u do
      if r ≠ [] then
        let S := fun x => set v r x
        for e in atoms do
          out := out ++ [S e, S (S e), S (S (S e))]
  return out

def fsCands (ys : List B) : List B := Id.run do
  let some yl := ys.getLast? | return []
  let mut ps : List (List Nat) := []
  for (u, v) in ys.zip ys.tail do
    if let some p := diffpos u v then ps := ps ++ [p]
  let mut out : List B := []
  for p in ps.eraseDups do
    for q in prefixes p do
      let us := ys.filterMap (get? · q)
      for c in localCands us do
        out := out ++ [set yl q c]
  return out

def offsetsToTry : List Int := [-2, -1, 0, 1, 2, 3]

/-- 厳密同期：既知の像 `(n, y)`（n ≥ 1）すべてで `c[n+k] = y` -/
def exactK (c : B) (xs : List (Nat × B)) : Option Int :=
  let xs1 := xs.filter (·.1 ≥ 1)
  offsetsToTry.find? fun k =>
    xs1.all fun (n, y) => (n : Int) + k ≥ 0 && fund c ((n : Int) + k).toNat == y

/-- 交互性：`c[n+k] ≤ y_n < c[n+k+1]`（n ≥ 1）、かつ `y_0 < c` -/
def alternK (c : B) (xs : List (Nat × B)) : Option Int :=
  offsetsToTry.find? fun k =>
    xs.all fun (n, y) =>
      if n == 0 then ltB y c else
      (n : Int) + k ≥ 0 &&
      leB (fund c ((n : Int) + k).toNat) y && ltB y (fund c ((n : Int) + k + 1).toNat)

inductive Verdict | exact (k : Int) | altern (k : Int) | none

def Verdict.rank : Verdict → Nat
  | .exact _ => 0
  | .altern _ => 1
  | .none => 2

def Verdict.show : Verdict → String
  | .exact k => s!"FS厳密同期(k={k})"
  | .altern k => s!"FS交互(k={k})"
  | .none => "FS未確認"

/-- 像が十分あるときだけ判定する -/
def fsVerdict (c : B) (xs : List (Nat × B)) : Verdict :=
  let n1 := (xs.filter (·.1 ≥ 1)).length
  if n1 ≥ 2 then
    match exactK c xs with
    | some k => .exact k
    | none =>
      if xs.length ≥ 3 then
        match alternK c xs with
        | some k => .altern k
        | none => .none
      else .none
  else .none

/-- `c` より大きい既知の標準項（`ups` と基底項）のうち最小のものから降下して、
    `c` が標準か判定する -/
def reachVia {T : Type} [OTSys T] (ups : List T) (c : T) : Reach T :=
  let bases := (List.range 8).map fun n => base (n + 1)
  match minT ((ups ++ bases).filter (ltB c ·)) with
  | some u => reach u c
  | none => .gaveUp

def standardVia {T : Type} [OTSys T] (ups : List T) (c : T) : Option Bool :=
  (reachVia ups c).ok

def stdTag : Option Bool → String
  | some true => "標準"
  | some false => "非標準"
  | none => "標準性未確認"

structure Cand (B : Type) where
  y : B
  verdict : Verdict
  votes : Nat
  fromFS : Bool
  std : Option Bool
  /-- FS 判定に、類推で補った像を使ったか -/
  guessed : Bool := false

structure Suggestion (A B : Type) where
  images : List (Nat × A × Option (B × Source))
  cands : List (Cand B)

def Cand.score (c : Cand B) : Nat := 2 * c.verdict.rank + (if c.guessed then 1 else 0)
def Cand.stdRank (c : Cand B) : Nat := if c.std == some true then 0 else 1

def Cand.better (c d : Cand B) : Bool :=
  if c.score != d.score then c.score < d.score
  else if c.stdRank != d.stdRank then c.stdRank < d.stdRank
  else if c.votes != d.votes then c.votes > d.votes
  else ltB c.y d.y

/-- FS 同期の原理で像の列を補う：`a[n-1] → a[n]` と `a[n] → a[n+1]` が同じ変形なら、
    B 側でも `y[n-1] → y[n]` と同じ変形で `y[n+1]` を作る。 -/
def propagate (fa : Array A) (ys : Array (Option B)) : Array (Option B) := Id.run do
  let mut ys := ys
  for n in [1:fa.size - 1] do
    if ys[n+1]!.isNone then
      match ys[n-1]!, ys[n]!, editOf fa[n-1]! fa[n]!, editOf fa[n]! fa[n+1]! with
      | some y0, some y1, some e0, some e1 =>
        if editKey e0 == editKey e1 then
          if let some eb := editOf y0 y1 then
            if let [y2] := applyEdit y1 eb then ys := ys.set! (n+1) (some y2)
      | _, _, _, _ => pure ()
  return ys

/-- `x` の対応先の候補を、根拠つきで良い順に並べる（非標準と判定された候補は除く） -/
def suggest (K : KB A B) (E : EditTable B) (N : Nat) (x : A) : Suggestion A B := Id.run do
  let images := (List.range N).map fun n => let xn := fund x n; (n, xn, image K E true xn)
  let fa := (images.map (·.2.1)).toArray
  let base : Array (Option B) := (images.map fun (_, _, im) => im.map (·.1)).toArray
  let toXs (ys : Array (Option B)) : List (Nat × B) :=
    (indexed ys.toList).filterMap fun (y, n) => y.map (n, ·)
  let xs := toXs base
  -- 最初に欠けている像を類推の上位候補で補った分岐（FS 同期で先へ伝播させる）
  let firstMissing := (List.range' 1 (N - 1)).find? fun n => base[n]!.isNone
  let guesses : List (Array (Option B)) := match firstMissing with
    | none => []
    | some n => ((analogy K E fa[n]!).take 3).map fun (y, _) => base.set! n (some y)
  let branches := (base :: guesses).map (propagate fa)
  let mut cands : Array (Cand B) := #[]
  for (y, v) in analogy K E x do
    cands := cands.push ⟨y, fsVerdict y xs, v, false, none, false⟩
  for ys in branches do
    let bx := toXs ys
    let lows := bx.map (·.2)
    if (bx.filter (·.1 ≥ 1)).length ≥ 2 then
      for c in (fsCands lows).filter (fun c => lows.all (ltB · c) && consistent K x c) do
        -- 確実な像だけで判定し、だめなら補った像での厳密同期だけを採用する
        let v0 := fsVerdict c xs
        let v1 := fsVerdict c bx
        let (vd, g) := if v0.rank < 2 then (v0, false) else (v1, true)
        if vd.rank == 0 || (vd.rank == 1 && !g) then
          match cands.findIdx? (·.y == c) with
          | some i =>
            cands := cands.modify i fun d =>
              let nd := { d with fromFS := true }
              if 2 * vd.rank + (if g then 1 else 0) < d.score then { nd with verdict := vd, guessed := g } else nd
          | none => cands := cands.push ⟨c, vd, 0, true, none, g⟩
  let ups := (K.map (·.2)).toList
  let checked := (cands.map fun c => { c with std := standardVia ups c.y }).filter (·.std != some false)
  let sorted := checked.toList.mergeSort (fun c d => c.better d || !(d.better c))
  return ⟨images, sorted⟩

/-- 予想の判定などで使う：最良候補 -/
def Suggestion.best (s : Suggestion A B) : Option (Cand B) := s.cands.head?

end TA
