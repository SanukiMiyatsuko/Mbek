import Mbek.TableAnalysis.Analysis

/-!
# 表解析ツール: レポート
-/

namespace TA
open TreeLike OTSys

variable {A B : Type} [OTSys A] [OTSys B]

def rowTag (r : Row A B) : String :=
  if r.trusted then s!"r{r.line}" else s!"r{r.line}({r.note})"

/-- 1. 順序の検査。違反の数を返す -/
def checkOrder (rows : Array (Row A B)) : IO Nat := do
  IO.println "## 1. 順序の検査"
  let mut bad := 0
  for i in [0:rows.size - 1] do
    let r := rows[i]!
    let s := rows[i+1]!
    let okA := ltB r.a s.a
    let okB := ltB r.b s.b
    if !(okA && okB) then
      bad := bad + 1
      IO.println s!"- 単調性違反: {rowTag r} → {rowTag s}  (A増加={okA}, B増加={okB})"
  let mut pv := 0
  for i in [0:rows.size] do
    for j in [i+1:rows.size] do
      let r := rows[i]!
      let s := rows[j]!
      if ltB r.a s.a != ltB r.b s.b || (r.a == s.a) != (r.b == s.b) then
        pv := pv + 1
        if pv ≤ 20 then IO.println s!"- 順序同型違反: {rowTag r} と {rowTag s}"
  IO.println s!"- 隣接行の単調性違反: {bad} 件 / 全対比較の違反: {pv} 件（{rows.size} 行）"
  return bad + pv

/-- 着地した行どうしが交互に並ぶか（種 n = 0 を除き、a 側の像と b 側の基本列が互いに相手の隙間に入る） -/
def interleaved (rows : Array (Row A B)) (s : Sync) : Bool :=
  let xs := s.hitsA.filterMap fun (n, i) => if n == 0 then none else rows[i]?.map (·.b)
  let ys := s.hitsB.filterMap fun (m, j) => if m == 0 then none else rows[j]?.map (·.b)
  xs.length ≥ 2 && ys.length ≥ 2 &&
  (xs.zip xs.tail).all (fun (u, v) => ys.any fun y => leB u y && leB y v) &&
  (ys.zip ys.tail).all (fun (u, v) => xs.any fun x => leB u x && leB x v)

def showHits (rows : Array (Row A B)) (h : List (Nat × Nat)) : String :=
  ", ".intercalate (h.map fun (n, i) => s!"[{n}]→{(rows[i]?.map rowTag).getD s!"#{i}"}")

def showReach {T : Type} [OTSys T] : Reach T → String
  | .reached => "標準"
  | .skipped => "非標準（前者をとると下回る）"
  | .stuck u => s!"到達できず：{fmt u} の基本列がこの項を飛び越える"
  | .gaveUp => "打ち切り"

/-- 1b. 標準性：各項が、標準と確認済みのより大きい項（または基底項）から
    基本列をたどって到達できるか。大きい行から順に確かめる。 -/
def checkStandard (rows : Array (Row A B)) : IO Unit := do
  IO.println "\n## 1b. 標準性（isOT の基底・確認済みの大きい行から基本列で到達できるか）"
  let mut okA : List A := []
  let mut okB : List B := []
  let mut bad := 0
  for r in rows.reverse do
    let ra := reachVia okA r.a
    let rb := reachVia okB r.b
    if ra.ok == some true then okA := r.a :: okA
    if rb.ok == some true then okB := r.b :: okB
    if ra.ok != some true || rb.ok != some true then
      bad := bad + 1
      IO.println s!"- {rowTag r}: A={showReach ra} / B={showReach rb}"
  IO.println s!"- 標準と確認できなかった行: {bad} 件（{rows.size} 行中）"

/-- 2. 基本列の同期 -/
def checkSync (rows : Array (Row A B)) (N : Nat) : IO Unit := do
  IO.println s!"\n## 2. 基本列の同期（n = 0..{N-1}）"
  IO.println "各行の基本列 a[n], b[m] が表のどの行に着地するかと、そこから読めるオフセット k（b[n+k] ↔ a[n]）。"
  let K : KB A B := rows.map fun r => (r.a, r.b)
  let mut ks : List Int := []
  let mut cats : List String := []
  for r in rows do
    let s := syncOf K N r.a r.b
    let (cat, verdict) := match s.offsets with
      | [k] =>
        let hA0 : Option (Nat × Nat) := s.hitsA.find? fun (p : Nat × Nat) => p.1 == 0
        let hBk : Option (Nat × Nat) :=
          if k ≥ 0 then s.hitsB.find? fun (p : Nat × Nat) => p.1 == k.toNat else none
        let seed := match hA0, hBk with
          | some (_, i), some (_, j) => if i == j then "" else "（種 n=0 のみずれ）"
          | _, _ => ""
        ("同期", s!"同期 k={k}{seed}")
      | [] =>
        if interleaved rows s then ("交互", "交互（b[m] < a[n] の像 < b[m+1] 型）")
        else if s.hitsA.isEmpty || s.hitsB.isEmpty then ("データ不足", "着地データ不足")
        else ("未確定", "オフセット未確定")
      | os => ("要確認", s!"要確認：複数のオフセット {os}")
    if let [k] := s.offsets then ks := ks ++ [k]
    cats := cats ++ [cat]
    IO.println s!"- {rowTag r}: A[{showHits rows s.hitsA}] B[{showHits rows s.hitsB}] → {verdict}"
  let dist := (ks.eraseDups.mergeSort).map fun k => s!"k={k}: {(ks.filter (· == k)).length}"
  let count (c : String) := (cats.filter (· == c)).length
  IO.println s!"- 集計: 同期 {count "同期"} 行（{", ".intercalate dist}）/ 交互 {count "交互"} / 未確定 {count "未確定"} / 着地データ不足 {count "データ不足"} / 要確認 {count "要確認"}"

/-- 3. FS 閉包 -/
def checkClosure (rows : Array (Row A B)) (N : Nat) (printDerived : Bool) : IO (KB A B) := do
  IO.println "\n## 3. FS 閉包（派生対応の生成と整合性）"
  let src : KB A B := (rows.filter (·.trusted)).map fun r => (r.a, r.b)
  let (K, conflicts) := closure src N
  IO.println s!"- 確定行 {src.size} 件から、種を除いた (a[n], b[n+k]) を {K.size - src.size} 件派生"
  IO.println s!"- 表・派生対応と矛盾した派生: {conflicts.size} 件"
  for (a, b, x, y) in conflicts.toList.take 20 do
    IO.println s!"  - 親 {fmt a} ↔ {fmt b} からの派生 {fmt x} ↔ {fmt y} が既知の対応と矛盾"
  if printDerived then
    IO.println "\n派生対応（CSV）:"
    for (x, y) in K.toList.drop src.size do
      IO.println s!"\"{fmt x}\",\"{fmt y}\",派生"
  return K

def showCand (c : Cand B) : String :=
  let src := (if c.votes > 0 then [s!"類推{c.votes}票"] else []) ++ (if c.fromFS then ["FS逆算"] else [])
  s!"{fmt c.y}  [{c.verdict.show}; {", ".intercalate src}]"

def printSuggestion (s : Suggestion A B) (limit : Nat := 5) : IO Unit := do
  for (n, xn, im) in s.images do
    let rhs := match im with
      | some (y, src) => s!"{fmt y}（{src.tag}）"
      | none => "?"
    IO.println s!"    a[{n}] = {fmt xn}  ↦  {rhs}"
  if s.cands.isEmpty then IO.println "    候補なし"
  for (c, i) in indexed (s.cands.take limit) do
    IO.println s!"    候補{i+1}: {showCand c}"

/-- 4. 予想の検証 -/
def checkConjectures (rows : Array (Row A B)) (K : KB A B) (N : Nat) : IO Unit := do
  let conj := rows.filter (!·.trusted)
  if conj.isEmpty then return
  IO.println "\n## 4. 予想の検証"
  let E := buildEdits K
  for r in conj do
    let ord := consistent K r.a r.b
    let xs := (List.range N).filterMap fun n => (image K E true (fund r.a n)).map fun (y, _) => (n, y)
    let vd := fsVerdict r.b xs
    let sg := suggest K E N r.a
    let agree := match sg.best with
      | some c => if c.y == r.b then "ツールの第1候補と一致" else s!"ツールの第1候補は {fmt c.y}"
      | none => "ツールは候補を出せず"
    let ups := (K.map (·.2)).toList
    IO.println s!"- {rowTag r}: {fmt r.a} ↔ {fmt r.b}"
    IO.println s!"    順序整合={ord}, B側は{stdTag (standardVia ups r.b)}, {vd.show}, {agree}"
    let K' := K ++ conj.map fun c => (c.a, c.b)
    match (syncOf K' N r.a r.b).offsets with
    | [k] =>
      IO.println s!"    同期 k={k} とすると、予想から次の対応が導かれる（次に確かめる行の候補）:"
      for n in [1:4] do
        let m : Int := n + k
        if m ≥ 0 then
          let x := fund r.a n
          let y := fund r.b m.toNat
          let st := match lookA K' x with
            | some y' => if y' == y then "既知と一致" else s!"既知 {fmt y'} と食い違う"
            | none => if consistent K x y then "表と整合" else "表と矛盾"
          IO.println s!"      {fmt x} ↔ {fmt y}  （{st}）"
    | _ => pure ()

/-- 5. leave-one-out：各確定行を隠し、残りから復元できるか -/
def leaveOneOut (rows : Array (Row A B)) (N : Nat) : IO Unit := do
  IO.println "\n## 5. leave-one-out（各行を隠して残りから復元）"
  let tr := rows.filter (·.trusted)
  let mut ok := 0
  let mut wrong := 0
  let mut none_ := 0
  for i in [0:tr.size] do
    let r := tr[i]!
    let src : KB A B := ((tr.toList.eraseIdx i).map fun s => (s.a, s.b)).toArray
    let (K0, _) := closure src N
    let K := K0.filter fun (a, b) => !(a == r.a) && !(b == r.b)
    let E := buildEdits K
    let sg := suggest K E N r.a
    match sg.best with
    | some c =>
      if c.y == r.b then
        ok := ok + 1
        IO.println s!"- {rowTag r}: 復元成功 [{c.verdict.show}; 類推{c.votes}票{if c.fromFS then ", FS逆算" else ""}]"
      else
        wrong := wrong + 1
        IO.println s!"- {rowTag r}: 不一致  推定 {showCand c}\n    正解 {fmt r.b}"
    | none =>
      none_ := none_ + 1
      IO.println s!"- {rowTag r}: 候補なし"
  IO.println s!"- 集計: 成功 {ok} / 不一致 {wrong} / 候補なし {none_}（{tr.size} 行）"

end TA
