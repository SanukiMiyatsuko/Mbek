/-!
# 表解析ツール: 共通部

二つの OT（順序数表記系）を同じ手続きで扱うための最小限のインターフェースと、
項を木として扱う汎用操作（部分項の取得・置換・差分位置・出現位置）を定める。
-/

/-- 項を「ラベル付きの木」として見るためのビュー。
    `kids` の最後の子を「後続の和（tail）」とみなす。 -/
class TreeLike (T : Type) where
  zero : T
  label : T → Option Nat
  kids : T → List T
  node : Nat → List T → T

/-- 表解析に必要な OT の操作一式。 -/
class OTSys (T : Type) extends BEq T, TreeLike T where
  /-- 体系の順序 `<` -/
  lt : T → T → Bool
  /-- 基本列 `s[n]` -/
  fund : T → Nat → T
  /-- 後者型（`dom = 1`）か -/
  isSucc : T → Bool
  /-- `s + 1` -/
  succ : T → T
  /-- ラベル `l` の原子項（引数がすべて 0 の単項） -/
  atom : Nat → T
  /-- 単項 `w` に対し `w·ω` を表す単項 -/
  omegaMul : T → Option T
  /-- `isOT` の基底項（パラメータ `n`） -/
  base : Nat → T
  parse? : String → Option T
  fmt : T → String

namespace TA
open TreeLike OTSys

variable {T : Type} [OTSys T]

scoped instance (priority := low) {T : Type} [TreeLike T] : Inhabited T := ⟨zero⟩

def modifyAt {α} : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, n + 1, f => x :: modifyAt xs n f

def indexed {α} (l : List α) : List (α × Nat) := l.zip (List.range l.length)

/-- 位置 `p`（子の番号の列）にある部分項 -/
def get? (t : T) : List Nat → Option T
  | [] => some t
  | i :: p => match label t with
    | none => none
    | some _ => match (kids t)[i]? with
      | some c => get? c p
      | none => none

/-- 位置 `p` の部分項を `u` に置き換える -/
def set (t : T) : List Nat → T → T
  | [], u => u
  | i :: p, u => match label t with
    | none => t
    | some n => node n (modifyAt (kids t) i (fun c => set c p u))

/-- `x` と `y` が異なる最も深い単一の位置（同じなら `none`） -/
partial def diffpos (x y : T) : Option (List Nat) :=
  if x == y then none else
  match label x, label y with
  | some n, some m =>
    if n == m then
      match (indexed ((kids x).zip (kids y))).filter (fun ((a, b), _) => !(a == b)) with
      | [((a, b), i)] => (diffpos a b).map (i :: ·)
      | _ => some []
    else some []
  | _, _ => some []

/-- `u` が `t` の部分項として現れる位置の一覧 -/
partial def occ (t u : T) : List (List Nat) :=
  (if t == u then [[]] else []) ++
  (indexed (kids t)).flatMap fun (c, i) => (occ c u).map (i :: ·)

/-- 和の分解（最後の子を tail とみなす） -/
partial def summands (t : T) : List T :=
  match label t with
  | none => []
  | some n =>
    let ks := kids t
    node n (ks.dropLast ++ [zero]) :: summands (ks.getLastD zero)

def ofSummands : List T → T
  | [] => zero
  | s :: rest => match label s with
    | none => ofSummands rest
    | some n => node n ((kids s).dropLast ++ [ofSummands rest])

def ltB (a b : T) : Bool := OTSys.lt a b
def leB (a b : T) : Bool := a == b || OTSys.lt a b

def minT (cs : List T) : Option T :=
  cs.foldl (fun acc c => match acc with
    | none => some c
    | some d => if ltB c d then some c else some d) none

/-- 降下の結果 -/
inductive Reach (T : Type) where
  /-- 到達した（`c` は標準） -/
  | reached
  /-- 前者をとると `c` を下回った（`c` は非標準） -/
  | skipped
  /-- `c < u` なのに `u[n] < c`（n < maxN）：`u` の基本列が `c` を飛び越える -/
  | stuck (u : T)
  /-- 打ち切り -/
  | gaveUp

/-- 標準項 `u` から基本列（自然数添字）と前者だけをたどって `c` に到達できるか。
    極限では `u[n] ≥ c` となる最小の `n` を選ぶ（貪欲降下）。 -/
def reach (u c : T) (maxN : Nat := 64) (fuel : Nat := 20000) : Reach T := Id.run do
  let mut u := u
  for _ in [0:fuel] do
    if u == c then return .reached
    if ltB u c || u == zero then return .skipped
    if isSucc u then
      u := fund u 0
    else
      match (List.range maxN).find? (fun n => leB c (fund u n)) with
      | some n => u := fund u n
      | none => return .stuck u
  return .gaveUp

def Reach.ok : Reach T → Option Bool
  | .reached => some true
  | .skipped => some false
  | _ => none

/-- 位置の直上の情報：親のラベル・子番号・（tail 位置なら）直前の単項 -/
structure Anchor (T : Type) where
  lbl : Option Nat
  idx : Nat
  head : Option T

instance [BEq T] : BEq (Anchor T) where
  beq a b := a.lbl == b.lbl && a.idx == b.idx && a.head == b.head

def anchor (t : T) (p : List Nat) : Anchor T :=
  match p.getLast? with
  | none => ⟨none, 0, none⟩
  | some i =>
    match get? t p.dropLast with
    | none => ⟨none, i, none⟩
    | some par =>
      let ks := kids par
      let isTail := i + 1 == ks.length
      ⟨label par, i,
        if isTail then (label par).map (fun n => node n (ks.dropLast ++ [zero])) else none⟩

/-- 局所的な書き換え `u ↦ v`（位置の直上の情報つき） -/
structure Edit (T : Type) where
  anc : Anchor T
  u : T
  v : T

instance [BEq T] : BEq (Edit T) where
  beq a b := a.anc == b.anc && a.u == b.u && a.v == b.v

/-- `x` から `y` への単一位置の書き換え -/
def editOf (x y : T) : Option (Edit T) := do
  let p ← diffpos x y
  let u ← get? x p
  let v ← get? y p
  pure ⟨anchor x p, u, v⟩

/-- 書き換えを `t` の当てはまるすべての位置に（一箇所ずつ）施した結果 -/
def applyEdit (t : T) (e : Edit T) : List T :=
  (occ t e.u).filterMap fun q => if anchor t q == e.anc then some (set t q e.v) else none

def editKey (e : Edit T) : String :=
  let a := e.anc
  s!"{a.lbl}|{a.idx}|{(a.head.map fmt).getD "-"}|{fmt e.u}|{fmt e.v}"

end TA
