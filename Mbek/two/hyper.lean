import Mbek.two.Base

/-!
# 弱 hyper-Mahlo 基数の崩壊まで

`mbek.lean` の `fund1`〜`fund5` を一つの `fundM kd` にまとめたもの。
`kd = .fin (MDeg.ofNat d)`（`d` は有限）で `fund (d+1)` と一致し、`fundH := fundM .hyper`。

## 用語

`l : Nat` について `K_{l+1} := P (l+1) Z Z` と書く。

* **鎖・段・次数**：`domM kd x = .C l ch`、`ch = [(l₁,d₁), …, (l_j,d_j)]` のとき、`ch` を `x` の鎖と呼ぶ。
  `π₀ := K_{l+1}`、`πᵢ := P l lᵢ Z`（`i = 1..j`）を鎖の段と呼び、`dᵢ` を `πᵢ` の次数、`kd` を `π₀` の次数と呼ぶ。
* **共終先**：上のとき `π_j`（`ch = []` なら `π₀ = K_{l+1}`）を `x` の共終先と呼ぶ。
* **分類**：共終先が `π_j` の `s1` に対し、`stepM kd s0 s1 l ch` は `P s0 s1 Z` を
  `push d`（鎖に段 `(s1, d)` を足す）、`keep`（共終先は `π_j` のまま）、`omega`（`domM` が `.ω`）のいずれかに分類する。
* **窓の下端**：`bᵢ := P l (takeAt lᵢ πᵢ₋₁) Z`（`i = 1..j`）。
* **冪の形**：項 `π = P s lp Z` と非増加の項の列 `e₀ ≥ e₁ ≥ ⋯` について、`π^(1) := π`、
  `π^(ν+1) := P s (lp + P s (lp + e₀) Z + P s (lp + e₁) Z + ⋯ + π) Z`（`ν := 1 + ω^e₀ + ω^e₁ + ⋯`）と書く。
  `π₀` については `s = l+1`, `lp = Z`、`πᵢ` については `s = l`, `lp = lᵢ`。

## 分類の規則（`stepM`）

共終先が `π_j` の `s1` について、

* `j = 0`（共終先が `K_{l+1}`）：`s0 < l` なら `omega`、`s0 > l` なら `keep`、`s0 = l` なら `newDeg` が次数 `d` を
  返せば `push d`、返さなければ `omega`。
* `j ≥ 1`：`P s0 s1 Z ≥ π_j` なら `keep`。`P s0 s1 Z < π_j` で `s0 < l` なら `omega`。
  `s0 = l` なら、`P l s1 Z < bᵢ` となる `i` があれば `omega`、なければ `newDeg` が次数 `d` を返せば `push d`、
  返さなければ `omega`。

`newDeg` が返す次数は、`s1` の末尾の単項（`lastMono s1`）と `π_j` の次数 `δ` で決まる。

* `δ = .hyper`（`π₀` のみ）：末尾の単項が `π₀` なら `0`、`π₀^(ν+1)` で全ての `eᵢ < K_{l+1}` なら `ν`、それ以外は返さない。
* `δ` が後者（`MDeg.pred? δ = some μ`）：末尾の単項によらず `μ`。
* `δ` が極限（`δ = pos es` で `MDeg.pred? δ = none`）：末尾の単項が `π_j` なら `0`、`π_j^(ν+1)` で `ν < δ` なら `ν`、
  それ以外は返さない。
* `δ = zero`：返さない。

`fund2`〜`fund5` の `M l`, `Ω l l1`, `M1 l l1 l2`, … は鎖を長さごとに別の構成子にしたもので、
そこでは `π₀` の次数が有限の後者なので、段の次数は常に一つずつ下がる。

## 意図する解釈

`push d` で作られる `P l s1 Z` は弱 `d`-Mahlo 基数（`d = 0` なら正則基数）、`K_{l+1}` は `l+1` 番目の弱 hyper-Mahlo 基数
（`kd = .fin d` なら弱 `d`-Mahlo 基数）を表す。`MDeg` の `pos es` は順序数 `1 + ω^es[0] + ω^es[1] + ⋯` を表す。
-/

open T

/-- 次数。`pos es` は順序数 `1 + ω^es[0] + ω^es[1] + ⋯`（`es` は非増加）を表す。 -/
inductive MDeg where
  | zero
  | pos (es : List T)
  deriving DecidableEq, Repr

/-- 鎖の段 `π₀ = K_{l+1} = P (l+1) Z Z` の次数（全ての `l` で共通） -/
inductive KDeg where
  /-- 次数 `d`（解釈：弱 `d`-Mahlo） -/
  | fin (d : MDeg)
  /-- `K_{l+1}` 未満の次数を全て許す（解釈：弱 hyper-Mahlo） -/
  | hyper
  deriving DecidableEq, Repr

/-- 有限の次数 `n` -/
def MDeg.ofNat : Nat → MDeg
  | 0 => .zero
  | n + 1 => .pos (List.replicate n Z)

/-- Cantor 標準形 `ω^a₀ + ω^a₁ + ⋯` どうしの比較（指数の列の辞書式比較） -/
def T.cnfLt : List T → List T → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then T.cnfLt as bs else false

def MDeg.lt : MDeg → MDeg → Bool
  | .zero, .zero => false
  | .zero, .pos _ => true
  | .pos _, .zero => false
  | .pos a, .pos b => T.cnfLt a b

/-- `δ` が後者（`δ = μ + 1`）なら `μ`、そうでなければ `none` -/
def MDeg.pred? : MDeg → Option MDeg
  | .zero => none
  | .pos es =>
    match es.getLast? with
    | none => some .zero
    | some e => if e = Z then some (.pos es.dropLast) else none

/-- 和を単項の列に分解する -/
def T.summandList : T → List T
  | Z => []
  | P a b c => P a b Z :: T.summandList c

/-- 末尾の単項（`y = y' + m`、`m` は単項、のときの `m`） -/
def T.lastMono : T → T
  | Z => Z
  | P a b c => if c = Z then P a b Z else T.lastMono c

/-- `x = p + r` なら `r` -/
def T.stripPrefix : T → T → Option T
  | Z, x => some x
  | P _ _ _, Z => none
  | P a b c, P a' b' c' => if a = a' ∧ b = b' then T.stripPrefix c c' else none

/-- `π = P s lp Z` について、`y` の末尾の単項から読む次数。
  * 末尾の単項が `π` → `0`
  * 末尾の単項が `π^(ν+1) = P s (lp + P s (lp + e₀) Z + P s (lp + e₁) Z + ⋯ + π) Z` → `pos [e₀, e₁, …]`（= `ν`）
  * それ以外 → `none` -/
def T.shapeDeg (s : Nat) (lp y : T) : Option MDeg :=
  match T.lastMono y with
  | Z => none
  | P a b _ =>
    if a ≠ s then none
    else if b = lp then some .zero
    else
      match T.stripPrefix lp b with
      | none => none
      | some r =>
        let ms := T.summandList r
        if ms.getLast? = some (P s lp Z) then
          let es := ms.dropLast.map fun m =>
            match m with
            | P a' b' _ => if a' = s then T.stripPrefix lp b' else none
            | Z => none
          if es.all Option.isSome then some (.pos (es.filterMap id)) else none
        else none

/-- 共終先 `π = P s lp Z` の次数が `δ` のとき、`stepM` が `push` で鎖に足す段 `(y, d)` の次数 `d`
    （`push` しないなら `none`）。`K` は `K_{l+1} = P (l+1) Z Z`。 -/
def T.newDeg (δ : KDeg) (s : Nat) (lp y K : T) : Option MDeg :=
  match δ with
  | .hyper =>
    match T.shapeDeg s lp y with
    | some (.pos es) => if es.all (fun e => decide (e < K)) then some (.pos es) else none
    | d => d
  | .fin d =>
    match d.pred? with
    | some p => some p
    | none =>
      match d with
      | .zero => none
      | .pos _ =>
        match T.shapeDeg s lp y with
        | some e => if e.lt d then some e else none
        | none => none

/-- 鎖の段 `[π₀, π₁, …, π_j]`（`π₀ = K_{l+1}`, `πᵢ = P l lᵢ Z`） -/
def T.prevs (l : Nat) (ch : List (T × MDeg)) : List T :=
  P (l + 1) Z Z :: ch.map (fun p => P l p.1 Z)

/-- `P l s1 Z < bᵢ`（窓の下端 `bᵢ = P l (takeAt lᵢ πᵢ₋₁) Z`）となる最初の `i` から 1 を引いたもの -/
def T.windowIdx (l : Nat) (ch : List (T × MDeg)) (s1 : T) : Option Nat :=
  ((ch.map Prod.fst).zip (T.prevs l ch)).findIdx? fun (li, pv) =>
    decide (P l s1 Z < P l (T.takeAt li pv) Z)

/-- 鎖が `ch` の `s1` を引数にとる `P s0 s1 Z` の分類 -/
inductive StepM where
  /-- `domM` が `.ω` -/
  | omega
  /-- 共終先は `s1` と同じ -/
  | keep
  /-- 鎖に段 `(s1, d)` を足す -/
  | push (d : MDeg)

def T.stepM (kd : KDeg) (s0 : Nat) (s1 : T) (l : Nat) (ch : List (T × MDeg)) : StepM :=
  match ch.getLast? with
  | none =>
    if s0 < l then .omega
    else if s0 = l then
      match T.newDeg kd (l + 1) Z s1 (P (l + 1) Z Z) with
      | some d => .push d
      | none => .omega
    else .keep
  | some (lj, dj) =>
    if P s0 s1 Z < P l lj Z then
      if s0 < l then .omega
      else
        match T.windowIdx l ch s1 with
        | some _ => .omega
        | none =>
          match T.newDeg (.fin dj) l lj s1 (P (l + 1) Z Z) with
          | some d => .push d
          | none => .omega
    else .keep

inductive DomM where
  | Zero
  | One
  | ω
  | C (l : Nat) (ch : List (T × MDeg))
  deriving DecidableEq, Repr

def T.domM (kd : KDeg) : T → DomM
  | Z => .Zero
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.domM kd s1 with
      | .Zero =>
        match s0 with
        | 0 => .One
        | l + 1 => .C l []
      | .One => .ω
      | .ω => .ω
      | .C l ch =>
        match T.stepM kd s0 s1 l ch with
        | .omega => .ω
        | .keep => .C l ch
        | .push d => .C l (ch ++ [(s1, d)])
    else T.domM kd s2

theorem T.domM_C_size (kd : KDeg) :
    ∀ (x : T) (l : Nat) (ch : List (T × MDeg)), T.domM kd x = .C l ch →
      ∀ p ∈ ch, p.1.size < x.size := by
  intro x
  induction x with
  | Z => intro l ch h; simp [T.domM] at h
  | P s0 s1 s2 ih1 ih2 =>
    intro l ch h p hp
    have hl := T.size_lt_size_P_left s0 s1 s2
    unfold T.domM at h
    split at h
    · split at h
      · split at h
        · exact DomM.noConfusion h
        · injection h with _ hch
          subst hch
          simp at hp
      · exact DomM.noConfusion h
      · exact DomM.noConfusion h
      · rename_i l' ch' hdom
        split at h
        · exact DomM.noConfusion h
        · injection h with _ hch
          subst hch
          exact Nat.lt_trans (ih1 l' ch' hdom p hp) hl
        · injection h with _ hch
          subst hch
          rcases List.mem_append.mp hp with hp | hp
          · exact Nat.lt_trans (ih1 l' ch' hdom p hp) hl
          · simp at hp
            subst hp
            exact hl
    · exact Nat.lt_trans (ih2 l ch h p hp) (T.size_lt_size_P_right s0 s1 s2)

/-- `[G_a, …, G_j]` と `H` から `G_j ∘ ⋯ ∘ G_a ∘ H` を作る -/
def T.composeAll (Gs : List (T → T)) (H : T → T) : T → T :=
  Gs.foldl (fun acc G => G ∘ acc) H

/-- 分類が `omega` のとき、反復する関数 `F` を `G_j ∘ ⋯ ∘ G_{i+1} ∘ fund (drop πᵢ s1)` とする `i`
    （`none` なら `F = G_j ∘ ⋯ ∘ G_1 ∘ (x ↦ P l (s1[x]) Z)`、`G_k x = P l (l_k[x]) Z`） -/
def T.collapseFrom (l : Nat) (ch : List (T × MDeg)) (s0 : Nat) (s1 : T) : Option Nat :=
  if ch = [] ∨ s0 < l then none
  else some ((T.windowIdx l ch s1).getD (ch.length - 1))

def T.fundM (kd : KDeg) (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h : T.domM kd s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fundM kd s1 Z) Z) t
      | .ω => P s0 (T.fundM kd s1 t) Z
      | .C l ch =>
        match T.stepM kd s0 s1 l ch with
        | .keep => P s0 (T.fundM kd s1 t) Z
        | .push _ => t
        | .omega =>
          let Gs : List (T → T) :=
            ch.attach.map fun ⟨p, _hp⟩ => fun x => P l (T.fundM kd p.1 x) Z
          let F : T → T :=
            match T.collapseFrom l ch s0 s1 with
            | none => T.composeAll Gs (fun x => P l (T.fundM kd s1 x) Z)
            | some i =>
              T.composeAll (Gs.drop i) (T.fundM kd (T.drop ((T.prevs l ch).getD i Z) s1))
          P s0 (T.fundM kd s1 (T.iter F t)) Z
    else P s0 s1 (T.fundM kd s2 t)
termination_by s.size
decreasing_by
  all_goals
    first
    | exact T.size_lt_size_P_left s0 s1 s2
    | exact T.size_lt_size_P_right s0 s1 s2
    | exact Nat.lt_of_le_of_lt (T.drop_size_le _ s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.domM_C_size kd s1 l ch _h p ‹_›) (T.size_lt_size_P_left s0 s1 s2)

/-- `π₀` の次数を `.hyper` としたもの（解釈：弱 hyper-Mahlo 基数の崩壊まで） -/
def T.domH : T → DomM := T.domM .hyper

def T.fundH : T → T → T := T.fundM .hyper

inductive T.isOTH : T → Prop where
| base (n : Nat) : T.isOTH (P 0 (P 0 (P n Z Z) Z) Z)
| step (s : T) (h : T.isOTH s) (n : Nat) : T.isOTH (T.fundH s (T.ofNat n))

#eval! domH (parse! "0^1^(1^0+1)")

#eval! domH (parse! "0^(1^1^0 + 0^(1^(1^0+1) + 0^1^(1^0+1) + 0^1^(1^0+1)))")

#eval! fundH (parse! "0^1^1^1") (parse! "0 + 0 + 0")

#eval! fundH (parse! "0^0^1^(1+1)") (parse! "0 + 0 + 0")

#eval! fundH (parse! "0^0^1^(1^0+1)") (parse! "0 + 0 + 0")

#eval! fundH (parse! "0^(1^1^0 + 0^(1^(1^0+1) + 0^(1^(1^0+1) + 0) + 0^1^(1^0+1)))") (parse! "0 + 0")
