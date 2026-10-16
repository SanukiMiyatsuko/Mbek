import Mbek.TableAnalysis.Core
import Mbek.two.mbek
import Mbek.three.rasen

/-!
# 表解析ツール: 体系の登録

* `MRF.T` : rasen の MRF（`p(s0,s1,s2)+s3`、表では `w` = ω）
* `MbekT M` : Mbek の項を `fund M`（M = 0..5）で読むもの
-/

/-! ## MRF -/

instance : TreeLike MRF.T where
  zero := .Z
  label | .Z => none | .P n .. => some n
  kids | .Z => [] | .P _ a b c => [a, b, c]
  node n ks := match ks with
    | [a, b, c] => .P n a b c
    | _ => .Z

def MRF.summandsM : MRF.T → List MRF.T
  | .Z => []
  | .P a b c d => .P a b c .Z :: MRF.summandsM d

/-- 表で使われている書式（`1`, `w`, `p(a,b,c)+…`） -/
partial def MRF.fmtSheet (t : MRF.T) : String :=
  match t with
  | .Z => "0"
  | _ => "+".intercalate ((MRF.summandsM t).map fun
      | .P 0 .Z .Z .Z => "1"
      | .P 0 .Z (.P 0 .Z .Z .Z) .Z => "w"
      | .P a b c _ => s!"p({a},{MRF.fmtSheet b},{MRF.fmtSheet c})"
      | .Z => "0")

/-- 和を一般に読む MRF のパーサ（`1+1`, `w+1`, `p(…)+1+1` なども読める）。
    項 := 単項 (`+` 単項)*、単項 := `0` | `1` | `w` | `ω` | `p(自然数,項,項)` -/
partial def MRF.parseTerm (cs : List Char) : Option (MRF.T × List Char) := do
  let (ms, rest) ← summands cs []
  pure (ms.foldr (fun m acc => match m with
    | .P a b c _ => .P a b c acc
    | .Z => acc) .Z, rest)
where
  summands (cs : List Char) (acc : List MRF.T) : Option (List MRF.T × List Char) := do
    let (m, rest) ← monomial cs
    match rest with
    | '+' :: rest' => summands rest' (acc ++ [m])
    | _ => pure (acc ++ [m], rest)
  monomial : List Char → Option (MRF.T × List Char)
    | '0' :: rest => some (.Z, rest)
    | '1' :: rest => some (.P 0 .Z .Z .Z, rest)
    | 'w' :: rest => some (.P 0 .Z (.P 0 .Z .Z .Z) .Z, rest)
    | 'ω' :: rest => some (.P 0 .Z (.P 0 .Z .Z .Z) .Z, rest)
    | 'p' :: '(' :: rest => do
      let ds := rest.takeWhile Char.isDigit
      if ds.isEmpty then none
      let n := ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
      let rest := rest.drop ds.length
      let rest ← match rest with | ',' :: r => some r | _ => none
      let (b, rest) ← MRF.parseTerm rest
      let rest ← match rest with | ',' :: r => some r | _ => none
      let (c, rest) ← MRF.parseTerm rest
      let rest ← match rest with | ')' :: r => some r | _ => none
      pure (.P n b c .Z, rest)
    | _ => none

def MRF.parseSheet (s : String) : Option MRF.T :=
  match MRF.parseTerm (s.toList.filter (!·.isWhitespace)) with
  | some (t, []) => some t
  | _ => none

instance : OTSys MRF.T where
  beq := (· == ·)
  lt a b := decide (a < b)
  fund s n := MRF.T.fund s (MRF.T.ofNat n)
  isSucc s := MRF.T.dom s == .one
  succ s := MRF.T.add s (.P 0 .Z .Z .Z)
  atom l := .P l .Z .Z .Z
  omegaMul
    | .P a b c .Z => some (.P a b (MRF.T.add c (.P 0 .Z .Z .Z)) .Z)
    | _ => none
  base n := .P 0 .Z (.P n .Z .Z .Z) .Z
  parse? := MRF.parseSheet
  fmt := MRF.fmtSheet

/-! ## Mbek -/

/-- Mbek の項を `fund M` で読むためのラッパー -/
structure MbekT (M : Nat) where
  t : T

def mbekFund : Nat → T → T → T
  | 0 => T.fund0
  | 1 => T.fund1
  | 2 => T.fund2
  | 3 => T.fund3
  | 4 => T.fund4
  | _ => T.fund5

def mbekIsSucc : Nat → T → Bool
  | 0, s => T.dom0 s == .One
  | 1, s => T.dom1 s == .One
  | 2, s => T.dom2 s == .One
  | 3, s => T.dom3 s == .One
  | 4, s => T.dom4 s == .One
  | _, s => T.dom5 s == .One

instance (M : Nat) : TreeLike (MbekT M) where
  zero := ⟨.Z⟩
  label | ⟨.Z⟩ => none | ⟨.P n _ _⟩ => some n
  kids | ⟨.Z⟩ => [] | ⟨.P _ a b⟩ => [⟨a⟩, ⟨b⟩]
  node n ks := match ks with
    | [a, b] => ⟨.P n a.t b.t⟩
    | _ => ⟨.Z⟩

instance (M : Nat) : OTSys (MbekT M) where
  beq a b := a.t == b.t
  lt a b := decide (a.t < b.t)
  fund s n := ⟨mbekFund M s.t (T.ofNat n)⟩
  isSucc s := mbekIsSucc M s.t
  succ s := ⟨T.add s.t (.P 0 .Z .Z)⟩
  atom l := ⟨.P l .Z .Z⟩
  omegaMul
    | ⟨.P n a .Z⟩ => some ⟨.P n (T.add a (.P 0 .Z .Z)) .Z⟩
    | _ => none
  base n := ⟨Nat.repeat (fun x => .P 0 x .Z) M (.P n .Z .Z)⟩
  parse? s := (parseT s).map (⟨·⟩)
  fmt s := String.ofList ((T.fmt s.t).pretty.toList.filter (· != ' '))
