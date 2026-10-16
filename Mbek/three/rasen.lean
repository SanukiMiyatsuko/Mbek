import Mbek.order

namespace MRF

inductive T where
| Z
| P (s0 : Nat) (s1 s2 s3 : T)
deriving DecidableEq, Inhabited

open T

def startsWithDigit : List Char → Bool
  | c :: _ => c.isDigit
  | [] => false

def consumeOnes : List Char → Nat → Nat × List Char
  | ' ' :: '+' :: ' ' :: '1' :: rest, n =>
      if startsWithDigit rest then
        (n, ' ' :: '+' :: ' ' :: '1' :: rest)
      else
        consumeOnes rest (n + 1)
  | cs, n => (n, cs)

def compressOnesAux : Nat → List Char → Bool → List Char
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, '1' :: rest, prevDigit =>
      if prevDigit then
        '1' :: compressOnesAux fuel rest true
      else
        let (n, remaining) := consumeOnes rest 1
        if n > 1 then
          (toString n).toList ++ compressOnesAux fuel remaining true
        else
          '1' :: compressOnesAux fuel rest true
  | fuel + 1, c :: rest, _ =>
      c :: compressOnesAux fuel rest c.isDigit

def compressOnes (s : String) : String :=
  let cs := s.toList
  String.ofList (compressOnesAux cs.length cs false)

def T.fmtRaw (t : T) : Std.Format :=
  match t with
  | Z => "0"
  | P 0 Z Z Z => "1"
  | P 0 Z (P 0 Z Z Z) Z => "ω"
  | P s0 s1 s2 Z =>
      f!"p({s0},{T.fmtRaw s1},{T.fmtRaw s2})"
  | P s0 s1 s2 s3 =>
      f!"p({s0},{T.fmtRaw s1},{T.fmtRaw s2}) + {T.fmtRaw s3}"

def T.fmt (t : T) : Std.Format :=
  Std.Format.text (compressOnes (T.fmtRaw t).pretty)

instance : Repr T where
  reprPrec t _ := T.fmt t

namespace T

private def removeWhitespace (s : String) : String :=
  String.ofList (s.toList.filter (fun c => !c.isWhitespace))

private def takeDigits : List Char → List Char × List Char
| [] => ([], [])
| c :: cs =>
  if c.isDigit then
    let (digits, rest) := takeDigits cs
    (c :: digits, rest)
  else
    ([], c :: cs)

private def parseNatChars
    (cs : List Char) : Option (Nat × List Char) :=
  let (digits, rest) := takeDigits cs
  if digits.isEmpty then
    none
  else
    let n := digits.foldl
      (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    some (n, rest)

private def expectChar
    (expected : Char) (cs : List Char) : Option (List Char) :=
  match cs with
  | c :: rest =>
      if c == expected then some rest else none
  | [] => none

partial def parseTermChars
    (cs : List Char) : Option (T × List Char) :=
  match cs with
  | '0' :: rest => some (Z, rest)
  | '1' :: rest => some (P 0 Z Z Z, rest)
  | 'ω' :: rest => some (P 0 Z (P 0 Z Z Z) Z, rest)
  | 'p' :: '(' :: rest => do
    let natResult ← parseNatChars rest
    let (s0, rest1) := natResult
    let rest2 ← expectChar ',' rest1
    let term1 ← parseTermChars rest2
    let (s1, rest3) := term1
    let rest4 ← expectChar ',' rest3
    let term2 ← parseTermChars rest4
    let (s2, rest5) := term2
    let rest6 ← expectChar ')' rest5
    match rest6 with
    | '+' :: rest7 => do
      let term3 ← parseTermChars rest7
      let (s3, rest8) := term3
      pure (P s0 s1 s2 s3, rest8)
    | _ => pure (P s0 s1 s2 Z, rest6)
  | _ => none

def ofString (s : String) : Option T :=
  let normalized := removeWhitespace s
  match parseTermChars normalized.toList with
  | some (t, []) => some t
  | _ => none

def parse! (s : String) : T :=
  match ofString s with
  | some t => t
  | none => panic! s!"T.parse!: failed to parse \"{s}\""

end T

inductive T.lt : T → T → Prop where
| Z_P (s0 : Nat) (s1 s2 s3 : T) : T.lt Z (P s0 s1 s2 s3)
| fst (s0 : Nat) (s1 s2 s3 : T) (t0 : Nat) (t1 t2 t3 : T) (h : s0 < t0) : T.lt (P s0 s1 s2 s3) (P t0 t1 t2 t3)
| snd (s0 : Nat) (s1 s2 s3 : T) (t1 t2 t3 : T) (h : T.lt s1 t1) : T.lt (P s0 s1 s2 s3) (P s0 t1 t2 t3)
| thd (s0 : Nat) (s1 s2 s3 : T) (t2 t3 : T) (h : T.lt s2 t2) : T.lt (P s0 s1 s2 s3) (P s0 s1 t2 t3)
| fth (s0 : Nat) (s1 s2 s3 : T) (t3 : T) (h : T.lt s3 t3) : T.lt (P s0 s1 s2 s3) (P s0 s1 s2 t3)

instance : LT T := ⟨T.lt⟩

theorem T.lt_inv (s0 : Nat) (s1 s2 s3 : T) (t0 : Nat) (t1 t2 t3 : T)
    (h : T.lt (P s0 s1 s2 s3) (P t0 t1 t2 t3)) :
    s0 < t0 ∨
      (s0 = t0 ∧ T.lt s1 t1) ∨
      (s0 = t0 ∧ s1 = t1 ∧ T.lt s2 t2) ∨
      (s0 = t0 ∧ s1 = t1 ∧ s2 = t2 ∧ T.lt s3 t3) := by
  cases h with
  | fst _ _ _ _ _ _ _ _ h => exact Or.inl h
  | snd _ _ _ _ _ _ _ h => exact Or.inr (Or.inl ⟨rfl, h⟩)
  | thd _ _ _ _ _ _ h => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩))
  | fth _ _ _ _ _ h => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, h⟩))

def T.decLt : (a b : T) → Decidable (T.lt a b)
  | .Z, .Z => isFalse (by intro h; cases h)
  | .Z, .P s0 s1 s2 s3 => isTrue (T.lt.Z_P s0 s1 s2 s3)
  | .P s0 s1 s2 s3, .Z => isFalse (by intro h; cases h)
  | .P s0 s1 s2 s3, .P t0 t1 t2 t3 => by
      by_cases h0 : s0 < t0
      · exact isTrue (T.lt.fst s0 s1 s2 s3 t0 t1 t2 t3 h0)
      · by_cases h0eq : s0 = t0
        · subst t0
          cases T.decLt s1 t1 with
          | isTrue h1 => exact isTrue (T.lt.snd s0 s1 s2 s3 t1 t2 t3 h1)
          | isFalse hn1 =>
            by_cases h1eq : s1 = t1
            · subst t1
              cases T.decLt s2 t2 with
              | isTrue h2 => exact isTrue (T.lt.thd s0 s1 s2 s3 t2 t3 h2)
              | isFalse hn2 =>
                by_cases h2eq : s2 = t2
                · subst t2
                  cases T.decLt s3 t3 with
                  | isTrue h3 => exact isTrue (T.lt.fth s0 s1 s2 s3 t3 h3)
                  | isFalse hn3 =>
                    exact isFalse (by
                      intro h
                      rcases T.lt_inv s0 s1 s2 s3 s0 s1 s2 t3 h with
                        hfirst | ⟨_, hsecond⟩ | ⟨_, _, hthird⟩ | ⟨_, _, _, hfourth⟩
                      · exact h0 hfirst
                      · exact hn1 hsecond
                      · exact hn2 hthird
                      · exact hn3 hfourth)
                · exact isFalse (by
                    intro h
                    rcases T.lt_inv s0 s1 s2 s3 s0 s1 t2 t3 h with
                      hfirst | ⟨_, hsecond⟩ | ⟨_, _, hthird⟩ | ⟨_, _, heq, _⟩
                    · exact h0 hfirst
                    · exact hn1 hsecond
                    · exact hn2 hthird
                    · exact h2eq heq)
            · exact isFalse (by
                intro h
                rcases T.lt_inv s0 s1 s2 s3 s0 t1 t2 t3 h with
                  hfirst | ⟨_, hsecond⟩ | ⟨_, heq, _⟩ | ⟨_, heq, _, _⟩
                · exact h0 hfirst
                · exact hn1 hsecond
                · exact h1eq heq
                · exact h1eq heq)
        · exact isFalse (by
            intro h
            rcases T.lt_inv s0 s1 s2 s3 t0 t1 t2 t3 h with
              hfirst | ⟨heq, _⟩ | ⟨heq, _, _⟩ | ⟨heq, _, _, _⟩
            · exact h0 hfirst
            · exact h0eq heq
            · exact h0eq heq
            · exact h0eq heq)

instance (a b : T) : Decidable (a < b) := T.decLt a b

def T.add : T → T → T
| Z, t => t
| P s0 s1 s2 s3, t => P s0 s1 s2 (T.add s3 t)

instance : Add T := ⟨T.add⟩

def T.mul : T → T → T
| _, Z => Z
| s, P _ _ _ t3 => s + mul s t3

def T.iter (F : T → T) : T → T
| Z => Z
| P _ _ _ t3 => F (iter F t3)

inductive T.Bound (t : T) : T → Prop where
| Z_holds : T.Bound t Z
| P_holds (s0 : Nat) (s1 s2 s3 : T) (h : P s0 s1 s2 Z < t) (hrec : T.Bound t s3) :
  T.Bound t (P s0 s1 s2 s3)

theorem Bound_inv (t : T) (s0 : Nat) (s1 s2 s3 : T) (h : T.Bound t (P s0 s1 s2 s3)) :
  P s0 s1 s2 Z < t ∧ T.Bound t s3 := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem Bound_Z_iff (t : T) : T.Bound t Z ↔ True := by
  exact ⟨fun _ => trivial, fun _ => T.Bound.Z_holds⟩

theorem Bound_P_iff (t : T) (s0 : Nat) (s1 s2 s3 : T) :
  T.Bound t (P s0 s1 s2 s3) ↔ (if P s0 s1 s2 Z < t then T.Bound t s3 else False) := by
  constructor
  · intro h
    have hp := Bound_inv t s0 s1 s2 s3 h
    simpa [hp.1] using hp.2
  · split
    · exact T.Bound.P_holds _ _ _ _ ‹_›
    · exact False.elim

def T.BoundDecidable : (t s : T) → Decidable (T.Bound t s)
| _, Z => isTrue T.Bound.Z_holds
| t, P s0 s1 s2 s3 =>
  if h : P s0 s1 s2 Z < t then
    match T.BoundDecidable t s3 with
    | isTrue hp => isTrue (T.Bound.P_holds s0 s1 s2 s3 h hp)
    | isFalse hn => isFalse (fun hcontra => hn (Bound_inv t s0 s1 s2 s3 hcontra).2)
  else
    isFalse (fun hcontra => h (Bound_inv t s0 s1 s2 s3 hcontra).1)

instance (t s : T) : Decidable (T.Bound t s) := T.BoundDecidable t s

def T.drop (t : T) : T → T
| Z => Z
| P s0 s1 s2 s3 =>
  if Bound t (P s0 s1 s2 s3) then
    P s0 s1 s2 s3
  else match s3 with
    | Z =>
      match s2 with
      | Z => drop t s1
      | P _ _ _ _ => drop t s2
    | P _ _ _ _ => drop t s3

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P 0 Z Z (T.ofNat n)

inductive Dom where
| zero
| one
| omega
| Omega (l0 : Nat) (l1 : T)
| Mahlo (l0 : Nat)
deriving DecidableEq

def T.dom (s : T) : Dom :=
  match s with
  | Z => .zero
  | P s0 s1 s2 s3 =>
    if s3 = Z then
      match dom s2 with
      | .zero =>
        match dom s1 with
        | .zero =>
          match s0 with
          | 0 => .one
          | _ + 1 => .Mahlo s0
        | .one => .Omega s0 s1
        | .omega => .omega
        | .Omega l0 l1 =>
          if P s0 s1 Z Z < P l0 l1 Z Z then
            .omega
          else .Omega l0 l1
        | .Mahlo l0 =>
          if s0 < l0 then
            if s0 < l0 - 1 then
              .omega
            else .Omega s0 s1
          else .Mahlo l0
      | .one => .omega
      | .omega => .omega
      | .Omega l0 l1 =>
        if P s0 s1 s2 Z < P l0 l1 Z Z then
          .omega
        else .Omega l0 l1
      | .Mahlo l0 =>
        if s0 < l0 then
          .omega
        else .Mahlo l0
    else dom s3

def T.fund (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 s3 =>
    if s3 = Z then
      match dom s2 with
      | .zero =>
        match dom s1 with
        | .zero =>
          match s0 with
          | 0 => Z
          | s0' + 1 => P s0' t Z Z
        | .one => P s0 (fund s1 Z) t Z
        | .omega => P s0 (fund s1 t) Z Z
        | .Omega l0 l1 =>
          if P s0 s1 Z Z < P l0 l1 Z Z then
            let F := fund s1
            P s0 (fund s1 (iter F t)) Z Z
          else P s0 (fund s1 t) Z Z
        | .Mahlo l0 =>
          if s0 < l0 then
            if s0 < l0 - 1 then
              let F := fund s1
              P s0 (fund s1 (iter F t)) Z Z
            else fund s1 (drop (P l0 Z Z Z) t)
          else P s0 (fund s1 t) Z Z
      | .one => mul (P s0 s1 (fund s2 Z) Z) t
      | .omega => P s0 s1 (fund s2 t) Z
      | .Omega l0 l1 =>
        if P s0 s1 s2 Z < P l0 l1 Z Z then
          let F := fund s2
          P s0 s1 (fund s2 (iter F t)) Z
        else P s0 s1 (fund s2 t) Z
      | .Mahlo l0 =>
        if s0 < l0 then
          let F := fund s2
          P s0 s1 (fund s2 (iter F t)) Z
        else P s0 s1 (fund s2 t) Z
    else P s0 s1 s2 (fund s3 t)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0),p(1,0,0)+p(0,p(1,0,0),0)))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0),p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0),0)))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0)+1,0))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0)+1,0),0))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(1,0,0),0))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),p(1,0,0)))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),p(1,0,0)+p(0,p(1,0,0),0)))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),p(1,0,0)+p(0,p(0,p(1,0,0),0),0)))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0))") (ofNat 4)

#eval fund (parse! "p(0,0,p(1,0,0)+p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0)+p(0,p(0,p(1,0,0),0),p(1,0,0)+p(0,p(1,0,0),0)),0))") (ofNat 4)

inductive T.isOT : T → Prop where
| base (n : Nat) : T.isOT (P 0 Z (P n Z Z Z) Z)
| step (s : T) (h : T.isOT s) (n : Nat) : T.isOT (T.fund s (T.ofNat n))

end MRF

namespace NMRF

inductive T where
| Z
| P (s0 : Nat) (s1 s2 s3 s4 : T)
deriving DecidableEq

open T

inductive T.lt : T → T → Prop where
| Z_P (s0 : Nat) (s1 s2 s3 s4 : T) : T.lt Z (P s0 s1 s2 s3 s4)
| fst (s0 : Nat) (s1 s2 s3 s4 : T) (t0 : Nat) (t1 t2 t3 t4 : T) (h : s0 < t0) : T.lt (P s0 s1 s2 s3 s4) (P t0 t1 t2 t3 t4)
| snd (s0 : Nat) (s1 s2 s3 s4 : T) (t1 t2 t3 t4 : T) (h : T.lt s1 t1) : T.lt (P s0 s1 s2 s3 s4) (P s0 t1 t2 t3 t4)
| thd (s0 : Nat) (s1 s2 s3 s4 : T) (t2 t3 t4 : T) (h : T.lt s2 t2) : T.lt (P s0 s1 s2 s3 s4) (P s0 s1 t2 t3 t4)
| fth (s0 : Nat) (s1 s2 s3 s4 : T) (t3 t4 : T) (h : T.lt s3 t3) : T.lt (P s0 s1 s2 s3 s4) (P s0 s1 s2 t3 t4)
| fif (s0 : Nat) (s1 s2 s3 s4 : T) (t4 : T) (h : T.lt s4 t4) : T.lt (P s0 s1 s2 s3 s4) (P s0 s1 s2 s3 t4)

instance : LT T := ⟨T.lt⟩

theorem T.lt_inv (s0 : Nat) (s1 s2 s3 s4 : T) (t0 : Nat) (t1 t2 t3 t4 : T)
    (h : T.lt (P s0 s1 s2 s3 s4) (P t0 t1 t2 t3 t4)) :
    s0 < t0 ∨
      (s0 = t0 ∧ T.lt s1 t1) ∨
      (s0 = t0 ∧ s1 = t1 ∧ T.lt s2 t2) ∨
      (s0 = t0 ∧ s1 = t1 ∧ s2 = t2 ∧ T.lt s3 t3) ∨
      (s0 = t0 ∧ s1 = t1 ∧ s2 = t2 ∧ s3 = t3 ∧ T.lt s4 t4) := by
  cases h with
  | fst _ _ _ _ _ _ _ _ _ _ h => exact Or.inl h
  | snd _ _ _ _ _ _ _ _ _ h => exact Or.inr (Or.inl ⟨rfl, h⟩)
  | thd _ _ _ _ _ _ _ _ h => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩))
  | fth _ _ _ _ _ _ _ h => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, h⟩)))
  | fif _ _ _ _ _ _ h => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, h⟩)))

def T.decLt : (a b : T) → Decidable (T.lt a b)
  | .Z, .Z => isFalse (by intro h; cases h)
  | .Z, .P s0 s1 s2 s3 s4 => isTrue (T.lt.Z_P s0 s1 s2 s3 s4)
  | .P s0 s1 s2 s3 s4, .Z => isFalse (by intro h; cases h)
  | .P s0 s1 s2 s3 s4, .P t0 t1 t2 t3 t4 => by
      by_cases h0 : s0 < t0
      · exact isTrue (T.lt.fst s0 s1 s2 s3 s4 t0 t1 t2 t3 t4 h0)
      · by_cases h0eq : s0 = t0
        · subst t0
          cases T.decLt s1 t1 with
          | isTrue h1 => exact isTrue (T.lt.snd s0 s1 s2 s3 s4 t1 t2 t3 t4 h1)
          | isFalse hn1 =>
            by_cases h1eq : s1 = t1
            · subst t1
              cases T.decLt s2 t2 with
              | isTrue h2 => exact isTrue (T.lt.thd s0 s1 s2 s3 s4 t2 t3 t4 h2)
              | isFalse hn2 =>
                by_cases h2eq : s2 = t2
                · subst t2
                  cases T.decLt s3 t3 with
                  | isTrue h3 => exact isTrue (T.lt.fth s0 s1 s2 s3 s4 t3 t4 h3)
                  | isFalse hn3 =>
                    by_cases h3eq : s3 = t3
                    · subst t3
                      cases T.decLt s4 t4 with
                      | isTrue h4 => exact isTrue (T.lt.fif s0 s1 s2 s3 s4 t4 h4)
                      | isFalse hn4 =>
                        exact isFalse (by
                          intro h
                          rcases T.lt_inv s0 s1 s2 s3 s4 s0 s1 s2 s3 t4 h with
                            hfirst | ⟨_, hsecond⟩ | ⟨_, _, hthird⟩ |
                            ⟨_, _, _, hfourth⟩ | ⟨_, _, _, _, hfifth⟩
                          · exact h0 hfirst
                          · exact hn1 hsecond
                          · exact hn2 hthird
                          · exact hn3 hfourth
                          · exact hn4 hfifth)
                    · exact isFalse (by
                        intro h
                        rcases T.lt_inv s0 s1 s2 s3 s4 s0 s1 s2 t3 t4 h with
                          hfirst | ⟨_, hsecond⟩ | ⟨_, _, hthird⟩ |
                          ⟨_, _, _, hfourth⟩ | ⟨_, _, _, heq, hfifth⟩
                        · exact h0 hfirst
                        · exact hn1 hsecond
                        · exact hn2 hthird
                        · exact hn3 hfourth
                        · exact h3eq heq)
                · exact isFalse (by
                    intro h
                    rcases T.lt_inv s0 s1 s2 s3 s4 s0 s1 t2 t3 t4 h with
                      hfirst | ⟨_, hsecond⟩ | ⟨_, _, hthird⟩ |
                      ⟨_, _, heq, _⟩ | ⟨_, _, heq, _, _⟩
                    · exact h0 hfirst
                    · exact hn1 hsecond
                    · exact hn2 hthird
                    · exact h2eq heq
                    · exact h2eq heq)
            · exact isFalse (by
                intro h
                rcases T.lt_inv s0 s1 s2 s3 s4 s0 t1 t2 t3 t4 h with
                  hfirst | ⟨_, hsecond⟩ | ⟨_, heq, _⟩ |
                  ⟨_, heq, _, _⟩ | ⟨_, heq, _, _, _⟩
                · exact h0 hfirst
                · exact hn1 hsecond
                · exact h1eq heq
                · exact h1eq heq
                · exact h1eq heq)
        · exact isFalse (by
            intro h
            rcases T.lt_inv s0 s1 s2 s3 s4 t0 t1 t2 t3 t4 h with
              hfirst | ⟨heq, _⟩ | ⟨heq, _, _⟩ | ⟨heq, _, _, _⟩ |
              ⟨heq, _, _, _, _⟩
            · exact h0 hfirst
            · exact h0eq heq
            · exact h0eq heq
            · exact h0eq heq
            · exact h0eq heq)

instance (a b : T) : Decidable (a < b) := T.decLt a b

def T.add : T → T → T
| Z, t => t
| P s0 s1 s2 s3 s4, t => P s0 s1 s2 s3 (T.add s4 t)

instance : Add T := ⟨T.add⟩

def T.mul : T → T → T
| _, Z => Z
| s, P _ _ _ _ t4 => s + mul s t4

def T.iter (F : T → T) : T → T
| Z => Z
| P _ _ _ _ t4 => F (iter F t4)

inductive T.Bound (t : T) : T → Prop where
| Z_holds : T.Bound t Z
| P_holds (s0 : Nat) (s1 s2 s3 s4 : T) (h : P s0 s1 s2 s3 Z < t) (hrec : T.Bound t s4) :
  T.Bound t (P s0 s1 s2 s3 s4)

theorem Bound_inv (t : T) (s0 : Nat) (s1 s2 s3 s4 : T) (h : T.Bound t (P s0 s1 s2 s3 s4)) :
  P s0 s1 s2 s3 Z < t ∧ T.Bound t s4 := by
  cases h; exact ⟨‹_›, ‹_›⟩

theorem Bound_Z_iff (t : T) : T.Bound t Z ↔ True := by
  exact ⟨fun _ => trivial, fun _ => T.Bound.Z_holds⟩

theorem Bound_P_iff (t : T) (s0 : Nat) (s1 s2 s3 s4 : T) :
  T.Bound t (P s0 s1 s2 s3 s4) ↔ (if P s0 s1 s2 s3 Z < t then T.Bound t s4 else False) := by
  constructor
  · intro h
    have hp := Bound_inv t s0 s1 s2 s3 s4 h
    simpa [hp.1] using hp.2
  · split
    · exact T.Bound.P_holds _ _ _ _ _ ‹_›
    · exact False.elim

def T.BoundDecidable : (t s : T) → Decidable (T.Bound t s)
| _, Z => isTrue T.Bound.Z_holds
| t, P s0 s1 s2 s3 s4 =>
  if h : P s0 s1 s2 s3 Z < t then
    match T.BoundDecidable t s4 with
    | isTrue hp => isTrue (T.Bound.P_holds s0 s1 s2 s3 s4 h hp)
    | isFalse hn => isFalse (fun hcontra => hn (Bound_inv t s0 s1 s2 s3 s4 hcontra).2)
  else
    isFalse (fun hcontra => h (Bound_inv t s0 s1 s2 s3 s4 hcontra).1)

instance (t s : T) : Decidable (T.Bound t s) := T.BoundDecidable t s

def T.drop (t : T) : T → T
| Z => Z
| P s0 s1 s2 s3 s4 =>
  if Bound t (P s0 s1 s2 s3 s4) then
    P s0 s1 s2 s3 s4
  else
    match s4 with
    | Z =>
      match s3 with
      | Z =>
        match s2 with
        | Z => drop t s1
        | P _ _ _ _ _ => drop t s2
      | P _ _ _ _ _ => drop t s3
    | P _ _ _ _ _ => drop t s4

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P 0 Z Z Z (T.ofNat n)

inductive Dom where
| zero
| one
| omega
| Omega (l0 : Nat) (l1 : T) (l2 : T)
| Mahlo (l0 : Nat) (l1 : T)
| Nahlo (l0 : Nat)
deriving DecidableEq

def T.dom (s : T) : Dom :=
  match s with
  | Z => .zero
  | P s0 s1 s2 s3 s4 =>
    if s4 = Z then
      match dom s3 with
      | .zero =>
        match dom s2 with
        | .zero =>
          match dom s1 with
          | .zero =>
            match s0 with
            | 0 => .one
            | _ + 1 => .Nahlo s0
          | .one => .Mahlo s0 s1
          | .omega => .omega
          | .Omega l0 l1 l2 =>
            if P s0 s1 Z Z Z < P l0 l1 Z Z Z then
              .omega
            else .Mahlo l0 l1
          | .Mahlo l0 l1 =>
            if P s0 s1 Z Z Z < P l0 l1 Z Z Z then
              .omega
            else .Mahlo l0 l1
          | .Nahlo l0 =>
            if s0 < l0 then
              if s0 < l0 - 1 then
                .omega
              else .Mahlo s0 s1
            else .Nahlo l0
        | .one => .Omega s0 s1 s2
        | .omega => .omega
        | .Omega l0 l1 l2 =>
          if P s0 s1 s2 Z Z < P l0 l1 l2 Z Z then
            .omega
          else .Omega l0 l1 l2
        | .Mahlo l0 l1 =>
          if P s0 s1 s2 Z Z < P l0 l1 Z Z Z then
            sorry
          else .Mahlo l0 l1
        | .Nahlo l0 =>
          if s0 < l0 then
            .omega
          else .Nahlo l0
      | .one => .omega
      | .omega => .omega
      | .Omega l0 l1 l2 =>
        if P s0 s1 s2 s3 Z < P l0 l1 l2 Z Z then
          .omega
        else .Omega l0 l1 l2
      | .Mahlo l0 l1 =>
        if P s0 s1 s2 s3 Z < P l0 l1 Z Z Z then
          .omega
        else .Mahlo l0 l1
      | .Nahlo l0 =>
        if s0 < l0 then
          .omega
        else .Nahlo l0
    else dom s4

def T.fund (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 s3 s4 =>
    if s4 = Z then
      match dom s3 with
      | .zero =>
        match dom s2 with
        | .zero =>
          match dom s1 with
          | .zero =>
            match s0 with
            | 0 => Z
            | s0' + 1 => P s0' t Z Z Z
          | .one => P s0 (fund s1 Z) t Z Z
          | .omega => P s0 (fund s1 t) Z Z Z
          | .Omega l0 l1 l2 =>
            if P s0 s1 Z Z Z < P l0 l1 l2 Z Z then
              let F := fund s1
              P s0 (fund s1 (iter F t)) Z Z Z
            else P s0 (fund s1 t) Z Z Z
          | .Mahlo l0 l1 =>
            if P s0 s1 Z Z Z < P l0 l1 Z Z Z then
              let F := fund s1
              P s0 (fund s1 (iter F t)) Z Z Z
            else P s0 (fund s1 t) Z Z Z
          | .Nahlo l0 =>
            if s0 < l0 then
              if s0 < l0 - 1 then
                let F := fund s1
                P s0 (fund s1 (iter F t)) Z Z Z
              else P s0 (fund s1 (drop (P (l0 + 1) Z Z Z Z) t)) Z Z Z
            else P s0 (fund s1 t) Z Z Z
        | .one => P s0 s1 (fund s2 Z) t Z
        | .omega => P s0 s1 (fund s2 t) Z Z
        | .Omega l0 l1 l2 =>
          if P s0 s1 s2 Z Z < P l0 l1 l2 Z Z then
            let F := fund s2
            P s0 s1 (fund s2 (iter F t)) Z Z
          else P s0 s1 (fund s2 t) Z Z
        | .Mahlo l0 l1 =>
          if P s0 s1 s2 Z Z < P l0 l1 Z Z Z then
            sorry
          else P s0 s1 (fund s2 t) Z Z
        | .Nahlo l0 =>
          if s0 < l0 then
            let F := fund s2
            P s0 s1 (fund s2 (iter F t)) Z Z
          else P s0 s1 (fund s2 t) Z Z
      | .one => mul (P s0 s1 s2 (fund s3 Z) Z) t
      | .omega => P s0 s1 s2 (fund s3 t) Z
      | .Omega l0 l1 l2 =>
        if P s0 s1 s2 s3 Z < P l0 l1 l2 Z Z then
          let F := fund s3
          P s0 s1 s2 (fund s3 (iter F t)) Z
        else P s0 s1 s2 (fund s3 t) Z
      | .Mahlo l0 l1 =>
        if P s0 s1 s2 s3 Z < P l0 l1 Z Z Z then
          let F := fund s3
          P s0 s1 s2 (fund s3 (iter F t)) Z
        else P s0 s1 s2 (fund s3 t) Z
      | .Nahlo l0 =>
        if s0 < l0 then
          let F := fund s3
          P s0 s1 s2 (fund s3 (iter F t)) Z
        else P s0 s1 s2 (fund s3 t) Z
    else P s0 s1 s2 s3 (fund s4 t)

inductive T.isOT : T → Prop where
| base (n : Nat) : T.isOT (P 0 Z Z (P n Z Z Z Z) Z)
| step (s : T) (h : T.isOT s) (n : Nat) : T.isOT (T.fund s (T.ofNat n))

end NMRF
