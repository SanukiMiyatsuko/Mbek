import Mbek.order

inductive T where
| Z : T
| P : Nat → T → T → T
deriving DecidableEq, Inhabited

open T

def T.fmtJoin : List Std.Format → Std.Format
  | []      => f!""
  | [x]     => x
  | x :: xs => f!"{x} + {T.fmtJoin xs}"

def T.fmtChain : T → List Std.Format
  | Z => []
  | P n t0 t1 =>
    let head :=
      match T.fmtChain t0 with
      | []  => f!"{n}"
      | [e] => f!"{n}^{e}"
      | es  => f!"{n}^({T.fmtJoin es})"
    head :: T.fmtChain t1

def T.fmt (t : T) : Std.Format :=
  match T.fmtChain t with
  | [] => "Z"
  | xs => T.fmtJoin xs

instance : Repr T where
  reprPrec t _ := T.fmt t

structure BIter where
  b : ByteArray
  i : Nat

def mkBIter (s : String) : BIter := { b := s.toUTF8, i := 0 }

def BIter.hasNext (it : BIter) : Bool := it.i < it.b.size

def BIter.curr (it : BIter) : UInt8 := it.b.get! it.i

def BIter.next (it : BIter) : BIter := { it with i := it.i + 1 }

def Parser (α : Type) := BIter → Option (α × BIter)

instance : Monad Parser where
  pure a := fun it => some (a, it)
  bind p f := fun it =>
    match p it with
    | none => none
    | some (a, it') => f a it'

instance : OrElse (Parser α) where
  orElse p q := fun it =>
    match p it with
    | some r => some r
    | none => q () it

def Parser.fail : Parser α := fun _ => none

def peekCh : Parser (Option UInt8) := fun it =>
  some ((if it.hasNext then some it.curr else none), it)

def pchar (c : Char) : Parser Unit := fun it =>
  if it.hasNext ∧ it.curr = c.toNat.toUInt8 then some ((), it.next) else none

def isDigitByte (b : UInt8) : Bool :=
  (48 : UInt8) ≤ b ∧ b ≤ (57 : UInt8)

def pdigit : Parser UInt8 := fun it =>
  if it.hasNext ∧ isDigitByte it.curr then some (it.curr, it.next) else none

def pmanyChar (fuel : Nat) (p : Parser UInt8) : Parser (List UInt8) :=
  match fuel with
  | 0 => fun it => some ([], it)
  | n + 1 =>
    fun it =>
      match p it with
      | none => some ([], it)
      | some (c, it') =>
        match pmanyChar n p it' with
        | some (cs, it'') => some (c :: cs, it'')
        | none => some ([c], it')
termination_by fuel

def pws (fuel : Nat) : Parser Unit :=
  match fuel with
  | 0 => fun it => some ((), it)
  | n + 1 =>
    fun it =>
      if it.hasNext ∧ it.curr = (32 : UInt8) then pws n it.next else some ((), it)
termination_by fuel

def pnat (fuel : Nat) : Parser Nat := do
  let cs ← pmanyChar fuel pdigit
  if cs.isEmpty then Parser.fail
  else pure (cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)

def pZ : Parser T := do
  pchar 'Z'
  pure T.Z

mutual
def pmonomial (fuel : Nat) : Parser (Nat × T) :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    let nn ← pnat (k + 1)
    pws (k + 1)
    match ← peekCh with
    | some c =>
      if c = ('^'.toNat.toUInt8) then do
        pchar '^'
        pws (k + 1)
        let e ← pexponent k
        pure (nn, e)
      else
        pure (nn, T.Z)
    | none => pure (nn, T.Z)
termination_by fuel

def pexponent (fuel : Nat) : Parser T :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    match ← peekCh with
    | some c =>
      if c = ('('.toNat.toUInt8) then do
        pchar '('
        pws (k + 1)
        let ms ← pchainList k
        pws (k + 1)
        pchar ')'
        pure (ms.foldr (fun (n, t0) acc => T.P n t0 acc) T.Z)
      else do
        let (n, t0) ← pmonomial k
        pure (T.P n t0 T.Z)
    | none => do
        let (n, t0) ← pmonomial k
        pure (T.P n t0 T.Z)
termination_by fuel

def pchainList (fuel : Nat) : Parser (List (Nat × T)) :=
  match fuel with
  | 0 => Parser.fail
  | k + 1 => do
    let m ← pmonomial k
    pws (k + 1)
    let rest ← pchainListRest k
    pure (m :: rest)
termination_by fuel

def pchainListRest (fuel : Nat) : Parser (List (Nat × T)) :=
  match fuel with
  | 0 => pure []
  | k + 1 =>
    (do
      pchar '+'
      pws (k + 1)
      let m ← pmonomial k
      pws (k + 1)
      let rest ← pchainListRest k
      pure (m :: rest))
    <|> pure []
termination_by fuel
end

def initFuel (s : String) : Nat := 8 * s.toUTF8.size + 64

def pTop (fuel : Nat) : Parser T :=
  pZ <|> (do
    let ms ← pchainList fuel
    pure (ms.foldr (fun (n, t0) acc => T.P n t0 acc) T.Z))

def parseT (s : String) : Option T := do
  let fuel := initFuel s
  let it0 := mkBIter s
  let (_, it1) ← pws fuel it0
  let (t, it2) ← pTop fuel it1
  let (_, it3) ← pws fuel it2
  if it3.hasNext then none else some t

def T.parse! (s : String) : T :=
  match parseT s with
  | some t => t
  | none   => panic! s!"T.parse!: failed to parse \"{s}\""

def T.add : T → T → T
| Z, t => t
| s, Z => s
| P s0 s1 s2, t =>
  P s0 s1 (s2.add t)

instance : Add T where
  add := T.add

theorem T.add_Z (a : T) : T.add a Z = a := by
  cases a with rfl

theorem T.P_add_eq (s0 : Nat) (s1 s2 y : T) : T.add (P s0 s1 s2) y = P s0 s1 (T.add s2 y) := by
  cases y with
  | Z => rw [T.add_Z s2]; rfl
  | P u0 u1 u2 => rfl

theorem T.exists_add_eq_P (a : T) (t0 : Nat) (t1 t2 : T) : ∃ u0 u1 u2, T.add a (P t0 t1 t2) = P u0 u1 u2 := by
  cases a with
  | Z => exact ⟨t0, t1, t2, rfl⟩
  | P s0 s1 s2 => exact ⟨s0, s1, T.add s2 (P t0 t1 t2), rfl⟩

inductive T.Lt : T → T → Prop where
| Z_lt_P (n : Nat) (t1 t2 : T) :
  Z.Lt (P n t1 t2)
| p_head (s0 t0 : Nat) (s1 t1 s2 t2 : T) (h : s0 < t0) :
  (P s0 s1 s2).Lt (P t0 t1 t2)
| p_mid (s0 : Nat) (s1 t1 : T) (s2 t2 : T) (h : T.Lt s1 t1) :
  (P s0 s1 s2).Lt (P s0 t1 t2)
| p_tail (s0 : Nat) (s1 : T) (s2 t2 : T) (h : T.Lt s2 t2) :
  (P s0 s1 s2).Lt (P s0 s1 t2)

instance : LT T where
  lt a b := a.Lt b

theorem lt_Z_Z_inv (h : Z < Z) : False := by
  cases h

theorem lt_P_Z_inv (s0 : Nat) (s1 s2 : T) (h : (P s0 s1 s2) < Z) : False := by
  cases h

theorem lt_Z_inv {a : T} (h : a < Z) : False := by
  cases h

theorem lt_inv (s0 : Nat) (s1 s2 : T) (t0 : Nat) (t1 t2 : T) (h : (P s0 s1 s2).Lt (P t0 t1 t2)) :
  s0 < t0 ∨ (s0 = t0 ∧ s1.Lt t1) ∨ (s0 = t0 ∧ s1 = t1 ∧ s2.Lt t2) := by
  cases h with
  | p_head _ _ _ _ _ _ h => exact Or.inl h
  | p_mid _ _ _ _ _ h => exact Or.inr (Or.inl ⟨rfl, h⟩)
  | p_tail _ _ _ _ h => exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)

def T.decLt (a b : T) : Decidable (a.Lt b) :=
  match a, b with
  | Z, Z => isFalse lt_Z_Z_inv
  | Z, P n t1 t2 => isTrue (T.Lt.Z_lt_P n t1 t2)
  | P s0 s1 s2, Z => isFalse (lt_P_Z_inv s0 s1 s2)
  | P s0 s1 s2, P t0 t1 t2 =>
    if h0 : s0 < t0 then
      isTrue (T.Lt.p_head s0 t0 s1 t1 s2 t2 h0)
    else
      if heq0 : s0 = t0 then
        match t0, heq0 with
        | _, rfl =>
          match T.decLt s1 t1 with
          | isTrue h1 => isTrue (T.Lt.p_mid s0 s1 t1 s2 t2 h1)
          | isFalse hn1 =>
            if heq1 : s1 = t1 then
              match t1, heq1 with
              | _, rfl =>
                match T.decLt s2 t2 with
                | isTrue h2 => isTrue (T.Lt.p_tail s0 s1 s2 t2 h2)
                | isFalse hn2 =>
                  isFalse (fun h =>
                    match lt_inv s0 s1 s2 s0 s1 t2 h with
                    | Or.inl h_lt => h0 h_lt
                    | Or.inr (Or.inl h_and) => hn1 h_and.2
                    | Or.inr (Or.inr h_and) => hn2 h_and.2.2
                  )
            else
              isFalse (fun h =>
                match lt_inv s0 s1 s2 s0 t1 t2 h with
                | Or.inl h_lt => h0 h_lt
                | Or.inr (Or.inl h_and) => hn1 h_and.2
                | Or.inr (Or.inr h_and) => heq1 h_and.2.1
              )
      else
        isFalse (fun h =>
          match lt_inv s0 s1 s2 t0 t1 t2 h with
          | Or.inl h_lt => h0 h_lt
          | Or.inr (Or.inl h_and) => heq0 h_and.1
          | Or.inr (Or.inr h_and) => heq0 h_and.1
        )

instance (a b : T) : Decidable (a < b) :=
  T.decLt a b

theorem nat_lt_total (n m : Nat) : n < m ∨ m < n ∨ n = m := by
  omega

theorem lt_irrefl_thm (a : T) : ¬ a.Lt a := by
  induction a with
  | Z => exact lt_Z_inv
  | P s0 s1 s2 ih1 ih2 =>
      intro h
      cases h with
      | p_head _ _ _ _ _ _ h => exact Nat.lt_irrefl _ h
      | p_mid _ _ _ _ _ h => exact ih1 h
      | p_tail _ _ _ _ h => exact ih2 h

theorem lt_trans_thm (a : T) : ∀ b c : T, a.Lt b → b.Lt c → a.Lt c := by
  induction a with
  | Z => intro b c _ h; cases h <;> exact T.Lt.Z_lt_P _ _ _
  | P a0 a1 a2 ih1 ih2 =>
      intro b c h1 h2
      cases h1 with
      | p_head _ _ _ _ _ _ h1 =>
          cases h2 <;> apply T.Lt.p_head <;> omega
      | p_mid _ _ _ _ _ h1 =>
          cases h2 with
          | p_head _ _ _ _ _ _ h2 => exact T.Lt.p_head _ _ _ _ _ _ h2
          | p_mid _ _ _ _ _ h2 => exact T.Lt.p_mid _ _ _ _ _ (ih1 _ _ h1 h2)
          | p_tail _ _ _ _ _ => exact T.Lt.p_mid _ _ _ _ _ h1
      | p_tail _ _ _ _ h1 =>
          cases h2 with
          | p_head _ _ _ _ _ _ h2 => exact T.Lt.p_head _ _ _ _ _ _ h2
          | p_mid _ _ _ _ _ h2 => exact T.Lt.p_mid _ _ _ _ _ h2
          | p_tail _ _ _ _ h2 => exact T.Lt.p_tail _ _ _ _ (ih2 _ _ h1 h2)

theorem lt_asymm_thm {a b : T} (h : a < b) : ¬ (b < a) := by
  intro hba
  exact lt_irrefl_thm a (lt_trans_thm a b a h hba)

theorem lt_total_thm (a b : T) : a.Lt b ∨ b.Lt a ∨ a = b := by
  induction a generalizing b with
  | Z =>
      cases b with
      | Z => exact Or.inr (Or.inr rfl)
      | P _ _ _ => exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | P a0 a1 a2 ih1 ih2 =>
      cases b with
      | Z => exact Or.inr (Or.inl (T.Lt.Z_lt_P _ _ _))
      | P b0 b1 b2 =>
          rcases nat_lt_total a0 b0 with h | h | rfl
          · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h)
          · exact Or.inr (Or.inl (T.Lt.p_head _ _ _ _ _ _ h))
          · rcases ih1 b1 with h | h | rfl
            · exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
            · exact Or.inr (Or.inl (T.Lt.p_mid _ _ _ _ _ h))
            · rcases ih2 b2 with h | h | rfl
              · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
              · exact Or.inr (Or.inl (T.Lt.p_tail _ _ _ _ h))
              · exact Or.inr (Or.inr rfl)

instance : strict_partial_order T where
  irrefl a := lt_irrefl_thm a
  trans a b c hf hs := lt_trans_thm a b c hf hs

instance : strict_linear_order T where
  total a b := lt_total_thm a b

theorem T.Z_le (s : T) : Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P _ _ _ => exact Or.inl (T.Lt.Z_lt_P _ _ _)

theorem add_lt_add_of_ne_Z (a X : T) (h : X ≠ Z) : a < T.add a X := by
  induction a with
  | Z => cases X with
      | Z => exact False.elim (h rfl)
      | P _ _ _ => exact T.Lt.Z_lt_P _ _ _
  | P a0 a1 a2 _ ih =>
      rw [T.P_add_eq]
      exact T.Lt.p_tail _ _ _ _ ih

theorem sandwich_tail (s0 : Nat) (s1 X c Y : T) (h1 : P s0 s1 X < c) (h2 : c < P s0 s1 Y) :
    ∃ c2, c = P s0 s1 c2 ∧ X < c2 ∧ c2 < Y := by
  cases h1 <;> cases h2 <;> try (exfalso; omega)
  all_goals first
    | exact ⟨_, rfl, ‹_›, ‹_›⟩
    | exact False.elim (lt_irrefl_thm _ ‹_›)
    | exact False.elim (lt_asymm_thm ‹_› ‹_›)

theorem sandwich_mid_tail (s0 : Nat) (X W Y c' : T) (h1 : P s0 X W < c') (h2 : c' < P s0 Y Z) :
    ∃ c1 c2, c' = P s0 c1 c2 ∧ ((X < c1 ∧ c1 < Y) ∨ (c1 = X ∧ W < c2)) := by
  cases h1 <;> cases h2 <;> try (exfalso; omega)
  all_goals first
    | exact ⟨_, _, rfl, Or.inl ⟨‹_›, ‹_›⟩⟩
    | exact ⟨_, _, rfl, Or.inr ⟨rfl, ‹_›⟩⟩
    | exact False.elim (lt_Z_inv ‹_›)

theorem sandwich_mid (s0 : Nat) (X Y c : T) (_hXY : X < Y) (h1 : P s0 X Z < c) (h2 : c < P s0 Y Z) :
    ∃ c1 c2, c = P s0 c1 c2 ∧ X ≤ c1 ∧ c1 < Y := by
  obtain ⟨c1, c2, rfl, h⟩ := sandwich_mid_tail s0 X Z Y c h1 h2
  rcases h with h | ⟨rfl, _⟩
  · exact ⟨c1, c2, rfl, Or.inl h.1, h.2⟩
  · exact ⟨_, c2, rfl, Or.inr rfl, _hXY⟩

def T.mul : T → T → T
| _, Z => Z
| a, P _ _ m2 => mul a m2 + a

inductive T.index_Prop (t : T) : T → Prop where
| Z_holds : T.index_Prop t Z
| P_holds (s0 : Nat) (s1 s2 : T) (h : P s0 s1 Z < t) (hrec : T.index_Prop t s2) :
  T.index_Prop t (P s0 s1 s2)

theorem index_Prop_inv (t : T) (s0 : Nat) (s1 s2 : T) (h : T.index_Prop t (P s0 s1 s2)) :
  P s0 s1 Z < t ∧ T.index_Prop t s2 := by
  cases h with
  | P_holds _ _ _ hlt hrec =>
    exact ⟨hlt, hrec⟩

theorem index_Prop_Z_iff (t : T) : T.index_Prop t Z ↔ True := by
  exact ⟨fun _ => trivial, fun _ => T.index_Prop.Z_holds⟩

theorem index_Prop_P_iff (t : T) (s0 : Nat) (s1 s2 : T) :
  T.index_Prop t (P s0 s1 s2) ↔ (if P s0 s1 Z < t then T.index_Prop t s2 else False) := by
  constructor
  · intro h
    have hp := index_Prop_inv t s0 s1 s2 h
    simpa [hp.1] using hp.2
  · split
    · exact T.index_Prop.P_holds _ _ _ ‹_›
    · exact False.elim

def T.indexPropDecidable : (t s : T) → Decidable (T.index_Prop t s)
| _, Z => isTrue T.index_Prop.Z_holds
| t, P s0 s1 s2 =>
  if h : P s0 s1 Z < t then
    match T.indexPropDecidable t s2 with
    | isTrue hp => isTrue (T.index_Prop.P_holds s0 s1 s2 h hp)
    | isFalse hn => isFalse (fun hcontra => hn (index_Prop_inv t s0 s1 s2 hcontra).2)
  else
    isFalse (fun hcontra => h (index_Prop_inv t s0 s1 s2 hcontra).1)

instance (t s : T) : Decidable (T.index_Prop t s) := T.indexPropDecidable t s

def T.drop (t : T) : T → T
| Z => Z
| P s0 s1 s2 =>
  if T.index_Prop t (P s0 s1 s2) then
    P s0 s1 s2
  else match s2 with
    | Z => drop t s1
    | P _ _ _ => drop t s2

def T.size : T → Nat
| Z => 0
| P _ t1 t2 => t1.size + t2.size + 1

theorem T.size_P (s0 : Nat) (s1 s2 : T) : (P s0 s1 s2).size = s1.size + s2.size + 1 := rfl

theorem T.size_lt_size_P_left (s0 : Nat) (s1 s2 : T) : s1.size < (P s0 s1 s2).size := by
  simp only [T.size]
  omega

theorem T.size_lt_size_P_right (s0 : Nat) (s1 s2 : T) : s2.size < (P s0 s1 s2).size := by
  simp only [T.size]
  omega

theorem T.drop_size_le : ∀ (t s : T), (T.drop t s).size ≤ s.size := by
  intro t s
  induction s with
  | Z => exact Nat.le_refl _
  | P s0 s1 s2 ih1 ih2 =>
      unfold T.drop
      split
      · exact Nat.le_refl _
      · cases s2 <;> simp only [T.size] at * <;> omega

inductive T.IsN : T → Prop
| zero : T.IsN Z
| succ : ∀ t : T, T.IsN t → T.IsN (P 0 Z t)

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P 0 Z (T.ofNat n)

theorem ofNat_IsN : ∀ n : Nat, T.IsN (T.ofNat n) := by
  intro n
  induction n with
  | zero => exact T.IsN.zero
  | succ n ih => exact T.IsN.succ _ ih

theorem mul_shape (s0 : Nat) (c t : T) (h : T.IsN t) :
    T.mul (P s0 c Z) t = Z ∨ ∃ Y, T.mul (P s0 c Z) t = P s0 c Y := by
  induction h with
  | zero => exact Or.inl rfl
  | succ t _ ih =>
      rw [T.mul.eq_2]
      rcases ih with h | ⟨y, h⟩
      · exact Or.inr ⟨Z, by rw [h]; rfl⟩
      · exact Or.inr ⟨T.add y (P s0 c Z), by rw [h]; exact T.P_add_eq _ _ _ _⟩

theorem mul_ofNat_one_step (X : T) (hX : X ≠ Z) (n : Nat) :
    T.mul X (T.ofNat n) < T.mul X (T.ofNat (n+1)) := by
  exact add_lt_add_of_ne_Z _ X hX

theorem mul_ofNat_strict_mono (X : T) (hX : X ≠ Z) (n1 : Nat) :
    ∀ n0, n0 < n1 → T.mul X (T.ofNat n0) < T.mul X (T.ofNat n1) := by
  induction n1 with
  | zero => intro n0 h; omega
  | succ n ih =>
      intro n0 h
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
      · exact lt_trans_thm _ _ _ (ih n0 h) (mul_ofNat_one_step X hX n)
      · exact mul_ofNat_one_step X hX _

theorem add_eq_hAdd (a b : T) : T.add a b = a + b := rfl

theorem mul_add_shape (s0 : Nat) (c : T) :
    ∀ n : Nat, (T.mul (P s0 c Z) (T.ofNat n)).add (P s0 c Z) = P s0 c (T.mul (P s0 c Z) (T.ofNat n)) := by
  intro n
  induction n with
  | zero =>
    rw [T.ofNat.eq_1, T.mul.eq_1, T.add.eq_1]
  | succ n ih =>
    rw [T.ofNat.eq_2, T.mul.eq_2, ← add_eq_hAdd, ih, T.P_add_eq s0 c (T.mul (P s0 c Z) (T.ofNat n)) (P s0 c Z), ih]

theorem mul_succ_shape (s0 : Nat) (c : T) :
    ∀ n : Nat, T.mul (P s0 c Z) (T.ofNat (n+1)) = P s0 c (T.mul (P s0 c Z) (T.ofNat n)) := by
  intro n
  rw [T.ofNat.eq_2, T.mul.eq_2, ← add_eq_hAdd, mul_add_shape s0 c n]

theorem tail_lt_wrap (s0 : Nat) (c : T) :
    ∀ n : Nat, T.mul (P s0 c Z) (T.ofNat n) < P s0 c (T.mul (P s0 c Z) (T.ofNat n)) := by
  intro n
  induction n with
  | zero => exact T.Lt.Z_lt_P _ _ _
  | succ n ih =>
      rw [mul_succ_shape]
      exact T.Lt.p_tail _ _ _ _ ih

theorem ofNat_one_step (n : Nat) : T.ofNat n < T.ofNat (n+1) := by
  induction n with
  | zero => exact T.Lt.Z_lt_P _ _ _
  | succ n ih => exact T.Lt.p_tail _ _ _ _ ih

theorem ofNat_strict_mono {n m : Nat} (h : n < m) : T.ofNat n < T.ofNat m := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
      · exact lt_trans_thm _ _ _ (ih h) (ofNat_one_step m)
      · exact ofNat_one_step _

theorem ofNat_reflect_lt {n m : Nat} (h : T.ofNat n < T.ofNat m) : n < m := by
  rcases nat_lt_total n m with hlt | hgt | rfl
  · exact hlt
  · exact False.elim (lt_asymm_thm h (ofNat_strict_mono hgt))
  · exact False.elim (lt_irrefl_thm _ h)

theorem IsN_exists_ofNat {t : T} (h : T.IsN t) : ∃ n, t = T.ofNat n := by
  induction h with
  | zero => exact ⟨0, rfl⟩
  | succ t _ ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, rfl⟩

def T.iter (F : T → T) : T → T
| Z => Z
| P _ _ m2 => F (iter F m2)

def T.takeAt (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s = t then
      Z
    else if s2 = Z then
      P s0 (T.takeAt s1 t) Z
    else P s0 s1 (T.takeAt s2 t)

def T.head : T → T
| Z => Z
| P s0 s1 _ => P s0 s1 Z

theorem T.head_mono {y x : T} (h : y < x) : T.head y ≤ T.head x := by
  cases h with
  | Z_lt_P _ _ _ => exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | p_head _ _ _ _ _ _ h => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h)
  | p_mid _ _ _ _ _ h => exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
  | p_tail _ _ _ _ _ => exact Or.inr rfl

theorem T.head_add_Z (w X : T) (hw : w = Z) : T.head (T.add w X) = T.head X := by
  rw [hw, T.add.eq_1]

theorem T.head_add_ne_Z (w0 : Nat) (w1 w2 X : T) : T.head (T.add (P w0 w1 w2) X) = T.head (P w0 w1 w2) := by
  rw [T.P_add_eq w0 w1 w2 X]
  rfl

def T.listLe (L L' : List T) : Prop := ∀ x ∈ L, ∃ y ∈ L', x ≤ y

theorem listLe_refl' (L : List T) : T.listLe L L := by
  intro x hx
  exact ⟨x, hx, Or.inr rfl⟩

theorem listLe_self_append (L L' : List T) : T.listLe L (L ++ L') := by
  intro x hx
  exact ⟨x, List.mem_append_left _ hx, Or.inr rfl⟩

theorem listLe_append_congr (Pre L1 L2 : List T) (h : T.listLe L1 L2) :
    T.listLe (Pre ++ L1) (Pre ++ L2) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨x, List.mem_append_left _ hx, Or.inr rfl⟩
  · obtain ⟨y, hy, hxy⟩ := h x hx
    exact ⟨y, List.mem_append_right _ hy, hxy⟩

theorem listLe_trans (L1 L2 L3 : List T) (h1 : T.listLe L1 L2) (h2 : T.listLe L2 L3) :
    T.listLe L1 L3 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h1 x hx
  obtain ⟨z, hz, hyz⟩ := h2 y hy
  exact ⟨z, hz, partial_order.trans x y z hxy hyz⟩
