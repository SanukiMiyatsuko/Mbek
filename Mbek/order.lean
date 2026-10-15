class strict_partial_order (A : Type u) [LT A] where
  irrefl : ∀ a : A, ¬ a < a
  trans : ∀ a b c : A, a < b → b < c → a < c

open strict_partial_order

variable (A : Type u) [LT A] [strict_partial_order A]

theorem lt_neq (a b : A) (h_lt : a < b) : a ≠ b := by
  rintro rfl
  exact irrefl a h_lt

instance : LE A where
  le a b := a < b ∨ a = b

instance (a b : A) [DecidableEq A] [Decidable (a < b)] : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

class partial_order where
  refl : ∀ a : A, a ≤ a
  trans : ∀ a b c : A, a ≤ b → b ≤ c → a ≤ c
  antisymm : ∀ a b : A, a ≤ b → b ≤ a → a = b

instance : partial_order A where
  refl a := by
    exact Or.inr rfl

  trans a b c h0 h1 := by
    rcases h0 with h0 | rfl
    · rcases h1 with h1 | rfl
      · exact Or.inl (trans a b c h0 h1)
      · exact Or.inl h0
    · exact h1

  antisymm a b h0 h1 := by
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · exact False.elim (irrefl a (trans a b a h0 h1))
      · exact h1.symm
    · exact h0

open partial_order

theorem lt_of_le_of_lt_thm (a b c : A) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rcases h1 with h1 | rfl
  · exact trans a b c h1 h2
  · exact h2

theorem lt_of_lt_of_le_thm (a b c : A) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rcases h2 with h2 | rfl
  · exact trans a b c h1 h2
  · exact h1

class strict_linear_order extends strict_partial_order A where
  total : ∀ a b : A, a < b ∨ b < a ∨ a = b

open strict_linear_order

variable (A : Type u) [LT A] [strict_linear_order A]

instance : LE A where
  le a b := a < b ∨ a = b

class linear_order extends partial_order A where
  total : ∀ a b : A, a ≤ b ∨ b ≤ a

instance : linear_order A where
  total a b := by
    rcases total a b with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)

namespace FundOrder

inductive TransClosure {α : Sort u} (r : α → α → Prop) : α → α → Prop where
| single {a b : α} : r a b → TransClosure r a b
| tail {a b c : α} : TransClosure r a b → r b c → TransClosure r a c

theorem TransClosure.trans {α : Sort u} {r : α → α → Prop}
    {a b c : α} (hab : TransClosure r a b) (hbc : TransClosure r b c) :
    TransClosure r a c := by
  induction hbc with
  | single hstep => exact .tail hab hstep
  | tail _ hstep ih => exact .tail ih hstep

end FundOrder
