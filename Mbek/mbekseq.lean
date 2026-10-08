def List.repeat {A : Type u} (n : Nat) : List A → List A :=
  fun xs => (List.replicate n xs).flatten

def List.lastIdx {A : Type u}
    (xs : List A) (h : xs ≠ []) : Nat :=
  match xs with
  | [] => absurd rfl h
  | _ :: as => as.length

mutual
def parent_cand (list : List Nat) : Nat → List Nat
  | 0 => List.range list.length
  | m + 1 =>
      match parent list m with
      | none => []
      | some p =>
          (List.range p).filter
            (fun i => list.drop i < list.drop p)

def parent (list : List Nat) (m : Nat) : Option Nat :=
  (parent_cand list m).max?
end

def uncle (list : List Nat) (x m : Nat) : Option Nat :=
  (parent_cand list m).filter (fun i => x < i) |>.min?

def relatives (list : List Nat) (x n : Nat) : Option Nat :=
  match n with
  | 0 =>
      match x with
      | 0 => none
      | x' + 1 => x'
  | 1 => x
  | n' + 1 =>
      match uncle list x n' with
      | none => none
      | some u => relatives list u n'

theorem parent_mem_parent_cand
    (list : List Nat) (m p : Nat)
    (hp : parent list m = some p) :
    p ∈ parent_cand list m := by
  apply List.max?_mem
  simpa only [parent] using hp

theorem parent_step
    (list : List Nat) (m p : Nat)
    (hp : parent list (m + 1) = some p) :
    ∃ q, parent list m = some q ∧ p < q := by
  have hmem : p ∈ parent_cand list (m + 1) :=
    parent_mem_parent_cand list (m + 1) p hp
  cases hprev : parent list m with
  | none =>
      simp [parent_cand, hprev] at hmem
  | some q =>
      have hfilter :
          p ∈ (List.range q).filter
            (fun i => list.drop i < list.drop q) := by
        simpa only [parent_cand, hprev] using hmem
      have hrange : p ∈ List.range q :=
        (List.mem_filter.mp hfilter).1
      have hlt : p < q :=
        List.mem_range.mp hrange
      exact ⟨q, rfl, hlt⟩

theorem parent_exists_lt
    (list : List Nat) :
    ∀ (m n p : Nat),
      n < m →
      parent list m = some p →
      ∃ q, parent list n = some q ∧ p < q := by
  intro m
  induction m with
  | zero =>
      intro n p hnm _
      exact (Nat.not_lt_zero n hnm).elim
  | succ m ih =>
      intro n p hnm hp
      obtain ⟨q, hq, hpq⟩ :=
        parent_step list m p hp
      cases Nat.lt_succ_iff_lt_or_eq.mp hnm with
      | inl hlt =>
          obtain ⟨r, hr, hqr⟩ :=
            ih n q hlt hq
          exact ⟨r, hr, Nat.lt_trans hpq hqr⟩
      | inr heq =>
          subst n
          exact ⟨q, hq, hpq⟩

theorem parent_ne_none_of_lt
    (list : List Nat) (m n : Nat)
    (hnm : n < m)
    (hm : parent list m ≠ none) :
    parent list n ≠ none := by
  cases hp : parent list m with
  | none =>
      exact (hm hp).elim
  | some p =>
      obtain ⟨q, hq, _⟩ :=
        parent_exists_lt list m n p hnm hp
      intro hn
      rw [hq] at hn
      cases hn

theorem parent_lt_of_gt
    (list : List Nat) (m n p q : Nat)
    (hnm : n < m)
    (hm : parent list m = some p)
    (hn : parent list n = some q) :
    p < q := by
  obtain ⟨q', hq', hpq'⟩ :=
    parent_exists_lt list m n p hnm hm
  have heq : q' = q :=
    Option.some.inj (hq'.symm.trans hn)
  simpa [heq] using hpq'

theorem parent_lt_length
    (list : List Nat) :
    ∀ m p, parent list m = some p → p < list.length := by
  intro m
  induction m with
  | zero =>
      intro p hp
      have hmem : p ∈ List.range list.length := by
        simpa only [parent_cand] using
          parent_mem_parent_cand list 0 p hp
      exact List.mem_range.mp hmem
  | succ m ih =>
      intro p hp
      obtain ⟨q, hq, hpq⟩ :=
        parent_step list m p hp
      exact Nat.lt_trans hpq (ih q hq)

theorem uncle_mem_parent_cand
    (list : List Nat) (x m u : Nat)
    (hu : uncle list x m = some u) :
    u ∈ parent_cand list m := by
  have hmem :
      u ∈ (parent_cand list m).filter
        (fun i => x < i) := by
    apply List.min?_mem
    simpa only [uncle] using hu
  exact (List.mem_filter.mp hmem).1

theorem uncle_ne_none_of_lt_parent
    (list : List Nat) (x m p : Nat)
    (hp : parent list m = some p)
    (hx : x < p) :
    uncle list x m ≠ none := by
  have hp_mem :
      p ∈ parent_cand list m :=
    parent_mem_parent_cand list m p hp
  have hp_filter :
      p ∈ (parent_cand list m).filter
        (fun i => x < i) := by
    simp [List.mem_filter, hp_mem, hx]
  intro hnone
  have hnone' :
      ((parent_cand list m).filter
        (fun i => x < i)).min? = none := by
    simpa only [uncle] using hnone
  have hnil :
      (parent_cand list m).filter
        (fun i => x < i) = [] :=
    List.min?_eq_none_iff.mp hnone'
  rw [hnil] at hp_filter
  exact List.not_mem_nil hp_filter

theorem uncle_ne_none_of_parent
    (list : List Nat) (m n p : Nat)
    (hnm : n < m)
    (hm : parent list m = some p) :
    uncle list p n ≠ none := by
  obtain ⟨q, hq, hpq⟩ :=
    parent_exists_lt list m n p hnm hm
  exact
    uncle_ne_none_of_lt_parent list p n q hq hpq

theorem relatives_ne_none_of_lt_parent
    (list : List Nat) :
    ∀ (k x p : Nat),
      parent list k = some p →
      x < p →
      relatives list x (k + 1) ≠ none := by
  intro k
  induction k with
  | zero =>
      intro x p hp hx
      simp [relatives]
  | succ k ih =>
      intro x p hp hx
      have huncle :
          uncle list x (k + 1) ≠ none :=
        uncle_ne_none_of_lt_parent
          list x (k + 1) p hp hx
      cases hu : uncle list x (k + 1) with
      | none =>
          exact (huncle hu).elim
      | some u =>
          have hmem :
              u ∈ parent_cand list (k + 1) :=
            uncle_mem_parent_cand
              list x (k + 1) u hu
          cases hprev : parent list k with
          | none =>
              have hnil :
                  parent_cand list (k + 1) = [] := by
                simp [parent_cand, hprev]
              simp [hnil] at hmem
          | some q =>
              have hfilter :
                  u ∈ (List.range q).filter
                    (fun i => list.drop i < list.drop q) := by
                simpa only [parent_cand, hprev] using hmem
              have hrange : u ∈ List.range q :=
                (List.mem_filter.mp hfilter).1
              have huq : u < q :=
                List.mem_range.mp hrange
              have hrec :
                  relatives list u (k + 1) ≠ none :=
                ih u q hprev huq
              change
                (match uncle list x (k + 1) with
                | none => (none : Option Nat)
                | some v => relatives list v (k + 1)) ≠ none
              simpa only [hu] using hrec


theorem relatives_ne_none_of_parent
    (list : List Nat) (m k p : Nat)
    (hkm : k < m)
    (hm : parent list m = some p) :
    relatives list p (k + 1) ≠ none := by
  obtain ⟨q, hq, hpq⟩ := parent_exists_lt list m k p hkm hm
  exact relatives_ne_none_of_lt_parent list k p q hq hpq

theorem relatives_ne_none_final
  (list : List Nat) (M p : Nat)
  (hM : 0 < M)
  (hp : parent list M = some p) :
  relatives list p M ≠ none := by
  cases M with
  | zero => exact (Nat.not_lt_zero 0 hM).elim
  | succ k =>
    exact relatives_ne_none_of_parent
      list (k + 1) k p
      (Nat.lt_succ_self k) hp

private def true_parent_scan
  (list : List Nat)
  (pm : Nat)
  (plist : Array Nat) :
  List Nat → Option (Option Nat)
| [] => none
| k :: ks =>
  if hk : k < plist.size then
    if hkPrev : k - 1 < plist.size then
      let pk := plist[k]'hk
      let pkPrev := plist[k - 1]'hkPrev
      if list.drop pm < list.extract pk pkPrev then
        some (relatives list pm (k + 1))
      else true_parent_scan list pm plist ks
    else true_parent_scan list pm plist ks
  else true_parent_scan list pm plist ks

private def true_parent_go
  (M : Nat)
  (list : List Nat)
  (last : Nat)
  (m : Nat)
  (plist : Array Nat) :
  Nat → Option Nat
| 0 =>
  if hM : M < plist.size then
    relatives list (plist[M]'hM) M
  else none
| fuel + 1 =>
  match parent list m with
  | none => none
  | some pm =>
    if hpm : pm < list.length then
      let a := list[pm]'hpm
      let plist' := plist.push pm
      if a < last - 1 then
        some pm
      else
        let ks := (List.range (min (M - 1) m)).drop 1
        match true_parent_scan list pm plist' ks with
        | some result => result
        | none =>
          true_parent_go M list last (m + 1) plist' fuel
    else none

def true_parent (M : Nat) (list : List Nat) : Option Nat :=
  match list.getLast? with
  | none => none
  | some last =>
      true_parent_go M list last 0 #[] (M + 1)

def expand (M : Nat) (list : List Nat) (n : Nat) : List Nat :=
  let init := list.dropLast
  match list.getLast? with
  | some (last' + 1) =>
    let base := init ++ [last']
    match true_parent M list with
    | none => List.repeat (n + 1) base
    | some i =>
      let step := base.drop (i + 1)
      base ++ List.repeat n step
  | _ => init
