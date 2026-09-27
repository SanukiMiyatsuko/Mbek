import Mbek.Base
import Mbek.order

open T

inductive Dom0 where
| Zero
| One
| ω
deriving DecidableEq

def T.dom0 : T → Dom0
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.dom0 s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | _ + 1 => .ω
    | .One => .ω
    | .ω => .ω
  else T.dom0 s2

def T.fund0 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.dom0 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | l + 1 => T.iter (P l · Z) t
      | .One => T.mul (P s0 (T.fund0 s1 Z) Z) t
      | .ω => P s0 (T.fund0 s1 t) Z
    else P s0 s1 (T.fund0 s2 t)

def T.ValidArg0 (s t : T) : Prop :=
  match dom0 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t

inductive Dom1 where
| Zero
| One
| ω
| Ω (l : Nat)
deriving DecidableEq

def T.dom1 : T → Dom1
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.dom1 s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | l + 1 => .Ω l
    | .One => .ω
    | .ω => .ω
    | .Ω l =>
      if s0 ≤ l then .ω
      else .Ω l
  else T.dom1 s2

def T.fund1 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.dom1 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund1 s1 Z) Z) t
      | .ω => P s0 (T.fund1 s1 t) Z
      | .Ω l =>
        if s0 ≤ l then
          let F := fun x => P l (T.fund1 s1 x) Z
          P s0 (T.fund1 s1 (T.iter F t)) Z
        else P s0 (T.fund1 s1 t) Z
    else P s0 s1 (T.fund1 s2 t)

def T.ValidArg1 (s t : T) : Prop :=
  match dom1 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .Ω l => T.index_Prop (P (l + 1) Z Z) t

inductive Dom2 where
| Zero
| One
| ω
| M (l : Nat)
| Ω (l : Nat) (s1 : T)
deriving DecidableEq

def T.dom2 : T → Dom2
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.dom2 s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | l + 1 => .M l
    | .One => .ω
    | .ω => .ω
    | .M l =>
      if s0 ≤ l then
        if s0 < l then
          .ω
        else .Ω l s1
      else .M l
    | .Ω l l1 =>
      if P s0 s1 Z < P l l1 Z then
        .ω
      else .Ω l l1
  else T.dom2 s2

theorem T.dom2_P_unfold (s0 : Nat) (s1 s2 : T) :
    T.dom2 (P s0 s1 s2) =
      (if s2 = Z then
        (match T.dom2 s1 with
        | .Zero =>
          match s0 with
          | 0 => .One
          | k + 1 => .M k
        | .One => .ω
        | .ω => .ω
        | .M k =>
          if s0 ≤ k then
            if s0 < k then
              .ω
            else .Ω k s1
          else .M k
        | .Ω k l1' =>
          if P s0 s1 Z < P k l1' Z then
            .ω
          else .Ω k l1')
      else T.dom2 s2) := rfl

theorem T.dom2_Omega_size_lt :
    ∀ (x : T) (l : Nat) (l1 : T), T.dom2 x = Dom2.Ω l l1 → l1.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 h
    rw [T.dom2.eq_1] at h
    exact Dom2.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 h
    rw [T.dom2_P_unfold] at h
    split at h
    case isFalse hne =>
      exact Nat.lt_trans (ih2 l l1 h) (T.size_lt_size_P_right s0 s1 s2)
    case isTrue heq =>
      split at h
      case h_1 =>
        split at h
        · exact Dom2.noConfusion h
        · exact Dom2.noConfusion h
      case h_2 => exact Dom2.noConfusion h
      case h_3 => exact Dom2.noConfusion h
      case h_4 heqM =>
        split at h
        case isTrue hle =>
          split at h
          case isTrue hlt => exact Dom2.noConfusion h
          case isFalse hnlt =>
            injection h with hl hl1
            rw [← hl1]
            exact T.size_lt_size_P_left s0 s1 s2
        case isFalse hnle => exact Dom2.noConfusion h
      case h_5 heqO =>
        split at h
        case isTrue hlt => exact Dom2.noConfusion h
        case isFalse hnlt =>
          injection h with hl hl1
          have heqO' : s1.dom2 = Dom2.Ω l l1 := by rw [heqO, hl, hl1]
          exact Nat.lt_trans (ih1 l l1 heqO') (T.size_lt_size_P_left s0 s1 s2)

def T.fund2 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom2 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund2 s1 Z) Z) t
      | .ω => P s0 (T.fund2 s1 t) Z
      | .M l =>
        if s0 ≤ l then
          if s0 < l then
            let F := fun x => P l (T.fund2 s1 x) Z
            P s0 (T.fund2 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund2 s1 t) Z
      | .Ω l l1 =>
        if P s0 s1 Z < P l l1 Z then
          let F1 := fun x => P l (T.fund2 l1 x) Z
          if s0 < l then
            let F2 := fun x => P l (T.fund2 s1 x) Z
            let F := F1 ∘ F2
            P s0 (T.fund2 s1 (T.iter F t)) Z
          else
            let F2 := T.fund2 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2
            P s0 (T.fund2 s1 (T.iter F t)) Z
        else P s0 (T.fund2 s1 t) Z
    else P s0 s1 (T.fund2 s2 t)
termination_by s.size
decreasing_by
  all_goals
    first
    | exact T.size_lt_size_P_left s0 s1 s2
    | exact Nat.lt_trans (T.dom2_Omega_size_lt s1 l l1 _h1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P (l + 1) Z Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact T.size_lt_size_P_right s0 s1 s2

#eval! fund2 (parse! "0^0^2^1^2") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(2^1^2 + 2^1^2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^2^(1^2 + 1^2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^2^1^(2 + 2)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^(0^1 + 0^1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^0^(1^0^1 + 1^0^1)") (parse! "0 + 0 + 0")

#eval! fund2 (parse! "0^(0^1^0^1 + 0^1^0^1)") (parse! "0 + 0 + 0")

inductive Dom3 where
| Zero
| One
| ω
| M2 (l : Nat)
| M1 (l : Nat) (s1 : T)
| Ω (l : Nat) (s1 s2 : T)
deriving DecidableEq

def T.dom3 (s : T) : Dom3 :=
  match s with
  | Z => .Zero
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h2 : T.dom3 s1 with
      | .Zero =>
        match s0 with
        | 0 => .One
        | l + 1 => .M2 l
      | .One => .ω
      | .ω => .ω
      | .M2 l =>
        if s0 ≤ l then
          if s0 < l then
            .ω
          else .M1 l s1
        else .M2 l
      | .M1 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else .Ω l l1 s1
        else .M1 l l1
      | .Ω l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          .ω
        else .Ω l l1 l2
    else T.dom3 s2

theorem T.dom3_M1_size_lt :
    ∀ (x : T) (l : Nat) (l1 : T), T.dom3 x = Dom3.M1 l l1 → l1.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 h
    unfold T.dom3 at h
    exact Dom3.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 h
    unfold T.dom3 at h
    split at h
    case isFalse hne =>
      exact Nat.lt_trans (ih2 l l1 h) (T.size_lt_size_P_right s0 s1 s2)
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom3.noConfusion h
      case h_2 => exact Dom3.noConfusion h
      case h_3 => exact Dom3.noConfusion h
      case h_4 heqM2 =>
        split at h
        case isTrue hle =>
          split at h
          case isTrue => exact Dom3.noConfusion h
          case isFalse =>
            injection h with hl hl1
            rw [← hl1]
            exact T.size_lt_size_P_left s0 s1 s2
        case isFalse => exact Dom3.noConfusion h
      case h_5 heqM1 =>
        split at h
        case isTrue hlt =>
          split at h
          case isTrue => exact Dom3.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom3.noConfusion h
            case isFalse => exact Dom3.noConfusion h
        case isFalse hnlt =>
          injection h with hl hl1
          have heq' : s1.dom3 = Dom3.M1 l l1 := by rw [heqM1, hl, hl1]
          exact Nat.lt_trans (ih1 l l1 heq') (T.size_lt_size_P_left s0 s1 s2)
      case h_6 heqΩ =>
        split at h <;> exact Dom3.noConfusion h

theorem T.dom3_Omega_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 : T), T.dom3 x = Dom3.Ω l l1 l2 →
      l1.size < x.size ∧ l2.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 h
    unfold T.dom3 at h
    exact Dom3.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 h
    unfold T.dom3 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2⟩ := ih2 l l1 l2 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom3.noConfusion h
      case h_2 => exact Dom3.noConfusion h
      case h_3 => exact Dom3.noConfusion h
      case h_4 heqM2 =>
        split at h
        case isTrue hle => split at h <;> exact Dom3.noConfusion h
        case isFalse => exact Dom3.noConfusion h
      case h_5 heqM1 =>
        split at h
        case isTrue hlt =>
          split at h
          case isTrue => exact Dom3.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom3.noConfusion h
            case isFalse =>
              injection h with hl hl1 hl2
              have heqM1' : s1.dom3 = Dom3.M1 l l1 := by rw [heqM1, hl, hl1]
              have hb1 : l1.size < s1.size := T.dom3_M1_size_lt s1 l l1 heqM1'
              have hb2 : l2.size < (P s0 s1 s2).size := by
                rw [← hl2]; exact T.size_lt_size_P_left s0 s1 s2
              exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2), hb2⟩
        case isFalse hnlt => exact Dom3.noConfusion h
      case h_6 heqΩ =>
        split at h
        case isTrue => exact Dom3.noConfusion h
        case isFalse =>
          injection h with hl hl1 hl2
          have heqΩ' : s1.dom3 = Dom3.Ω l l1 l2 := by rw [heqΩ, hl, hl1, hl2]
          obtain ⟨hb1, hb2⟩ := ih1 l l1 l2 heqΩ'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2)⟩

def T.fund3 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom3 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund3 s1 Z) Z) t
      | .ω => P s0 (T.fund3 s1 t) Z
      | .M2 l =>
        if s0 ≤ l then
          if s0 < l then
            let F := fun x => P l (T.fund3 s1 x) Z
            P s0 (T.fund3 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund3 s1 t) Z
      | .M1 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          let F1 := fun x => P l (T.fund3 l1 x) Z
          if s0 < l then
            let F2 := fun x => P l (T.fund3 s1 x) Z
            let F := F1 ∘ F2
            P s0 (T.fund3 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F2 := T.fund3 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2
            P s0 (T.fund3 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund3 s1 t) Z
      | .Ω l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          let F1 := fun x => P l (T.fund3 l2 x) Z
          let F2 := fun x => P l (T.fund3 l1 x) Z
          if s0 < l then
            let F3 := fun x => P l (T.fund3 s1 x) Z
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund3 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F3 := T.fund3 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund3 s1 (T.iter F t)) Z
          else
            let F3 := T.fund3 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F3
            P s0 (T.fund3 s1 (T.iter F t)) Z
        else P s0 (T.fund3 s1 t) Z
    else P s0 s1 (T.fund3 s2 t)
termination_by s.size
decreasing_by
  all_goals
    first
    | exact T.size_lt_size_P_left s0 s1 s2
    | exact T.size_lt_size_P_right s0 s1 s2
    | exact Nat.lt_trans (T.dom3_M1_size_lt s1 l l1 _h1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom3_Omega_size_lt s1 l l1 l2 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom3_Omega_size_lt s1 l l1 l2 _h1).2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P (l + 1) Z Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l1 Z) s1) (T.size_lt_size_P_left s0 s1 s2)

#eval! fund3 (parse! "0^0^0^2^2^1^1^2^1^2") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^(0^(1 + 1) + 0^(1 + 1))") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^0^1^0^1^1") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^0^1^0^1^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^0^1^0^(1^1 + 1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^0^1^(0^1^1 + 0^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^0^(1^0^1^1 + 1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^1^(0^1^0^1^1 + 0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^1^(1^0^1^0^1^1 + 1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^0^(1^1^0^1^0^1^1 + 1^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^(0^0^1 + 0^0^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^0^(0^1 + 0^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^(0^(0^1+0^1)+0^(0^1+0^1))") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^1^1") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^1^(1+1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^1^0^1^(1^1+1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^1^0^(1^1^1+1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^1^(0^1^1^1+0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^1^(1^0^1^1^1+1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^0^(1^1^0^1^1^1+1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^1^(0^1^1^0^1^1^1+0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^1^(1^0^1^1^0^1^1^1+1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^1^(1^1^0^1^1^0^1^1^1+1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^0^(1^1^1^0^1^1^0^1^1^1+1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^1^(0^1^1^1^0^1^1^0^1^1^1+0^1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

#eval! fund3 (parse! "0^(1^0^1^1^1^0^1^1^0^1^1^1+1^0^1^1^1^0^1^1^0^1^1^1)") (parse! "0 + 0 + 0")

inductive Dom4 where
| Zero
| One
| ω
| M3 (l : Nat)
| M2 (l : Nat) (s1 : T)
| M1 (l : Nat) (s1 s2 : T)
| Ω (l : Nat) (s1 s2 s3 : T)
deriving DecidableEq

def T.dom4 (s : T) : Dom4 :=
  match s with
  | Z => .Zero
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.dom4 s1 with
      | .Zero =>
        match s0 with
        | 0 => .One
        | l + 1 => .M3 l
      | .One => .ω
      | .ω => .ω
      | .M3 l =>
        if s0 ≤ l then
          if s0 < l then
            .ω
          else .M2 l s1
        else .M3 l
      | .M2 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else .M1 l l1 s1
        else .M2 l l1
      | .M1 l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            .ω
          else .Ω l l1 l2 s1
        else .M1 l l1 l2
      | .Ω l l1 l2 l3 =>
        if P s0 s1 Z < P l l3 Z then
          .ω
        else .Ω l l1 l2 l3
    else T.dom4 s2

theorem T.dom4_M2_size_lt :
    ∀ (x : T) (l : Nat) (l1 : T), T.dom4 x = Dom4.M2 l l1 → l1.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 h
    unfold T.dom4 at h
    exact Dom4.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 h
    unfold T.dom4 at h
    split at h
    case isFalse hne =>
      exact Nat.lt_trans (ih2 l l1 h) (T.size_lt_size_P_right s0 s1 s2)
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom4.noConfusion h
      case h_2 => exact Dom4.noConfusion h
      case h_3 => exact Dom4.noConfusion h
      case h_4 heqM3 =>
        split at h
        case isTrue hle =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            injection h with hl hl1
            rw [← hl1]
            exact T.size_lt_size_P_left s0 s1 s2
        case isFalse => exact Dom4.noConfusion h
      case h_5 heqM2 =>
        split at h
        case isTrue hlt =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse => exact Dom4.noConfusion h
        case isFalse hnlt =>
          injection h with hl hl1
          have heq' : s1.dom4 = Dom4.M2 l l1 := by rw [heqM2, hl, hl1]
          exact Nat.lt_trans (ih1 l l1 heq') (T.size_lt_size_P_left s0 s1 s2)
      case h_6 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom4.noConfusion h
              case isFalse => exact Dom4.noConfusion h
        case isFalse h1 => exact Dom4.noConfusion h
      case h_7 heqΩ =>
        split at h <;> exact Dom4.noConfusion h

theorem T.dom4_M1_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 : T), T.dom4 x = Dom4.M1 l l1 l2 →
      l1.size < x.size ∧ l2.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 h
    unfold T.dom4 at h
    exact Dom4.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 h
    unfold T.dom4 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2⟩ := ih2 l l1 l2 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom4.noConfusion h
      case h_2 => exact Dom4.noConfusion h
      case h_3 => exact Dom4.noConfusion h
      case h_4 heqM3 =>
        split at h
        case isTrue hle => split at h <;> exact Dom4.noConfusion h
        case isFalse => exact Dom4.noConfusion h
      case h_5 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse =>
              injection h with hl hl1 hl2
              have heqM2' : s1.dom4 = Dom4.M2 l l1 := by rw [heqM2, hl, hl1]
              have hb1 : l1.size < s1.size := T.dom4_M2_size_lt s1 l l1 heqM2'
              have hb2 : l2.size < (P s0 s1 s2).size := by
                rw [← hl2]; exact T.size_lt_size_P_left s0 s1 s2
              exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2), hb2⟩
        case isFalse h1 => exact Dom4.noConfusion h
      case h_6 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom4.noConfusion h
              case isFalse => exact Dom4.noConfusion h
        case isFalse h1 =>
          injection h with hl hl1 hl2
          have heqM1' : s1.dom4 = Dom4.M1 l l1 l2 := by rw [heqM1, hl, hl1, hl2]
          obtain ⟨hb1, hb2⟩ := ih1 l l1 l2 heqM1'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2)⟩
      case h_7 heqΩ =>
        split at h <;> exact Dom4.noConfusion h

theorem T.dom4_Omega_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 l3 : T), T.dom4 x = Dom4.Ω l l1 l2 l3 →
      l1.size < x.size ∧ l2.size < x.size ∧ l3.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 l3 h
    unfold T.dom4 at h
    exact Dom4.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 l3 h
    unfold T.dom4 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2, hh3⟩ := ih2 l l1 l2 l3 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh3 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom4.noConfusion h
      case h_2 => exact Dom4.noConfusion h
      case h_3 => exact Dom4.noConfusion h
      case h_4 heqM3 =>
        split at h
        case isTrue hle => split at h <;> exact Dom4.noConfusion h
        case isFalse => exact Dom4.noConfusion h
      case h_5 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse => exact Dom4.noConfusion h
        case isFalse h1 => exact Dom4.noConfusion h
      case h_6 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom4.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom4.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom4.noConfusion h
              case isFalse =>
                injection h with hl hl1 hl2 hl3
                have heqM1' : s1.dom4 = Dom4.M1 l l1 l2 := by rw [heqM1, hl, hl1, hl2]
                obtain ⟨hb1, hb2⟩ := T.dom4_M1_size_lt s1 l l1 l2 heqM1'
                have hb3 : l3.size < (P s0 s1 s2).size := by
                  rw [← hl3]; exact T.size_lt_size_P_left s0 s1 s2
                exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                      Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2), hb3⟩
        case isFalse h1 => exact Dom4.noConfusion h
      case h_7 heqΩ =>
        split at h
        case isTrue => exact Dom4.noConfusion h
        case isFalse =>
          injection h with hl hl1 hl2 hl3
          have heqΩ' : s1.dom4 = Dom4.Ω l l1 l2 l3 := by rw [heqΩ, hl, hl1, hl2, hl3]
          obtain ⟨hb1, hb2, hb3⟩ := ih1 l l1 l2 l3 heqΩ'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb3 (T.size_lt_size_P_left s0 s1 s2)⟩

def T.fund4 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom4 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund4 s1 Z) Z) t
      | .ω => P s0 (T.fund4 s1 t) Z
      | .M3 l =>
        if s0 ≤ l then
          if s0 < l then
            let F := fun x => P l (T.fund4 s1 x) Z
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund4 s1 t) Z
      | .M2 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          let F1 := fun x => P l (T.fund4 l1 x) Z
          if s0 < l then
            let F2 := fun x => P l (T.fund4 s1 x) Z
            let F := F1 ∘ F2
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F2 := T.fund4 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund4 s1 t) Z
      | .M1 l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          let F1 := fun x => P l (T.fund4 l2 x) Z
          let F2 := fun x => P l (T.fund4 l1 x) Z
          if s0 < l then
            let F3 := fun x => P l (T.fund4 s1 x) Z
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F3 := T.fund4 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            let F3 := T.fund4 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F3
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund4 s1 t) Z
      | .Ω l l1 l2 l3 =>
        if P s0 s1 Z < P l l3 Z then
          let F1 := fun x => P l (T.fund4 l3 x) Z
          let F2 := fun x => P l (T.fund4 l2 x) Z
          let F3 := fun x => P l (T.fund4 l1 x) Z
          if s0 < l then
            let F4 := fun x => P l (T.fund4 s1 x) Z
            let F := F1 ∘ F2 ∘ F3 ∘ F4
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F4 := T.fund4 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3 ∘ F4
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            let F4 := T.fund4 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F2 ∘ F4
            P s0 (T.fund4 s1 (T.iter F t)) Z
          else
            let F4 := T.fund4 (T.drop (P l l2 Z) s1)
            let F := F1 ∘ F4
            P s0 (T.fund4 s1 (T.iter F t)) Z
        else P s0 (T.fund4 s1 t) Z
    else P s0 s1 (T.fund4 s2 t)
termination_by s.size
decreasing_by
  all_goals
    first
    | exact T.size_lt_size_P_left s0 s1 s2
    | exact T.size_lt_size_P_right s0 s1 s2
    | exact Nat.lt_trans (T.dom4_M2_size_lt s1 l l1 _h1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom4_M1_size_lt s1 l l1 l2 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom4_M1_size_lt s1 l l1 l2 _h1).2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom4_Omega_size_lt s1 l l1 l2 l3 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom4_Omega_size_lt s1 l l1 l2 l3 _h1).2.1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom4_Omega_size_lt s1 l l1 l2 l3 _h1).2.2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P (l + 1) Z Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l1 Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l2 Z) s1) (T.size_lt_size_P_left s0 s1 s2)

#eval! fund4 (parse! "0^2^2^1^1^1^2^1^1^2") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^0^1^0^1^1") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^0^1^0^1^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^0^1^0^(1^1 + 1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^0^1^(0^1^1 + 0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^0^(1^0^1^1 + 1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^1^(0^1^0^1^1 + 0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^0^(1^0^1^0^1^1 + 1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^1^(0^1^0^1^0^1^1 + 0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^1^(1^0^1^0^1^0^1^1 + 1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^(1^1^0^1^0^1^0^1^1 + 1^1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^(0^1^1^0^1^0^1^0^1^1 + 0^1^1^0^1^0^1^0^1^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^0^0^1^0^1") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^0^0^1^0^(1 + 1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^0^0^1^(0^1 + 0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^0^0^(1^0^1 + 1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^0^(0^1^0^1 + 0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^1^(0^0^1^0^1 + 0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^0^(1^0^0^1^0^1 + 1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^0^(0^1^0^0^1^0^1 + 0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^1^(0^0^1^0^0^1^0^1 + 0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^1^(1^0^0^1^0^0^1^0^1 + 1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^0^(1^1^0^0^1^0^0^1^0^1 + 1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^0^(0^1^1^0^0^1^0^0^1^0^1 + 0^1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

#eval! fund4 (parse! "0^(0^0^1^1^0^0^1^0^0^1^0^1 + 0^0^1^1^0^0^1^0^0^1^0^1)") (parse! "0 + 0 + 0")

inductive Dom5 where
| Zero
| One
| ω
| M4 (l : Nat)
| M3 (l : Nat) (s1 : T)
| M2 (l : Nat) (s1 s2 : T)
| M1 (l : Nat) (s1 s2 s3 : T)
| Ω (l : Nat) (s1 s2 s3 s4 : T)
deriving DecidableEq

def T.dom5 (s : T) : Dom5 :=
  match s with
  | Z => .Zero
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.dom5 s1 with
      | .Zero =>
        match s0 with
        | 0 => .One
        | l + 1 => .M4 l
      | .One => .ω
      | .ω => .ω
      | .M4 l =>
        if s0 ≤ l then
          if s0 < l then
            .ω
          else .M3 l s1
        else .M4 l
      | .M3 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else .M2 l l1 s1
        else .M3 l l1
      | .M2 l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            .ω
          else .M1 l l1 l2 s1
        else .M2 l l1 l2
      | .M1 l l1 l2 l3 =>
        if P s0 s1 Z < P l l3 Z then
          if s0 < l then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            .ω
          else if P s0 s1 Z < P l (T.takeAt l3 (P l l2 Z)) Z then
            .ω
          else .Ω l l1 l2 l3 s1
        else .M1 l l1 l2 l3
      | .Ω l l1 l2 l3 l4 =>
        if P s0 s1 Z < P l l4 Z then
          .ω
        else .Ω l l1 l2 l3 l4
    else T.dom5 s2

theorem T.dom5_M3_size_lt :
    ∀ (x : T) (l : Nat) (l1 : T), T.dom5 x = Dom5.M3 l l1 → l1.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 h
    unfold T.dom5 at h
    exact Dom5.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 h
    unfold T.dom5 at h
    split at h
    case isFalse hne =>
      exact Nat.lt_trans (ih2 l l1 h) (T.size_lt_size_P_right s0 s1 s2)
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom5.noConfusion h
      case h_2 => exact Dom5.noConfusion h
      case h_3 => exact Dom5.noConfusion h
      case h_4 heqM4 =>
        split at h
        case isTrue hle =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            injection h with hl hl1
            rw [← hl1]
            exact T.size_lt_size_P_left s0 s1 s2
        case isFalse => exact Dom5.noConfusion h
      case h_5 heqM3 =>
        split at h
        case isTrue hlt =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse => exact Dom5.noConfusion h
        case isFalse hnlt =>
          injection h with hl hl1
          have heq' : s1.dom5 = Dom5.M3 l l1 := by rw [heqM3, hl, hl1]
          exact Nat.lt_trans (ih1 l l1 heq') (T.size_lt_size_P_left s0 s1 s2)
      case h_6 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_7 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse =>
                split at h
                case isTrue => exact Dom5.noConfusion h
                case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_8 heqΩ =>
        split at h <;> exact Dom5.noConfusion h

theorem T.dom5_M2_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 : T), T.dom5 x = Dom5.M2 l l1 l2 →
      l1.size < x.size ∧ l2.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 h
    unfold T.dom5 at h
    exact Dom5.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 h
    unfold T.dom5 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2⟩ := ih2 l l1 l2 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom5.noConfusion h
      case h_2 => exact Dom5.noConfusion h
      case h_3 => exact Dom5.noConfusion h
      case h_4 heqM4 =>
        split at h
        case isTrue hle => split at h <;> exact Dom5.noConfusion h
        case isFalse => exact Dom5.noConfusion h
      case h_5 heqM3 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              injection h with hl hl1 hl2
              have heqM3' : s1.dom5 = Dom5.M3 l l1 := by rw [heqM3, hl, hl1]
              have hb1 : l1.size < s1.size := T.dom5_M3_size_lt s1 l l1 heqM3'
              have hb2 : l2.size < (P s0 s1 s2).size := by
                rw [← hl2]; exact T.size_lt_size_P_left s0 s1 s2
              exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2), hb2⟩
        case isFalse h1 => exact Dom5.noConfusion h
      case h_6 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse => exact Dom5.noConfusion h
        case isFalse h1 =>
          injection h with hl hl1 hl2
          have heqM2' : s1.dom5 = Dom5.M2 l l1 l2 := by rw [heqM2, hl, hl1, hl2]
          obtain ⟨hb1, hb2⟩ := ih1 l l1 l2 heqM2'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2)⟩
      case h_7 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse =>
                split at h
                case isTrue => exact Dom5.noConfusion h
                case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_8 heqΩ =>
        split at h <;> exact Dom5.noConfusion h

theorem T.dom5_M1_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 l3 : T), T.dom5 x = Dom5.M1 l l1 l2 l3 →
      l1.size < x.size ∧ l2.size < x.size ∧ l3.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 l3 h
    unfold T.dom5 at h
    exact Dom5.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 l3 h
    unfold T.dom5 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2, hh3⟩ := ih2 l l1 l2 l3 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh3 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom5.noConfusion h
      case h_2 => exact Dom5.noConfusion h
      case h_3 => exact Dom5.noConfusion h
      case h_4 heqM4 =>
        split at h
        case isTrue hle => split at h <;> exact Dom5.noConfusion h
        case isFalse => exact Dom5.noConfusion h
      case h_5 heqM3 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_6 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse =>
                injection h with hl hl1 hl2 hl3
                have heqM2' : s1.dom5 = Dom5.M2 l l1 l2 := by rw [heqM2, hl, hl1, hl2]
                obtain ⟨hb1, hb2⟩ := T.dom5_M2_size_lt s1 l l1 l2 heqM2'
                have hb3 : l3.size < (P s0 s1 s2).size := by
                  rw [← hl3]; exact T.size_lt_size_P_left s0 s1 s2
                exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                      Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2), hb3⟩
        case isFalse h1 => exact Dom5.noConfusion h
      case h_7 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse =>
                split at h
                case isTrue => exact Dom5.noConfusion h
                case isFalse => exact Dom5.noConfusion h
        case isFalse h1 =>
          injection h with hl hl1 hl2 hl3
          have heqM1' : s1.dom5 = Dom5.M1 l l1 l2 l3 := by rw [heqM1, hl, hl1, hl2, hl3]
          obtain ⟨hb1, hb2, hb3⟩ := ih1 l l1 l2 l3 heqM1'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb3 (T.size_lt_size_P_left s0 s1 s2)⟩
      case h_8 heqΩ =>
        split at h <;> exact Dom5.noConfusion h

theorem T.dom5_Omega_size_lt :
    ∀ (x : T) (l : Nat) (l1 l2 l3 l4 : T), T.dom5 x = Dom5.Ω l l1 l2 l3 l4 →
      l1.size < x.size ∧ l2.size < x.size ∧ l3.size < x.size ∧ l4.size < x.size := by
  intro x
  induction x with
  | Z =>
    intro l l1 l2 l3 l4 h
    unfold T.dom5 at h
    exact Dom5.noConfusion h
  | P s0 s1 s2 ih1 ih2 =>
    intro l l1 l2 l3 l4 h
    unfold T.dom5 at h
    split at h
    case isFalse hne =>
      obtain ⟨hh1, hh2, hh3, hh4⟩ := ih2 l l1 l2 l3 l4 h
      exact ⟨Nat.lt_trans hh1 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh2 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh3 (T.size_lt_size_P_right s0 s1 s2),
            Nat.lt_trans hh4 (T.size_lt_size_P_right s0 s1 s2)⟩
    case isTrue heq =>
      split at h
      case h_1 => split at h <;> exact Dom5.noConfusion h
      case h_2 => exact Dom5.noConfusion h
      case h_3 => exact Dom5.noConfusion h
      case h_4 heqM4 =>
        split at h
        case isTrue hle => split at h <;> exact Dom5.noConfusion h
        case isFalse => exact Dom5.noConfusion h
      case h_5 heqM3 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_6 heqM2 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse => exact Dom5.noConfusion h
        case isFalse h1 => exact Dom5.noConfusion h
      case h_7 heqM1 =>
        split at h
        case isTrue h1 =>
          split at h
          case isTrue => exact Dom5.noConfusion h
          case isFalse =>
            split at h
            case isTrue => exact Dom5.noConfusion h
            case isFalse =>
              split at h
              case isTrue => exact Dom5.noConfusion h
              case isFalse =>
                split at h
                case isTrue => exact Dom5.noConfusion h
                case isFalse =>
                  injection h with hl hl1 hl2 hl3 hl4
                  have heqM1' : s1.dom5 = Dom5.M1 l l1 l2 l3 := by
                    rw [heqM1, hl, hl1, hl2, hl3]
                  obtain ⟨hb1, hb2, hb3⟩ := T.dom5_M1_size_lt s1 l l1 l2 l3 heqM1'
                  have hb4 : l4.size < (P s0 s1 s2).size := by
                    rw [← hl4]; exact T.size_lt_size_P_left s0 s1 s2
                  exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                        Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2),
                        Nat.lt_trans hb3 (T.size_lt_size_P_left s0 s1 s2), hb4⟩
        case isFalse h1 => exact Dom5.noConfusion h
      case h_8 heqΩ =>
        split at h
        case isTrue => exact Dom5.noConfusion h
        case isFalse =>
          injection h with hl hl1 hl2 hl3 hl4
          have heqΩ' : s1.dom5 = Dom5.Ω l l1 l2 l3 l4 := by
            rw [heqΩ, hl, hl1, hl2, hl3, hl4]
          obtain ⟨hb1, hb2, hb3, hb4⟩ := ih1 l l1 l2 l3 l4 heqΩ'
          exact ⟨Nat.lt_trans hb1 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb2 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb3 (T.size_lt_size_P_left s0 s1 s2),
                Nat.lt_trans hb4 (T.size_lt_size_P_left s0 s1 s2)⟩

def T.fund5 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom5 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund5 s1 Z) Z) t
      | .ω => P s0 (T.fund5 s1 t) Z
      | .M4 l =>
        if s0 ≤ l then
          if s0 < l then
            let F := fun x => P l (T.fund5 s1 x) Z
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund5 s1 t) Z
      | .M3 l l1 =>
        if P s0 s1 Z < P l l1 Z then
          let F1 := fun x => P l (T.fund5 l1 x) Z
          if s0 < l then
            let F2 := fun x => P l (T.fund5 s1 x) Z
            let F := F1 ∘ F2
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F2 := T.fund5 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund5 s1 t) Z
      | .M2 l l1 l2 =>
        if P s0 s1 Z < P l l2 Z then
          let F1 := fun x => P l (T.fund5 l2 x) Z
          let F2 := fun x => P l (T.fund5 l1 x) Z
          if s0 < l then
            let F3 := fun x => P l (T.fund5 s1 x) Z
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F3 := T.fund5 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            let F3 := T.fund5 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F3
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund5 s1 t) Z
      | .M1 l l1 l2 l3 =>
        if P s0 s1 Z < P l l3 Z then
          let F1 := fun x => P l (T.fund5 l3 x) Z
          let F2 := fun x => P l (T.fund5 l2 x) Z
          let F3 := fun x => P l (T.fund5 l1 x) Z
          if s0 < l then
            let F4 := fun x => P l (T.fund5 s1 x) Z
            let F := F1 ∘ F2 ∘ F3 ∘ F4
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F4 := T.fund5 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3 ∘ F4
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            let F4 := T.fund5 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F2 ∘ F4
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l3 (P l l2 Z)) Z then
            let F4 := T.fund5 (T.drop (P l l2 Z) s1)
            let F := F1 ∘ F4
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else t
        else P s0 (T.fund5 s1 t) Z
      | .Ω l l1 l2 l3 l4 =>
        if P s0 s1 Z < P l l4 Z then
          let F1 := fun x => P l (T.fund5 l4 x) Z
          let F2 := fun x => P l (T.fund5 l3 x) Z
          let F3 := fun x => P l (T.fund5 l2 x) Z
          let F4 := fun x => P l (T.fund5 l1 x) Z
          if s0 < l then
            let F5 := fun x => P l (T.fund5 s1 x) Z
            let F := F1 ∘ F2 ∘ F3 ∘ F4 ∘ F5
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l1 (P (l + 1) Z Z)) Z then
            let F5 := T.fund5 (T.drop (P (l + 1) Z Z) s1)
            let F := F1 ∘ F2 ∘ F3 ∘ F4 ∘ F5
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l2 (P l l1 Z)) Z then
            let F5 := T.fund5 (T.drop (P l l1 Z) s1)
            let F := F1 ∘ F2 ∘ F3 ∘ F5
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else if P s0 s1 Z < P l (T.takeAt l3 (P l l2 Z)) Z then
            let F5 := T.fund5 (T.drop (P l l2 Z) s1)
            let F := F1 ∘ F2 ∘ F5
            P s0 (T.fund5 s1 (T.iter F t)) Z
          else
            let F5 := T.fund5 (T.drop (P l l3 Z) s1)
            let F := F1 ∘ F5
            P s0 (T.fund5 s1 (T.iter F t)) Z
        else P s0 (T.fund5 s1 t) Z
    else P s0 s1 (T.fund5 s2 t)
termination_by s.size
decreasing_by
  all_goals
    first
    | exact T.size_lt_size_P_left s0 s1 s2
    | exact T.size_lt_size_P_right s0 s1 s2
    | exact Nat.lt_trans (T.dom5_M3_size_lt s1 l l1 _h1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_M2_size_lt s1 l l1 l2 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_M2_size_lt s1 l l1 l2 _h1).2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_M1_size_lt s1 l l1 l2 l3 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_M1_size_lt s1 l l1 l2 l3 _h1).2.1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_M1_size_lt s1 l l1 l2 l3 _h1).2.2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_Omega_size_lt s1 l l1 l2 l3 l4 _h1).1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_Omega_size_lt s1 l l1 l2 l3 l4 _h1).2.1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_Omega_size_lt s1 l l1 l2 l3 l4 _h1).2.2.1 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_trans (T.dom5_Omega_size_lt s1 l l1 l2 l3 l4 _h1).2.2.2 (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P (l + 1) Z Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l1 Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l2 Z) s1) (T.size_lt_size_P_left s0 s1 s2)
    | exact Nat.lt_of_le_of_lt (T.drop_size_le (P l l3 Z) s1) (T.size_lt_size_P_left s0 s1 s2)
