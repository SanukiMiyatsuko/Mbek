import Mbek.mbek

open T

inductive DomM where
| Zero
| One
| ω
| M (l : Nat) (lx : List T)
| Ω (l : Nat) (lx : List T)
deriving DecidableEq

def DomM.next (rank l : Nat) (lx : List T) (s : T) : DomM :=
  let lx' := lx ++ [s]
  if lx'.length + 1 = rank then
    .Ω l lx'
  else
    .M l lx'

def T.lastTerm? : List T → Option T
| [] => none
| a :: ax =>
  match ax with
  | [] => some a
  | _ :: _ => T.lastTerm? ax

def T.cutBase (l : Nat) : Option T → T
| none => P (l + 1) Z Z
| some a => P l a Z

def T.firstCutAux (l : Nat) (s : T) : Option T → List T → Option (T × List T)
| _, [] => none
| prev, a :: ax =>
  let b := T.cutBase l prev
  if s < P l (T.takeAt a b) Z then
    some (b, a :: ax)
  else
    T.firstCutAux l s (some a) ax

def T.firstCut (l : Nat) (s : T) (lx : List T) : Option (T × List T) :=
  T.firstCutAux l s none lx

def T.firstCutBeforeLastAux (l : Nat) (s : T) : Option T → List T → Option (T × List T)
| _, [] => none
| prev, a :: ax =>
  match ax with
  | [] => none
  | _ :: _ =>
    let b := T.cutBase l prev
    if s < P l (T.takeAt a b) Z then
      some (b, a :: ax)
    else
      T.firstCutBeforeLastAux l s (some a) ax


def T.firstCutBeforeLast (l : Nat) (s : T) (lx : List T) : Option (T × List T) :=
  T.firstCutBeforeLastAux l s none lx

def T.lastCutBase (l : Nat) : List T → T
| [] => P (l + 1) Z Z
| a :: ax =>
  match ax with
  | [] => P (l + 1) Z Z
  | [_] => P l a Z
  | _ :: _ :: _ => T.lastCutBase l ax

def T.domM (rank : Nat) : T → DomM
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.domM rank s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | l + 1 =>
        if rank = 0 then
          .ω
        else if rank = 1 then
          .Ω l []
        else
          .M l []
    | .One => .ω
    | .ω => .ω
    | .M l lx =>
      match lx with
      | [] =>
        if s0 ≤ l then
          if s0 < l then
            .ω
          else
            DomM.next rank l [] s1
        else
          .M l []
      | _ :: _ =>
        match T.lastTerm? lx with
        | none => .M l lx
        | some a =>
          let s' := P s0 s1 Z
          if s' < P l a Z then
            if s0 < l then
              .ω
            else
              match T.firstCut l s' lx with
              | some _ => .ω
              | none => DomM.next rank l lx s1
          else
            .M l lx
    | .Ω l lx =>
      match lx with
      | [] =>
        if s0 ≤ l then
          .ω
        else
          .Ω l []
      | _ :: _ =>
        match T.lastTerm? lx with
        | none => .Ω l lx
        | some a =>
          if P s0 s1 Z < P l a Z then
            .ω
          else
            .Ω l lx
  else
    T.domM rank s2

def T.fundMCore (rank : Nat) : Nat → T → T → T
| 0, _, _ => Z
| fuel + 1, s, t =>
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.domM rank s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | l + 1 =>
          if rank = 0 then
            T.iter (P l · Z) t
          else
            t
      | .One =>
        T.mul (P s0 (T.fundMCore rank fuel s1 Z) Z) t
      | .ω =>
        P s0 (T.fundMCore rank fuel s1 t) Z
      | .M l lx =>
        match lx with
        | [] =>
          if s0 ≤ l then
            if s0 < l then
              let F := fun u => P l (T.fundMCore rank fuel s1 u) Z
              P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
            else
              t
          else
            P s0 (T.fundMCore rank fuel s1 t) Z
        | _ :: _ =>
          match T.lastTerm? lx with
          | none => P s0 (T.fundMCore rank fuel s1 t) Z
          | some a =>
            let s' := P s0 s1 Z
            if s' < P l a Z then
              let apply := fun (ax : List T) (u : T) =>
                ax.foldl (fun v b => P l (T.fundMCore rank fuel b v) Z) u
              if s0 < l then
                let F := fun u =>
                  apply lx (P l (T.fundMCore rank fuel s1 u) Z)
                P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
              else
                match T.firstCut l s' lx with
                | some (b, ax) =>
                  let F := fun u =>
                    apply ax (T.fundMCore rank fuel (T.drop b s1) u)
                  P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
                | none => t
            else
              P s0 (T.fundMCore rank fuel s1 t) Z
      | .Ω l lx =>
        match lx with
        | [] =>
          if s0 ≤ l then
            let F := fun u => P l (T.fundMCore rank fuel s1 u) Z
            P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
          else
            P s0 (T.fundMCore rank fuel s1 t) Z
        | _ :: _ =>
          match T.lastTerm? lx with
          | none => P s0 (T.fundMCore rank fuel s1 t) Z
          | some a =>
            let s' := P s0 s1 Z
            if s' < P l a Z then
              let apply := fun (ax : List T) (u : T) =>
                ax.foldl (fun v b => P l (T.fundMCore rank fuel b v) Z) u
              if s0 < l then
                let F := fun u =>
                  apply lx (P l (T.fundMCore rank fuel s1 u) Z)
                P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
              else
                match T.firstCutBeforeLast l s' lx with
                | some (b, ax) =>
                  let F := fun u =>
                    apply ax (T.fundMCore rank fuel (T.drop b s1) u)
                  P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
                | none =>
                  let b := T.lastCutBase l lx
                  let F := fun u =>
                    P l (T.fundMCore rank fuel a
                      (T.fundMCore rank fuel (T.drop b s1) u)) Z
                  P s0 (T.fundMCore rank fuel s1 (T.iter F t)) Z
            else
              P s0 (T.fundMCore rank fuel s1 t) Z
    else
      P s0 s1 (T.fundMCore rank fuel s2 t)

def T.fundM (rank : Nat) (s t : T) : T :=
  T.fundMCore rank (s.size + 1) s t
