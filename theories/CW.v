(*** Computational W types ***)

(**

  The idea is to provide an alternative to W types that actually provides the
  expected computation rules. Currently, W types are limited in that they only
  support those computation rules propositionally and actually require function
  extensionality.

  This experimental proposal seems to improve on this front and is actually
  able to encode regular W types, so it is at least strictly better, although
  slightly more complex.

  The CW type we provide supports indices. We also use option "-indices-matter"
  to make sure we handle universes properly.

**)

From Coq Require Import Utf8.

Set Universe Polymorphism.

(**

  We first redefine [True], [False] and [list] to avoid universe pollution and
  to ensure [list] is universe polymorphic.

**)

Inductive True : Prop :=
| I.

Inductive False : Prop :=.

Inductive list@{i}  (A : Type@{i}) : Type@{i} :=
| nil
| cons (x : A) (l : list A).

Arguments nil {A}.
Arguments cons {A}.

(** Test whether a list is empty **)
Definition isnil {A} (l : list A) :=
  match l with
  | nil => True
  | _ => False
  end.

Section CW.

  Universes i j k l m.
  Constraint l < m.

  (** Type of indices **)
  Context (Ix : Type@{i}).

  (** Instances of recursive arguments **)
  Inductive ind_inst@{u} : Type@{max(u+1,i)} :=
  | ind (ix : Ix)
  | qind (A : Type@{u}) (i : A → Ix).

  (** Type of constructors (or rather index for the family of constructors) **)
  Context (Cons : Type@{j}).

  (** Context (Type) associated to each constructor **)
  Context (Ctx : Cons → Type@{k}).

  (** Recursive arguments for each constructor **)
  Context (Args : ∀ (c : Cons), Ctx c → list@{m} ind_inst@{l}).

  (** Index of the return type of each constructor **)
  Context (idx : ∀ (c : Cons), Ctx c → Ix).

  Notation cstrs := (list@{m} ind_inst@{l}).

  (** Useful projections from lists of [ind_inst] **)

  Definition is_ind (l : cstrs) :=
    match l with
    | cons (ind ix) l => True
    | _ => False
    end.

  Definition is_qind (l : cstrs) :=
    match l with
    | cons (qind A i) l => True
    | _ => False
    end.

  Definition ind_ix l (h : is_ind l) :=
    match l return is_ind l → _ with
    | cons (ind ix) l => λ _, ix
    | _ => λ h, False_rect _ h
    end h.

  Definition ind_tl l (h : is_ind l) :=
    match l return is_ind l → _ with
    | cons (ind ix) l => λ _, l
    | _ => λ h, False_rect _ h
    end h.

  Definition qind_ty l (h : is_qind l) :=
    match l return is_qind l → _ with
    | cons (qind A ix) l => λ _, A
    | _ => λ h, False_rect _ h
    end h.

  Definition qind_i l (h : is_qind l) : qind_ty l h → Ix :=
    match l return ∀ (h : is_qind l), qind_ty l h → Ix with
    | cons (qind A ix) l => λ _, ix
    | _ => λ h, False_rect _ h
    end h.

  Definition qind_tl l (h : is_qind l) :=
    match l return is_qind l → _ with
    | cons (qind A ix) l => λ _, l
    | _ => λ h, False_rect _ h
    end h.

  (** An inductive to instantiate the recursive arguments.

    We use the projections above to avoid having [l] as an index and thus
    increasing the universe artificially.
    This obfuscate the definition slightly but it is probably worth it!

  **)

  Inductive args@{u v w | l < v, i <= w, l <= w} (I : Ix → Type@{u}) (l : cstrs) : Type@{max(u,l)} :=
  (* Inductive args (I : Ix → Type) (l : cstrs) : Type := *)
  | args_nil : isnil@{m} l → args I l
  | args_oind (h : is_ind l) :
    I (ind_ix l h) → args I (ind_tl l h) → args I l
  | args_qind (h : is_qind l) :
    (∀ (c : qind_ty@{v l} l h), I (qind_i@{v w} l h c)) → args I (qind_tl l h) → args I l.

  Arguments args_nil {I l}.
  Arguments args_oind {I l}.
  Arguments args_qind {I l}.

  Inductive CW@{u v w} : Ix → Type@{u} :=
  | con (c : Cons) (ctx : Ctx c) : args@{u v w} CW (Args c ctx) → CW (idx c ctx).

End CW.

(* Set Printing Universes.
Print CW. *)
