(*** Indexed W types as CW types ***)

(**

  We first recall what an indexed W types is before showing it can be encoded
  using CW types while retaining the computation rules.

  We take the version of Jasper Hugunin here, as defined in
  https://github.com/jashug/IWTypes

**)

From Coq Require Import Utf8 Lia.
From Equations Require Import Equations.
From CW Require Import CW.

Set Universe Polymorphism.
Set Equations Transparent.

Module real_IW.

  Section def.

    Context (A : Type) (B : A → Type).
    Context (I : Type).
    Context (C : A → I) (D : ∀ (x : A), B x → I).

    Inductive real_IW : I → Type :=
    | sup (x : A) (f : ∀ (c : B x), real_IW (D x c)) : real_IW (C x).

    (* About sup. *)
    (* About real_IW_rect. *)

  End def.

  (* Set Printing Universes.
  About real_IW. *)

  (** Universes

    The above command yields the following result:

    real_IW@{i j k} :
      ∀ (A : Type@{i}) (B : A → Type@{j}) (I : Type@{k})
        (C : A → I) (D : ∀ x : A, B x → I),
        I → Type@{max(i,j,k)}

  **)

End real_IW.

Section IW.

  (** The parameters of IW **)
  Context (A : Type) (B : A → Type).
  Context (I : Type).
  Context (C : A → I) (D : ∀ (x : A), B x → I).

  (** Only one constructor **)
  Definition Cons := unit.

  (** Only one non-recursive argument **)
  Definition Ctx (_ : Cons) := A.

  (** Only one recursive argument, quantified **)
  Definition Args (c : Cons) (a : Ctx c) :=
    cons (qind (B a) (D a)) nil.

  (** Return index is given by [C] **)
  Definition idx (c : Cons) (a : Ctx c) :=
    C a.

  (** Now we are ready to define [IW]! **)
  Definition IW : I → Type :=
    CW I Cons Ctx Args idx.

  (** We also define the constructor [sup]: **)
  Definition sup (x : A) (f : ∀ c, IW (D x c)) : IW (C x) :=
    con tt x (args_qind CW.I f (args_nil CW.I)).

  (** Finally we define the eliminator. **)
  Equations IW_rect (P : ∀ i, IW i → Type)
    (h : ∀ x f, (∀ c, P (D x c) (f c)) → P (C x) (sup x f))
    (i : I) (t : IW i) : P i t :=
    IW_rect P h i (con tt x (args_qind CW.I f (args_nil CW.I))) :=
      h x f (λ c, IW_rect P h _ _).

  (** We verify that the computation rule is indeed verified.

    In particular we can see that Equations did not introduce any funny
    business, so all is well.

   **)
  Goal ∀ P h x f,
    IW_rect P h (C x) (sup x f) = h x f (λ c, IW_rect P h (D x c) (f c)).
  Proof.
    reflexivity.
  Abort.

End IW.

(** We can also check the universes if needed. **)

(* Set Printing Universes.
About IW. *)

(** This returns the following

  IW@{i j k l m n o p} :
    ∀ (A : Type@{i}) (B : A → Type@{j}) (I : Type@{k})
      (C : A → I) (D : ∀ x : A, B x → I),
      I → Type@{l}

  with the following constraints

  j < m
  j < o
  i <= n
  j <= n
  j <= p
  k <= m
  k <= n
  k <= p
  n <= l

  As such we can pick l = n = max(i,j,k), p = max(j,k), m = max(k,j+1), o = j+1
  and recover the same universe constraints as the inductive version.

**)
