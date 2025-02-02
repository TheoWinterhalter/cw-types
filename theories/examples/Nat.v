(*** Natural numbers as CW types ***)

From Coq Require Import Utf8 Lia.
From Equations Require Import Equations.
From CW Require Import CW.

Set Equations Transparent.

Section Nat.

  (** No index **)
  Definition Ix := unit.

  (** Two constructors **)
  Definition Cons := bool.

  (** No non-recursive arguments **)
  Definition Ctx (isz : Cons) := unit.

  (** Only one recursive argument for the second constructor **)
  Definition Args (isz : Cons) (_ : Ctx isz) :=
    if isz then nil
    else cons (ind tt) nil.

  (** Return index is trivial **)
  Definition idx (isz : Cons) (_ : Ctx isz) :=
    tt.

  (** Now we are ready to define [Nat]! **)
  Notation PreNat := (CW Ix Cons Ctx Args idx).

  Definition Nat : Type :=
    PreNat tt.

  (** We also define the constructor [zer]: **)
  Definition zer : Nat :=
    con true tt (args_nil CW.I).

  (** And the constructor [suc]: **)
  Definition suc (n : Nat) : Nat :=
    con false tt (args_oind CW.I n (args_nil CW.I)).

  (** Finally we define the eliminator. **)
  Equations Nat_rect_gen (P : ∀ u, PreNat u → Type)
    (hz : P tt zer)
    (hs : ∀ n, P tt n → P tt (suc n))
    u (n : PreNat u) : P u n :=
    Nat_rect_gen P hz hs ?(tt) (con true tt (args_nil CW.I)) := hz ;
    Nat_rect_gen P hz hs ?(tt) (con false tt (args_oind CW.I n (args_nil CW.I))) :=
      hs n (Nat_rect_gen P hz hs tt n).

  Definition Nat_rect (P : Nat → Type)
    (hz : P zer)
    (hs : ∀ n, P n → P (suc n))
    (n : Nat) : P n :=
    Nat_rect_gen (λ u, match u with tt => P end) hz hs tt n.

  (** We verify that the computation rules are indeed verified. **)

  Goal ∀ P hz hs, Nat_rect P hz hs zer = hz.
  Proof.
    reflexivity.
  Abort.

  Goal ∀ P hz hs n, Nat_rect P hz hs (suc n) = hs n (Nat_rect P hz hs n).
  Proof.
    reflexivity.
  Abort.

End Nat.
