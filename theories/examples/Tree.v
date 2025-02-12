(*** Trees (nested version) as CW types ***)

(**

  We rely on the fact that nested inductive types can be implemented as mutual
  inductive types which in turn are encoded using an index.

**)

From Coq Require Import Utf8 Lia.
From Equations Require Import Equations.
From CW Require Import CW.

Set Equations Transparent.

Module Real.

  (** Nested version **)
  Inductive n_tree (A : Type) :=
  | n_node (a : A) (children : list (n_tree A)).

  (** Mutual version **)
  Inductive m_tree (A : Type) :=
  | m_node (a : A) (children : m_forest A)

  with m_forest (A : Type) :=
  | m_nil
  | m_cons (t : m_tree A) (f : m_forest A).

  (** Indexed version **)
  Inductive i_tree (A : Type) : bool -> Type :=
  | i_node (a : A) (children : i_tree A false) : i_tree A true
  | i_nil : i_tree A false
  | i_cons (t : i_tree A true) (f : i_tree A false) : i_tree A false.

  (* About i_tree_rect. *)
  (**

    [i_tree_rect :
      ∀ (A : Type) (P : ∀ b, i_tree A b → Type),
        (∀ a children,
          P false children →
          P true (i_node A a children)
        ) →
        P false (i_nil A) →
        (∀ t, P true t → ∀ f, P false f → P false (i_cons A t f)) →
        ∀ b i, P b i
    ]

  **)

End Real.

Section Tree.

  (** All is parametrised by the type of labels **)
  Context (A : Type).

  (** Index tells whether it's a tree or a forest **)
  Definition Ix := bool.

  (** Three constructors **)
  Definition Cons := option bool.

  (** Three-way branching **)

  Notation c_node := (Some true).
  Notation c_nil := (Some false).
  Notation c_cons := (None).

  Definition cons_case (c : Cons) {T} (u v w : T) : T :=
    match c with
    | c_node => u
    | c_nil => v
    | c_cons => w
    end.

  (** Non-recursive arguments

    Only [node] as one, the label (of type [A]).

  **)
  Definition Ctx (c : Cons) :=
    cons_case c A unit unit.

  (** Recursive arguments **)
  Definition Args (c : Cons) (_ : Ctx c) :=
    cons_case c
      (cons (ind false) nil)
      nil
      (cons (ind true) (cons (ind false) nil)).

  (** Return index **)
  Definition idx (c : Cons) (_ : Ctx c) :=
    cons_case c true false false.

  (** Now we are ready to define [Tree]! **)
  Notation PreTree := (CW Ix Cons Ctx Args idx).

  Definition Tree : Type :=
    PreTree true.

  Definition Forest : Type :=
    PreTree false.

  (** Constructors **)

  Definition node (a : A) (children : Forest) : Tree :=
    con c_node a (args_oind CW.I children (args_nil CW.I))
    : PreTree (idx c_node _).

  Definition fnil : Forest :=
    con c_nil tt (args_nil CW.I) : PreTree (idx c_nil _).

  Definition fcons (t : Tree) (f : Forest) : Forest :=
    con c_cons tt (args_oind CW.I t (args_oind CW.I f (args_nil CW.I)))
    : PreTree (idx c_cons _).

  (** Eliminator **)

  Equations rect (P : ∀ b, PreTree b → Type)
    (hnode : ∀ a children, P false children → P true (node a children))
    (hnil : P false fnil)
    (hcons : ∀ t f, P true t → P false f → P false (fcons t f))
    {b} t : P b t :=
    rect P hn hz hs (con c_node a (args_oind CW.I ch (args_nil CW.I))) :=
      hn a ch (rect P hn hz hs ch) ;
    rect P hn hz hs (con c_nil tt (args_nil CW.I)) := hz ;
    rect P hn hz hs (con c_cons tt (args_oind CW.I t (args_oind CW.I f (args_nil CW.I)))) :=
      hs t f (rect P hn hz hs t) (rect P hn hz hs f).

  (** We verify that the computation rules are indeed verified. **)

  Goal ∀ P hn hz hs a ch, rect P hn hz hs (node a ch) = hn a ch (rect P hn hz hs ch).
  Proof.
    reflexivity.
  Abort.

  Goal ∀ P hn hz hs, rect P hn hz hs fnil = hz.
  Proof.
    reflexivity.
  Abort.

  Goal ∀ P hn hz hs t f, rect P hn hz hs (fcons t f) = hs t f (rect P hn hz hs t) (rect P hn hz hs f).
  Proof.
    reflexivity.
  Abort.

End Tree.
