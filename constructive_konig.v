(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Permutation Utf8.

Import ListNotations.

Set Implicit Arguments.

(* Finitary conjunction over: ⋀₁P a list, or ⋀₂R a pair of lists *)
#[local] Notation "⋀₁ P" := (Forall P) (at level 0, right associativity, format "⋀₁ P").
#[local] Notation "⋀₂ R" :=(Forall2 R) (at level 0, right associativity, format "⋀₂ R").

(* Notations for homogeneous unary and binary relations *)
#[local] Notation rel₁ X := (X → Prop).
#[local] Notation rel₂ X := (X → X → Prop).

(* Inclusion for relations and the converse/transposed relation *)
#[local] Notation "P ⊆₁ Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[local] Notation "R ⊆₂ T" := (∀ x y, R x y → T x y) (at level 70, no associativity, format "R  ⊆₂  T").
#[local] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Arguments In {_}.
Arguments length {_}.
Arguments cons {_}.

(* Usual notation for length, membership and permutations *)
#[local] Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").
#[local] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[local] Notation "l ~ₚ m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").

(* Usual hints for membership and permutations *)
#[local] Hint Resolve in_eq in_cons in_or_app incl_refl incl_tl : core.
#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_middle Permutation_cons_app Permutation_in Permutation_sym : core.

(** Some list utilities *)

Fact cons_inj X (x y : X) l m : x::l = y::m → x = y ∧ l = m.
Proof. now inversion 1. Qed.

Fact app_length_inj X (l₁ l₂ m₁ m₂ : list X) :
    l₁++l₂ = m₁++m₂ → ⌊l₁⌋ = ⌊m₁⌋ → l₁ = m₁ ∧ l₂ = m₂.
Proof.
  revert m₁; induction l₁ as [ | x l₁ IH ]; intros [ | y m₁ ]; try easy; simpl.
  intros (-> & ?)%cons_inj E.
  destruct (IH m₁); try lia; subst; auto.
Qed.

Fact list_rev_forall X (P : list X → Prop) : (∀l, P (rev l)) → ∀l, P l.
Proof. intros ? ?; rewrite <- rev_involutive; auto. Qed.

(* Cutting a list in half given a split of its length *)
Fact list_length_split X (m : list X) a b : ⌊m⌋ = a+b → { l : _ & { r | m = l++r ∧ ⌊l⌋ = a ∧ ⌊r⌋ = b } }.
Proof.
  intros E.
  exists (firstn a m), (skipn a m); split.
  + now rewrite firstn_skipn.
  + rewrite firstn_length_le, skipn_length; lia. 
Qed.

(* Forall2 mononotic *)

Fact Forall2_mono X Y (R T : X → Y → Prop) : R ⊆₂ T → ⋀₂R ⊆₂ ⋀₂T.
Proof. induction 2; eauto. Qed.

(* Finite reification of an existential quantifier *)
Fact forall_ex_Forall2 X Y (R : X → Y → Prop) l : (∀x, x ∈ l → ∃y, R x y) → ∃m, ⋀₂R l m.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + exists []; eauto.
  + destruct (Hl x); auto.
    destruct IHl; eauto.
Qed.

(* Inversion facts for the ⋀₂R _ _ predicate *)
Fact Forall2_in_left_inv X Y (R : X → Y → Prop) l m x : ⋀₂R l m → x ∈ l → ∃y, y ∈ m ∧ R x y.
Proof.
  induction 1 as [ | ? ? ? ? ? _ IH ]; simpl; try easy.
  intros [ <- | (? & [])%IH ]; eauto.
Qed.

Fact Forall2_in_right_inv X Y (R : X → Y → Prop) l m y : ⋀₂R l m → y ∈ m → ∃x, x ∈ l ∧ R x y.
Proof.
  induction 1 as [ | ? ? ? ? ? _ IH ]; simpl; try easy.
  intros [ <- | (? & [])%IH ]; eauto.
Qed.

Arguments Forall2_in_left_inv [_ _ _ _ _ _].
Arguments Forall2_in_right_inv [_ _ _ _ _ _].

Fact Forall2_nil_left_inv X Y (R : X → Y → Prop) m : ⋀₂R [] m → m = [].
Proof. now inversion 1. Qed.

Fact Forall2_nil_right_inv X Y (R : X → Y → Prop) l : ⋀₂R l [] → l = [].
Proof. now inversion 1. Qed.

Fact Forall2_cons_left_inv X Y (R : X → Y → Prop) x l m : 
    ⋀₂R (x::l) m → ∃ y m', m = y::m' ∧ R x y ∧ ⋀₂R l m'.
Proof. inversion 1; eauto. Qed.

Fact Forall2_cons_right_inv X Y (R : X → Y → Prop) l y m :
    ⋀₂R l (y::m) → ∃ x l', l = x::l' ∧ R x y ∧ ⋀₂R l' m.
Proof. inversion 1; eauto. Qed.

Fact Forall2_cons_iff X Y (R : X → Y → Prop) l m x y : 
    ⋀₂R (x::l) (y::m) ↔ R x y ∧ ⋀₂R l m.
Proof.
  split.
  + now inversion 1.
  + intros []; eauto.
Qed.

(* Forall2 swap *)
Fact Forall2_swap X Y (R : X → Y → Prop) l m : ⋀₂R l m ↔ ⋀₂(R⁻¹) m l.
Proof. split; induction 1; eauto. Qed.

(* Forall2 and rev *)

Local Fact Forall2__Forall2_rev X Y (R : X → Y → Prop) l m : ⋀₂R l m → ⋀₂R (rev l) (rev m).
Proof.
  induction 1; simpl; auto.
  apply Forall2_app; auto.
Qed.

Fact Forall2_rev_iff X Y (R : X → Y → Prop) l m : ⋀₂R l m ↔ ⋀₂R (rev l) (rev m).
Proof.
  split.
  + apply Forall2__Forall2_rev.
  + intros ?%Forall2__Forall2_rev.
    now rewrite !rev_involutive in H.
Qed.

(* Forall2 composition *) 

Fact Forall2_compose {X Y Z} {R : X → Y → Prop} {T : Y → Z → Prop} {l m p} :
    ⋀₂R l m → ⋀₂T m p → ⋀₂(λ x z, ∃y, R x y ∧ T y z) l p.
Proof.
  induction 1 as [ | x y l m H1 H2 IH2 ] in p |- *.
  + intros ->%Forall2_nil_left_inv; auto.
  + intros (? & ? & -> & [])%Forall2_cons_left_inv; eauto.
Qed.

(* Weak binary choice over finitely many elements *)
Fact list_wchoose X (P Q : X → Prop) l :
    (∀x, x ∈ l → P x ∨ Q x)
  → (∃x, x ∈ l ∧ P x) ∨ ∀x, x ∈ l → Q x.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + right; now simpl.
  + destruct (Hl x); eauto.
    destruct IHl as [(? & []) | ]; eauto.
    right; intros ? [ <- | ]; eauto.
Qed.

(* Weakly decidable proposition satisfy propositional XM *)
Notation wdec P := (P ∨ ¬ P).

(* Weak decidability of membership/∈ *)

Fact list_in_wdec X (x : X) l : (∀y, y ∈ l → wdec (x = y)) → wdec (x ∈ l).
Proof.
  induction l as [ | y l IHl ]; intros Hl.
  + right; now simpl.
  + destruct (Hl y) as [ <- | ]; eauto.
    destruct IHl; eauto.
    right; intros [ <- | ]; eauto.
Qed.

(* Maximum value in a list of integers *)
Definition list_max := fold_right max 0.

Fact list_max_in n l : n ∈ l → n ≤ list_max l.
Proof.
  revert n; apply Forall_forall.
  induction l as [ | x l IHl ]; simpl; constructor.
  + lia.
  + revert IHl; apply Forall_impl; lia.
Qed.

Fact list_max_find l : l = [] ∨ list_max l ∈ l.
Proof.
  induction l as [ | x l [ -> | ] ]; auto; right; simpl.
  + lia.
  + destruct (Nat.max_spec_le x (list_max l))
      as [ (_ & ->) | (_ & ->) ]; auto.
Qed.

(** Recollection of De Morgan laws, exclusively used in one equivalence below to
    give an explanation of positive and negative characterizations of covers.
    We *DO NOT* import the Classical module to be precise on a which De Morgan law
    we actually use in this equivalence proof.

    Notice that we keep excluded middle (XM) as a (local) assumption, ie we do not
    declare it as an axiom so we can be precise in our claim that it is only
    needed to show that equivalence between the positive and negative
    characterization of covers. *)

(* This is the definition of propositonal eXcluded Middle (XM) *)
Definition XM := ∀P, P ∨ ¬ P.

Section De_Morgan_FO.

  Variables X : Type.

  (** These are intuitionistically valid *)

  (* Congruence laws *)

  Fact imp_iff_compat (A B C D : Prop) : (A ↔ C) → (B ↔ D) → (A → B) ↔ (C → D).
  Proof. tauto. Qed.

  Fact forall_iff_compat (P Q : X → Prop) : (∀x, P x ↔ Q x) → (∀x, P x) ↔ (∀x, Q x).
  Proof. intros H1; split; intros ? ?; apply H1; auto. Qed.

  (* Three intuitionistic propositional De Morgan laws *)

  Fact imp_not__not_conj (P Q : Prop) : (P → ¬ Q) ↔ ¬ (P ∧ Q).
  Proof. tauto. Qed.

  Fact imp_imp_comm (A B C : Prop) : (A → B → C) ↔ (B → A → C).
  Proof. tauto. Qed.

  Fact contrapose_not (A B : Prop) : (A → ¬ B) ↔ (B → ¬ A).
  Proof. tauto. Qed.

  (* Two intuitionistic first-order De Morgan laws *)

  Fact not_ex_conj (P Q : X → Prop) : ¬ (∃y, P y ∧ Q y) ↔ ∀y, P y → ¬ Q y.
  Proof.
    split.
    + intros H y H1 H2; apply H; eauto.
    + intros H1 (y & H2%H1 & []%H2).
  Qed.

  Fact not_ex_forall_not (P : X → Prop) : ¬ (∃x, P x) ↔ ∀x, ¬ P x.
  Proof.
    split.
    + intros H x p; apply H; eauto.
    + now intros H (? & ?%H).
  Qed.

  (** For the below De Morgan laws, one needs excluded middle *)

  Hypothesis xm : XM.

  Fact nnpp (P : Prop) : ¬ ¬ P ↔ P.
  Proof.
    split.
    + intros H.
      destruct (xm P); auto.
      now destruct H.
    + intros H H1; now apply H1.
  Qed.

  (* These two are classic propositional De Morgan laws *)

  Fact contrapose_0 (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P).
  Proof.
    split.
    + intros H G ?%H; now apply G.
    + intros H H1.
      destruct (xm Q) as [ | []%H ]; trivial.
  Qed.

  (* ¬ (P → Q) ↔ (P ∧ ¬ Q) but in negative position to avoid the conjunction ∧ *)
  Fact not_imp_negative (P Q A : Prop) : (¬ (P → Q) → A) ↔ (¬ Q → P → A).
  Proof.
    split.
    + intros H1 H2 H3; apply H1; intros ?; apply H2; auto.
    + intros H1 H2; apply H1.
      * contradict H2; auto.
      * apply nnpp; contradict H2; now intros ?%H2.
  Qed.

  (* This is classic first order De Morgan contraposition *)
  Fact contrapose_1 (P Q : X → Prop) : P ⊆₁ Q ↔ (λ x, ¬ Q x) ⊆₁ (λ x, ¬ P x).
  Proof.
    split.
    + intros H x H1; contradict H1; auto.
    + intros H x H1.
      destruct (xm (Q x)); auto.
      contradict H1; auto.
  Qed.

End De_Morgan_FO.

(** Some basic results about Dependent Choice (DC), here in type theory.
    We give a more convenient form to DC over a Σ-type *)

Section dependent_choice_sigma.

  Definition DC X :=
    ∀(R : rel₂ X),
        (∀x, ∃y, R x y) 
       → ∀x, ∃ρ, ρ 0 = x ∧ ∀n, R (ρ n) (ρ (S n)).

  (* Below is a specialization of Dependent Choice on a Σ-type 

     If R is a total relation on {x | Q x} then there is a 
     R-sequence starting from any point in Q. *)

  Definition DC_Σ {X} (Q : rel₁ X) :=
    ∀R, (∀x, Q x → ∃y, Q y ∧ R x y)
       → ∀x, Q x → ∃ρ, ρ 0 = x ∧ (∀n, Q (ρ n) ∧ R (ρ n) (ρ (S n))).

  Fact DC_sig__DC_Σ X (Q : rel₁ X) : DC {x | Q x} → DC_Σ Q.
  Proof.
    intros dc R HR x Hx.
    destruct dc
      with (R := λ u v : sig Q, R (proj1_sig u) (proj1_sig v))
           (x := exist _ x Hx)
      as (ρ & H1 & H2).
    + intros (u & Hu); simpl.
      destruct (HR _ Hu) as (v & Hv & E).
      now exists (exist _ v Hv).
    + exists (fun n => proj1_sig (ρ n)); repeat split; auto.
      * now rewrite H1.
      * apply (proj2_sig _).
  Qed.

  Fact DC_Σ__DC X : DC_Σ (λ _ : X, True) → DC X.
  Proof.
    intros dc R HR x.
    destruct (dc R) with x as (ρ & H1 & H2); eauto.
    + clear x; intros x _; destruct (HR x); eauto.
    + exists ρ; split; auto; intro; apply H2.
  Qed.

  Hint Resolve DC_sig__DC_Σ DC_Σ__DC : core.

  (* Dependent Choice and Dependent Choice on Σ-types are equivalent *)

  Corollary DC_iff_DC_Σ : (∀X, DC X) ↔ ∀ X P, @DC_Σ X P.
  Proof. split; eauto. Qed.

End dependent_choice_sigma.

(** The three below definitions of accessibility are the same:
      - founded 
      - acc 
      - Acc
    apart from the orientation of the relation or from
    superflous parameters. *)

Inductive acc {X} (R : rel₂ X) x : Prop :=
  | acc_intro : (∀y, R x y → acc R y) → acc R x.

Fact acc_irrefl X (R : rel₂ X) x : acc R x → ¬ R x x.
Proof. unfold not; induction 1; eauto. Qed.

(** This is the notion "R-founded" defined in [SC], Definition 3.1 p 74

    [SC] Claudio Sacerdoti Coen and Silvio Valentini. "General Recursion and Formal Topology." 
         PAR-10. Partiality and Recursion in Interactive Theorem Provers, volume 5 of 
         EPiC Series in Computing, pages 72–83. EasyChair, 2012. doi:10.29007/hl75. *)

Inductive founded {X} (R : rel₂ X) x : Prop :=
  | founded_intro : ¬ R x x → (∀y, R x y → founded R y) → founded R x.

(* This is Coq standard definition of Acc R, part of the Init module 
   which uses the reversed relation as compared to acc R *)

Print Acc.

Section founded_vs_acc_vs_Acc.

  Variables (X : Type).

  Implicit Type (R : rel₂ X).

  Hint Constructors acc founded Acc : core.

  Fact founded_iff_acc R x : founded R x ↔ acc R x.
  Proof.
    split.
    + induction 1; auto.
    + induction 1 as [ x Hx IH ]; eauto.
      constructor; auto.
      now intros H%acc_irrefl.
  Qed.

  Remark Acc_rev_iff_acc R x : Acc R⁻¹ x ↔ acc R x.
  Proof. split; induction 1; eauto. Qed.

  Remark acc_rev_iff_Acc R x : acc R⁻¹ x ↔ Acc R x.
  Proof. rewrite <- Acc_rev_iff_acc; reflexivity. Qed.

End founded_vs_acc_vs_Acc.

(** The notion of being upward closed for T *)

#[local] Notation upclosed T P := (∀ x y, T x y → P x → P y).

Fact Forall_upclosed_perm X (P : rel₁ X) : upclosed (λ l m, l ~ₚ m) ⋀₁P.
Proof. intros ? ?; rewrite !Forall_forall; eauto. Qed.

(**  The cover inductive predicate is given by two rules  *)

Unset Elimination Schemes.

Inductive cover	{X} (T : rel₂ X) (P : rel₁ X) x : Prop :=
  | cover_stop : P x → cover T P x
  | cover_next : (∀y, T x y → cover T P y) → cover T P x.

Set Elimination Schemes.

#[local] Hint Constructors cover : core.

Arguments cover_stop {_ _ _ _}.
Arguments cover_next {_ _ _ _}.

Section cover_ind.

  (* This one is usually auto-generated (but "Unset Elimination Schemes"
     prevents that) so let us review the code here. *)

  Variables (X : Type)
            (T : rel₂ X)
            (P : rel₁ X)
            (Q : rel₁ X)
            (Qs : P ⊆₁ Q)
            (Qn : ∀y, T y ⊆₁ Q → Q y).

  Fixpoint cover_ind x (d : cover T P x) : Q x :=
    match d with
    | cover_stop p => Qs p
    | cover_next n => Qn (λ y hy, cover_ind (n y hy))
    end.

End cover_ind.

Section cover_morphism.

  (* Transfert of the cover predicate using a morphism *)

  Variables (X Y : Type) (R : rel₂ X) (T : rel₂ Y)
            (P : rel₁ X) (Q : rel₁ Y)
            (f : Y → X)
            (HPQ : ∀y, P (f y) → Q y)
            (HRT : ∀ y₁ y₂, T y₁ y₂ → R (f y₁) (f y₂)).

  Lemma cover_morphism x y : x = f y → cover R P x → cover T Q y.
  Proof.
    intros Hy H; revert H y Hy.
    induction 1; intros ? ->; eauto.
  Qed.

End cover_morphism.

Section cover_extra.

  Variables (X : Type).

  Implicit Type (R T : rel₂ X) (P Q : rel₁ X).

  (* cover T P is antitone in T and monotone in P *)
  Fact cover_mono R T P Q : T ⊆₂ R → P ⊆₁ Q → cover R P ⊆₁ cover T Q.
  Proof. intros ? ? ?; now apply cover_morphism with (f := λ x, x). Qed.

  (* It preserves upward closed predicates *)
  Fact cover_upclosed T P : upclosed T P → upclosed T (cover T P).
  Proof. intros ? ? y H2 H3; revert H3 y H2; induction 1; eauto. Qed.

  Fact cover_idempotent T P : cover T (cover T P) ⊆₁ cover T P.
  Proof. induction 1; eauto. Qed.

  Hint Constructors acc : core.

  (* the cover inductive predicate generalizes
     the acc(essibility) predicate *)
  Theorem acc_iff_cover_empty T x : acc T x ↔ cover T (λ _, False) x.
  Proof. split; induction 1; now eauto. Qed.

  (* Positive characterization of cover T P x is ∀Q, cover_pos T P x Q *)
  Definition cover_pos T P x := λ Q, P ⊆₁ Q → (∀y, T y ⊆₁ Q → Q y) → Q x.

  (* The negative "characterization" of cover T P x is ∀Q, cover_neg T P x Q

     This characterization reads as: if a predicate Q is such that
       - Q contains x
       - Q is T-unstoppable
     then Q meets P *)
  Definition cover_neg T P x := λ Q, Q x → (∀y, Q y → ∃z, Q z ∧ T y z) → ∃y, P y ∧ Q y.

  (* The positive characterization is just a reformulation 
     of the inductive principle cover_ind for cover T P x,
     obtained by reordering the hypotheses. *)
  Fact cover_iff_cover_pos T P x : cover T P x ↔ ∀Q, cover_pos T P x Q.
  Proof.
    split.
    + intros Hx Q HQ0 HQ1; revert X T P Q HQ0 HQ1 x Hx; exact cover_ind.
    + intros H; apply H; auto.
  Qed.

  (* The positive characterization implies the negative characterization
     but not the converse; unless XM is assumed (see below).
     We use ∀Q, cover_pos T P x Q as an induction principle. *)
  Lemma cover_pos__cover_neg T P x : (∀Q, cover_pos T P x Q) → ∀Q, cover_neg T P x Q.
  Proof.
    unfold cover_neg.
    intros H.
    apply H; clear x H.
    + intros x; now exists x.
    + intros x IH Q H1 H2.
      destruct (H2 _ H1) as (? & []); eauto.
  Qed.

  Theorem cover_negative T P x : cover T P x → ∀Q, Q x → (∀y, Q y → ∃z, Q z ∧ T y z) → ∃y, P y ∧ Q y.
  Proof. rewrite cover_iff_cover_pos; apply cover_pos__cover_neg. Qed.

  Section cover_neg__cover_pos_DeMorgan.

    Hypothesis xm : XM.

    (* cover_pos and cover_neg are De Morgan duals, ie they are equivalent under excluded middle.
       We give a proof that only uses first order De Morgan laws in addition to congruence laws,
       which serve as a mean to rewrite under quantifiers. *)
    Remark cover_pos_iff_neg_XM T P x Q : cover_pos T P x Q ↔ cover_neg T P x (λ x, ¬ Q x).
    Proof.
      unfold cover_pos, cover_neg.
      rewrite <- not_imp_negative; trivial.
      rewrite contrapose_0 with (Q := ∃y, P y ∧ ¬ Q y); trivial.
      rewrite nnpp; trivial.
      repeat apply imp_iff_compat.       (* congruence → *)
      + rewrite not_ex_conj.
        apply forall_iff_compat; intro.  (* congruence ∀ *)
        apply imp_iff_compat_l.          (* congruence → *)
        rewrite nnpp; trivial.
        reflexivity.
      + apply forall_iff_compat; intro.  (* congruence ∀ *)
        rewrite contrapose_0 with (Q := Q _); trivial.
        apply imp_iff_compat_l.          (* congruence → *)
        rewrite <- nnpp with (P := ∃_, _); trivial.
        apply not_iff_compat.            (* congruence ¬ *)
        rewrite not_ex_forall_not.
        apply forall_iff_compat; intro.  (* congruence → *)
        rewrite <- imp_not__not_conj, <- contrapose_0; trivial.
        reflexivity.
      + reflexivity.
    Qed.

    Corollary cover_neg__cover_pos_XM T P x : (∀Q, cover_neg T P x Q) → ∀Q, cover_pos T P x Q.
    Proof. intros H ?; apply cover_pos_iff_neg_XM, H. Qed.

  End cover_neg__cover_pos_DeMorgan.

  (* The sequential "characterization" of cover T P x is ∀ρ, cover_seq T P x ρ.
     This reads as any T-sequence starting at x meets P *)
  Definition cover_seq T P x := λ ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → ∃n, P (ρ n).

  (* For a T-sequence ρ starting at x, its direct image 
     Q := λ x, ∃n, x = ρ n, satisfies
       - Q contains x
       - Q is T-unstoppable
     Hence Q meets P, which entails that ρ meets P *)
  Lemma cover_seq_direct_image T P x ρ : cover_neg T P x (λ x, ∃n, x = ρ n) → cover_seq T P x ρ.
  Proof. 
    intros H H1 H2.
    destruct H as (? & ? & ? & ->); eauto.
    intros ? (? & ->); eauto.
  Qed.

  Corollary cover_neg__cover_seq T P x : (∀Q, cover_neg T P x Q) → ∀ρ, cover_seq T P x ρ.
  Proof. intros H ρ; apply cover_seq_direct_image, H. Qed.

  Theorem cover_sequences T P x : cover T P x → ∀ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → ∃n, P (ρ n).
  Proof. intro; apply cover_neg__cover_seq; unfold cover_neg; now apply cover_negative. Qed.

  Section cover_seq__cover_neg_Dependent_Choice.

    Hypothesis dc : ∀X, DC X.

    (* Using D(ependent) C(hoice) on a Σ-type, but w/o excluded middle, one can get
       the negative characterization of cover T P x from the sequential one. *)
    Lemma cover_seq__cover_neg_DC T P x : (∀ρ, cover_seq T P x ρ) → ∀Q, cover_neg T P x Q.
    Proof.
      rewrite DC_iff_DC_Σ in dc.
      intros H Q Hx HQ.
      destruct (dc _ _ HQ _ Hx)
        as (rho & H1 & H2).
      destruct (H _ H1) as (n & Hn); eauto.
      + intro; apply H2.
      + exists (rho n); split; auto; apply H2.
    Qed.

    Hypothesis xm : XM.

    Theorem cover_seq_characterization_XM_DC T P x : cover T P x ↔ ∀ρ, cover_seq T P x ρ.
    Proof.
      split.
      + intro; now apply cover_neg__cover_seq, cover_pos__cover_neg, cover_iff_cover_pos.
      + intro; apply cover_iff_cover_pos, cover_neg__cover_pos_XM, cover_seq__cover_neg_DC; trivial.
    Qed.

  End cover_seq__cover_neg_Dependent_Choice.

End cover_extra.

Check cover_seq_characterization_XM_DC.

(** acc inductive predicate specializations *)

Section acc_instances.

  Variables (X : Type) (R : rel₂ X).

  Implicit Types (Q : rel₁ X).

  Lemma acc_negative x : acc R x → ∀Q, Q x → (∀y, Q y → ∃z, Q z ∧ R y z) → False.
  Proof.
    intros H%acc_iff_cover_empty Q H1 H2.
    now destruct (cover_negative H _ H1 H2).
  Qed.

  Lemma acc_sequences x : acc R x → ∀ρ, ρ 0 = x → (∀n, R (ρ n) (ρ (S n))) → False.
  Proof.
    intros H%acc_iff_cover_empty ρ <- ?.
    destruct cover_sequences
      with (ρ := ρ) (1 := H); eauto.
  Qed.

End acc_instances.

(** Finitary lifting of a binary relation to lists *)

(* fimage (for finitary image) is the lifting of T to lists (viewed as finite sets)
   T† := fimage T is a way to interpret finitary FANs, defined as:

     T† l m if any member of m in a T-image of some member of l *)

Definition fimage {X} (T : rel₂ X) l m := ∀y, y ∈ m → ∃x, x ∈ l ∧ T x y.

#[local] Notation "T †" := (fimage T) (at level 1, left associativity, format "T †").

Section finitary_image.

  Variable (X : Type) (T : rel₂ X).

  Implicit Type (l : list X) (P : rel₁ X).

  Fact fimage_mono l₁ l₂ m₁ m₂ : incl l₁ l₂ → incl m₂ m₁ → T† l₁ m₁ → T† l₂ m₂.
  Proof. intros ? ? H y ?; destruct (H y) as (? & []); eauto. Qed.

  Fact fimage_in_r_inv l m : T† l m → ∀y, y ∈ m → T† l [y].
  Proof. intros ? ? ? ? [ <- | [] ]; eauto. Qed.

  Fact fimage_sg_inv x y : T† [x] [y] → T x y.
  Proof. intros H; destruct (H y) as (? & [ <- | [] ] & ?); auto. Qed.

  Fact fimage_sg_r l x y : T x y → x ∈ l → T† l [y].
  Proof. intros ? ? ? [ <- | [] ]; eauto. Qed.

  Hint Resolve fimage_sg_inv fimage_in_r_inv : core.

  Fact fimage_sg_l_inv x m : T† [x] m → ∀y, y ∈ m → T x y.
  Proof. eauto. Qed.

  Lemma fimage_split_inv l₁ l₂ m : T† (l₁++l₂) m → ∃ m₁ m₂, m ~ₚ m₁++m₂ ∧ T† l₁ m₁ ∧ T† l₂ m₂.
  Proof.
    induction m as [ | x m IHm ]; intros H1.
    + exists nil, nil; repeat split; auto; intros ? [].
    + destruct IHm as (m1 & m2 & H3 & H4 & H5).
      * intros ? ?; apply H1; right; auto.
      * destruct (H1 x) as (y & []%in_app_iff & H7); auto.
        - exists (x::m1), m2; repeat split; simpl; eauto.
          intros ? [ <- | ]; eauto.
        - exists m1, (x::m2); repeat split; auto.
          intros ? [ <- | ]; eauto.
  Qed.

  Fact fimage_upclosed_perm_left k : upclosed (λ l m, l ~ₚ m) (λ l, T† l k).
  Proof. intros ? ? ? H ? (? & [])%H; eauto. Qed.

  Fact Forall_upclosed_fimage P : upclosed T P → upclosed T† ⋀₁P.
  Proof.
    intros ? ? ? H; do 2 rewrite Forall_forall.
    intros ? ? (? & [])%H; eauto.
  Qed.

End finitary_image.

Section FAN_cover.

  (** We give an original proof of a quite general formulation of 
      the FAN theorem for cover inductive predicates. *)

  Variable (X : Type) (T : rel₂ X) (P : rel₁ X) (HP : upclosed T P).

  Hint Resolve fimage_upclosed_perm_left Forall_upclosed_fimage Forall_upclosed_perm cover_upclosed : core.

  Fact cover_fimage_Forall_upclosed_perm : upclosed (λ l m, l ~ₚ m) (cover T† ⋀₁P).
  Proof. intros l m H1 H2; revert H2 m H1; induction 1; eauto. Qed.

  Hint Resolve fimage_sg_r : core.

  (** The key lemma: the T†-cover of ⋀₁ P *)

  Hint Resolve cover_fimage_Forall_upclosed_perm : core.

  Lemma cover_fimage_union l r : cover T† ⋀₁P l → cover T† ⋀₁P r → cover T† ⋀₁P (l++r).
  Proof.
    induction 1 as [ l Hl | ] in r |- *.
    + induction 1 in l, Hl |- *; eauto.
      * constructor 1; apply Forall_app; eauto.
      * constructor 2; intros ? (? & ? & ?%Permutation_sym & [])%fimage_split_inv; eauto.
    + constructor 2; intros ? (? & ? & ?%Permutation_sym & [])%fimage_split_inv; eauto.
  Qed.

  Corollary cover_fimage_Forall_cons x m : cover T† ⋀₁P [x] → cover T† ⋀₁P m → cover T† ⋀₁P (x::m).
  Proof. apply cover_fimage_union with (l := [_]). Qed.

  Hint Resolve fimage_mono
               fimage_in_r_inv
               cover_fimage_Forall_cons : core.

  Corollary cover_fimage_Forall l : (∀x, x ∈ l → cover T† ⋀₁P [x]) → cover T† ⋀₁P l.
  Proof. rewrite <- Forall_forall; induction 1; eauto. Qed.

  (* If x is in the T-cover of P then [x] is in the T†-cover of ⋀₁P
     hence P will be satisfied uniformly over all the iterates of
     the direct images of x, provided we only consider finitely
     many of them at each step *)

  Theorem FAN_cover x : cover T P x → cover T† ⋀₁P [x].
  Proof.
    induction 1 as [ | x IHx ].
    + now repeat constructor.
    + constructor 2; intros l Hl.
      apply cover_fimage_Forall.
      intros ? ?%(fimage_sg_l_inv Hl); auto.
  Qed.

  Hint Resolve FAN_cover : core.

  Theorem FAN_cover_many : ⋀₁(cover T P) ⊆₁ cover T† ⋀₁P.
  Proof.
    intros l Hl; apply cover_fimage_Forall.
    rewrite Forall_forall in Hl.
    eauto.
  Qed.

  (** This characterization looks like the characterization
      of Accessibility wrt. to list ordering, such as 

      https://github.com/DmxLarchey/Hydra/blob/a387860ba85490cd925c4488ab2f5b3e8fddbbcf/theories/hydra.v#L222

      Remains to be further investigated: can Acc_lo_iff 
      could be derived from cover_fimage_iff below. *)

  Fact cover_fimage_Forall_Forall l : cover T† ⋀₁P l → ∀x, x ∈ l → cover T P x.
  Proof. 
    induction 1 as [ l Hl | ]; eauto.
    rewrite Forall_forall in Hl; auto.
  Qed.

  Hint Resolve FAN_cover_many cover_fimage_Forall_Forall : core.

  Theorem cover_fimage_iff l : cover T† ⋀₁P l ↔ ∀x, x ∈ l → cover T P x.
  Proof. split; eauto; rewrite <- Forall_forall; auto. Qed.

End FAN_cover.

(** (reverse) n-prefixes of sequences
    beware that pfx α n = [α (n-1);...;α 0] *)

Section pfx.

  Variables (X : Type).

  Implicit Type (α : nat → X).

  Definition pfx α :=
    fix loop n :=
      match n with
      | 0   => []
      | S n => α n :: loop n
      end.

  Fact pfx_length α n : ⌊pfx α n⌋ = n.
  Proof. induction n; simpl; auto. Qed.

  Fact pfx_fix α n : pfx α (1+n) = α n :: pfx α n.
  Proof. reflexivity. Qed.

  Fact pfx_ext α β n : (∀ i : nat, i < n → α i = β i) → pfx α n = pfx β n.
  Proof. induction n; intro; simpl; f_equal; auto. Qed.

  Fact pfx_add α n m : pfx α (n+m) = pfx (λ i, α (i+m)) n ++ pfx α m.
  Proof. now induction n; simpl; f_equal. Qed.

  Fact pfx_S α n : pfx α (S n) = pfx (λ i, α (1+i)) n ++ [α 0].
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite pfx_add; f_equal; auto.
    apply pfx_ext; intros ? _; f_equal; lia.
  Qed.

  Fact pfx_split α n l m :
      l++m = pfx α n
    → l = pfx (λ i, α (i+⌊m⌋)) ⌊l⌋
    ∧ m = pfx α ⌊m⌋.
  Proof.
    intros E.
    apply app_length_inj.
    + rewrite E, <- pfx_add.
      f_equal.
      apply f_equal with (f := length) in E.
      now rewrite app_length, pfx_length in E.
    + now rewrite pfx_length.
  Qed.

End pfx.

Arguments pfx {X}.

(** the extends relation between lists *)

Section extends.

  Variable (X : Type).

  Implicit Type (l : list X).

  Inductive extends l : list X → Prop :=
    | extends_intro x : extends l (x::l).

  Hint Constructors extends : core.

  Fact extends_inv (l m : list X) :
      extends l m
    → match m with
      | []   => False
      | _::m => l = m
      end.
  Proof. now induction 1. Qed.

  Fact extends_iff l m : extends l m ↔ ∃ x : X, m = x::l.
  Proof.
    split.
    + induction 1; eauto.
    + intros (? & ->); auto.
  Qed.

  Fact hd_extends {l m} : extends l m → { x : X | m = x::l }.
  Proof.
    destruct m as [ | x m ]; intros H%extends_inv.
    + easy.
    + now exists x; subst.
  Qed.

  (* extends-sequences are sequences of n-prefixes *)
  Fact extends_pfx (α : nat → list X) :
      α 0 = [] 
    → (∀n, extends (α n) (α (S n)))
    → { ρ | ∀n, α n = pfx ρ n }.
  Proof.
    intros H1 H2.
    exists (λ n, proj1_sig (hd_extends (H2 n))).
    intros n.
    induction n as [ | n IHn ].
    + now simpl.
    + simpl.
      rewrite <- IHn.
      exact (proj2_sig (hd_extends _)).
  Qed. 

  (* And conversely *)
  Fact pfx_extends (ρ : nat → X) : pfx ρ 0 = [] ∧ ∀n, extends (pfx ρ n) (pfx ρ (S n)).
  Proof. split; constructor. Qed.

End extends.

Arguments extends {X}.

#[local] Hint Constructors extends : core.

(** bar inductive predicate specialized to lists *)

(* Monotone predicates on lists *)
#[local] Notation monotone P := (∀x l, P l → P (x::l)).

Section bar.

  Variables (X : Type).

  Implicit Type (P Q : rel₁ (list X)) (l : list X).

  (* Monotone is just an instance of upward-closed *)
  Fact upclosed_extends_iff_monotone P : upclosed extends P ↔ monotone P.
  Proof.
    split.
    + intros H ? ?; apply H; constructor.
    + induction 2; auto.
  Qed.

  Inductive bar P l : Prop :=
    | bar_stop : P l → bar P l
    | bar_next : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_iff_cover_extends P l : bar P l ↔ cover extends P l.
  Proof.
    split.
    + induction 1; eauto.
      constructor 2; induction 1; auto.
    + induction 1; eauto.
  Qed.

  Fact bar_monotone P : monotone P → monotone (bar P).
  Proof.
    rewrite <- !upclosed_extends_iff_monotone.
    intros H ? ?.
    rewrite !bar_iff_cover_extends.
    apply (cover_upclosed H).
  Qed.

  Fact bar_mono P Q : P ⊆₁ Q → bar P ⊆₁ bar Q.
  Proof. 
    intros ? ?.
    rewrite !bar_iff_cover_extends.
    apply cover_mono; auto.
  Qed.

  Fact bar_negative P : bar P [] → ∀Q, Q [] → (∀l, Q l → ∃x, Q (x::l)) → ∃l, P l ∧ Q l.
  Proof.
    intros H%bar_iff_cover_extends Q H1 H2. 
    apply (cover_negative H); eauto.
    intros ? (? & ?)%H2; eauto.
  Qed.

  Fact bar_sequences P : bar P [] → ∀α, ∃n, P (pfx α n).
  Proof.
    intros H%bar_iff_cover_extends α.
    destruct cover_sequences
      with (ρ := λ n, pfx α n) (1 := H); eauto.
    constructor.
  Qed.

  Hypothesis (xm : XM) (dc : ∀X, DC X).

  Theorem Brouwer_bar_XM_DC P : bar P [] ↔ ∀α, ∃n, P (pfx α n).
  Proof.
    rewrite bar_iff_cover_extends, cover_seq_characterization_XM_DC; auto.
    split.
    + intros H α.
      destruct (H (pfx α)); eauto.
      constructor.
    + intros H ρ H1 H2.
      destruct extends_pfx with (2 := H2)
        as (α & Hα); auto.
      destruct (H α) as (n & Hn).
      exists n; now rewrite Hα.
  Qed.

End bar.

Arguments bar {_}.

#[local] Hint Constructors bar : core.

(** The notion of finiteness defined as listability,
    equivalent to Kuratowsky finiteness *)

(* P is a finite predicate if it is listable *)
Definition finite {X} (P : rel₁ X) := ∃l, ∀x, P x ↔ x ∈ l.

(* The carrier of a list is finite, by definition *)
Fact finite_in X (l : list X) : finite (λ x, x ∈ l).
Proof. exists l; tauto. Qed.

(* The singleton is finite *)
Fact finite_eq X (x : X) : finite (λ y, x = y).
Proof. exists [x]; simpl; tauto. Qed.

(* Equivalent predicates are equi-finite *)
Fact finite_equiv X (P Q : rel₁ X) : (∀x, P x ↔ Q x) → finite Q → finite P.
Proof. intros E (l & ?); exists l; firstorder. Qed.

(* Composition by a finitary relation *)
Lemma finite_compose X Y (P : rel₁ X) (R : X → Y → Prop) :
        finite P
      → (∀x, P x → finite (R x))
      → finite (λ y, ∃x, R x y ∧ P x).
Proof.
  intros (l & Hl) HR.
  assert (∀x, x ∈ l → finite (R x)) as (m & Hm)%forall_ex_Forall2.
  + intros; now apply HR, Hl.
  + exists (concat m).
    intros y; rewrite in_concat; split.
    * intros (x & H1 & H2%Hl).
      destruct (Forall2_in_left_inv Hm H2) as (z & ? & E).
      exists z; now rewrite <- E.
    * intros (z & H1 & H2).
      destruct (Forall2_in_right_inv Hm H1) as (x & ? & E).
      exists x; now rewrite E, Hl.
Qed.

(* Choice sequences are finitely many *)
Fact finite_Forall2_rev X Y (R : X → Y → Prop) m :
       (∀y, y ∈ m → finite (λ x, R x y)) 
     → finite (λ l, ⋀₂R l m).
Proof.
  induction m as [ | y m IHm ].
  + intros _.
    apply finite_equiv with (Q := eq []).
    * split.
      - now intros ->%Forall2_nil_right_inv.
      - intros <-; auto.
    * apply finite_eq.
  + intros H.
    apply finite_equiv with (Q := λ l, exists x, (exists l', x::l' = l ∧ ⋀₂R l' m) ∧ R x y).
    * split.
      - intros (? & ? & -> & [])%Forall2_cons_right_inv; eauto.
      - intros (? & (? & <- & ?) & ?); auto.
    * apply finite_compose.
      1: apply H; auto.
      intros ? _; apply finite_compose; auto.
      intros ? _; apply finite_eq.
Qed.

(** The FAN on lists *)

#[local] Notation FAN lc := (λ l, ⋀₂(λ x c, x ∈ c) l lc).

#[local] Hint Resolve finite_in : core.

Fact FAN_finite X (lc : list (list X)) : finite (FAN lc).
Proof. apply finite_Forall2_rev; eauto. Qed.

(** Construction of the generic product and exponential 
    for lists, ie compute/spec of the list of choice lists,
    ake the concrete FAN is found in D. Fridlender's paper *)

Section list_prod.

  Variables (X Y Z : Type) (p : X → Y → Z).

  Definition list_prod l m := flat_map (λ x, map (p x) m) l.

  Fact list_prod_spec l m z : (∃ x y, z = p x y ∧ x ∈ l ∧ y ∈ m) ↔ z ∈ list_prod l m.
  Proof.
    unfold list_prod; rewrite in_flat_map; split.
    + intros (x & ? & -> & []).
      exists x; rewrite in_map_iff; eauto.
    + intros (? & ? & (? & <- & ?)%in_map_iff); eauto.
  Qed.

End list_prod.

Arguments list_prod {_ _ _}.

Section list_fan.

  Variable X : Type.

  Implicit Type (lc : list (list X)).

  Definition list_fan := 
    fix loop lc :=
      match lc with 
      | []    => [[]]
      | c::lc => list_prod cons c (loop lc)
      end.

  Fact list_fan_spec lc l : FAN lc l ↔ l ∈ list_fan lc.  
  Proof.
    induction lc as [ | c lc IH ] in l |- *; simpl; split.
    + intros ->%Forall2_nil_right_inv; auto.
    + intros [ <- | [] ]; eauto.
    + intros (? & ? & -> & ? & ?%IH)%Forall2_cons_right_inv.
      apply list_prod_spec; eauto.
    + intros (? & ? & -> & ? & ?%IH)%list_prod_spec; eauto.
  Qed.

  (* list_fan gives an explicit inhabitant of FAN *)
  Local Remark list_fan_finite_inhabits lc : finite (FAN lc).
  Proof. exact (ex_intro _ (list_fan lc) (list_fan_spec lc)). Qed.

  Fact list_fan_cons_inv c lc l : l ∈ list_fan (c::lc) ↔ ∃ x m, l = x::m ∧ x ∈ c ∧ m ∈ list_fan lc.
  Proof.
    rewrite <- list_fan_spec; split.
    + intros (x & m & ?)%Forall2_cons_right_inv.
      exists x, m; now rewrite <- list_fan_spec.
    + intros (x & m & -> & ? & ?%list_fan_spec); eauto.
  Qed.

  Fact extends_list_fan l m : extends l m → extends† (list_fan l) (list_fan m).
  Proof. induction 1; intros ? (? & ? & -> & [])%list_fan_cons_inv; eauto. Qed.

End list_fan.

Arguments list_fan {_}.

#[local] Hint Resolve extends_list_fan : core.

(** FAN theorem for inductive bars w/o reference to list_fan in its type *)
Theorem FAN_bar X (P : rel₁ (list X)) : monotone P → bar P [] → bar (λ l, FAN l ⊆₁ P) [].
Proof.
  intros HP; rewrite !bar_iff_cover_extends.
  intros ?%FAN_cover.
  2: now apply upclosed_extends_iff_monotone.
  revert H.
  apply cover_morphism with (f := list_fan); eauto.
  intros l Hl m ?%list_fan_spec.
  rewrite Forall_forall in Hl; auto.
Qed.

(** Generalization of Theorem 6 p12 of https://www.brics.dk/RS/98/39/BRICS-RS-98-39.pdf 
    where the implementation of lfan is abstracted away. *)
Theorem FAN_Fridlender X (P : rel₁ (list X)) (lfan : list (list X) → list (list X)) :
         (∀l lc, l ∈ lfan lc ↔ FAN lc l)
       → monotone P
       → bar P [] → bar (λ lc, ⋀₁P (lfan lc)) [].
Proof.
  intros Hlfan M H%FAN_bar; auto; clear M.
  revert H; apply bar_mono.
  intros lc Hlc; apply Forall_forall.
  now intros ? ?%Hlfan%Hlc.
Qed.

(** list branching finite trees, ie trees nested with lists *)

Unset Elimination Schemes.
Inductive tree X : Type := node : X → list (tree X) → tree X.
Set Elimination Schemes.

Arguments node {_}.

#[local] Notation "⟨ x | l ⟩" := (node x l) (at level 0, format "⟨ x | l ⟩").

Fact tree_ind X (P : tree X → Prop) :
    (∀ x l, (∀ t, t ∈ l → P t) → P ⟨x|l⟩) → ∀t, P t.
Proof.
  intros HP.
  refine (fix tree_ind t := _).
  destruct t as [ x l ].
  apply HP.
  intro t.
  induction l as [ | r l IH ].
  + intros [].
  + intros [ <- | ].
    * apply tree_ind.
    * now apply IH.
Qed.

Section tree_extra.

  Variables X : Type.

  Implicit Type (x : X) (t : tree X).

  Definition root t := match t with ⟨x|_⟩ => x end.
  Definition sons t := match t with ⟨_|l⟩ => l end.

  Fixpoint tree_ht t := 1+list_max (map tree_ht (sons t)).

  Fact tree_ht_fix x l : tree_ht ⟨x|l⟩ = 1+list_max (map tree_ht l).
  Proof. reflexivity. Qed.

  Inductive branch : tree X → list X → X → Prop :=
    | branch_void x l :          branch ⟨x|l⟩ [] x
    | branch_cons x l y m p z :  ⟨y|m⟩ ∈ l
                               → branch ⟨y|m⟩ p z
                               → branch ⟨x|l⟩ (y::p) z.

  Hint Constructors branch : core.

  Fact branch_inv t p z :
       branch t p z
     → match p with
       | []   => root t = z
       | y::p => ∃s, s ∈ sons t ∧ root s = y ∧ branch s p z
       end.
  Proof. destruct 1; eauto. Qed.

  Fact branch_nil_inv t z : branch t [] z ↔ root t = z.
  Proof.
    split.
    + apply branch_inv.
    + intros <-; destruct t; auto.
  Qed.

  Fact branch_cons_inv t y p z :
      branch t (y::p) z ↔ ∃s, s ∈ sons t ∧ root s = y ∧ branch s p z.
  Proof.
    split.
    + apply branch_inv.
    + destruct t; simpl; intros ([] & ? & <- & ?); eauto.
  Qed.

  Fact branch_length_tree_ht t p z : branch t p z → ⌊p⌋ < tree_ht t.
  Proof.
    induction 1 as [ | ? ? ? ? ? ? ? ? IH ]; simpl; [ lia | ].
    rewrite <- Nat.succ_lt_mono.
    apply Nat.lt_le_trans with (1 := IH),
          list_max_in,
          in_map_iff; eauto.
  Qed.

  (* If X has (weakly) decidable equality then branch is a
     (weakly) decidable predicate *)

  Lemma branch_wdec : (∀ x y, wdec (x = y)) → ∀ t p y, wdec (branch t p y).
  Proof.
    intros eqdec t.
    induction t as [ x l IH ].
    intros [ | y p ] z.
    + destruct (eqdec z x) as [ <- | ]; auto.
      right; intros <-%branch_inv; auto.
    + destruct list_wchoose 
        with (l := l) 
             (P := λ s, root s = y ∧ branch s p z)
             (Q := λ s, ~ (root s = y ∧ branch s p z))
        as [ ([k m] & H1 & <- & H3) | C ]; eauto.
      * intros u Hu.
        destruct (eqdec (root u) y) as [ <- | C ].
        2: right; intros []; auto.
        destruct (IH _ Hu p z); tauto.
      * right.
        intros (s & H1 & <- & H3)%branch_inv.
        apply (C s); eauto.
  Qed.

End tree_extra.

Arguments root {_}.
Arguments sons {_}.
Arguments tree_ht {_}.
Arguments branch {_}.

#[local] Hint Constructors branch : core.

(** Paths in a graph represented by a binary relation *)

Section path.

  Variable (X : Type).

  Implicit Type (T : rel₂ X) (P : rel₁ X) (x : X).

  (* Path in a graph (binary relation): path x p y means that
     p is the list of visited vertices after x and up to y *)

  Inductive path T : X → list X → X → Prop :=
    | path_void x :       path T x [] x
    | path_cons x y p z : T x y
                        → path T y p z
                        → path T x (y::p) z.

  Hint Constructors path : core.

  Fact path_inv T x p z :
       path T x p z
     → match p with
       | []   => x = z
       | y::p => T x y ∧ path T y p z
       end.
  Proof. destruct 1; eauto. Qed.

  Fact path_app T x p y q z : path T x p y → path T y q z → path T x (p++q) z.
  Proof. induction 1; simpl; eauto. Qed.

  Fact path_app_inv T x p q z : path T x (p++q) z → ∃y, path T x p y ∧ path T y q z.
  Proof.
    induction p as [ | ? ? IH ] in x |- *; simpl; eauto.
    intros (? & (? & [])%IH)%path_inv; eauto.
  Qed.

  Fact path_nil_inv T x y : path T x [] y ↔ x = y.
  Proof.
    split.
    + apply path_inv.
    + intros ->; eauto.
  Qed.

  Fact path_cons_inv T x y p z :
      path T x (y::p) z ↔ T x y ∧ path T y p z.
  Proof.
    split.
    + apply path_inv.
    + intros []; eauto.
  Qed.

  Hint Resolve path_app : core.

  Fact path_snoc_inv T x p a z : path T x (p++[a]) z ↔ ∃y, path T x p y ∧ T y z ∧ a = z.
  Proof. 
    split.
    + intros (? & ? & (? & ->%path_inv)%path_inv)%path_app_inv; eauto. 
    + intros (? & ? & ? & ->); eauto.
  Qed.

  Fact upclosed_path T P : upclosed T P → upclosed (λ x y, ∃p, path T x p y) P.
  Proof. intros ? ? ? (? & H); induction H; eauto. Qed.

  Section path_monotone.

    Variables (T : rel₂ X)
              (Q : list X → X → Prop)
              (HQ : ∀ p x y, T x y → Q p x → Q (p++[y]) y).

    Fact path_monotone p q x y : path T x q y → Q p x → Q (p++q) y.
    Proof.
      induction q as [ | ] using rev_ind in y |- *.
      + rewrite app_nil_r; now intros <-%path_inv.
      + intros (? & ? & ? & ->)%path_snoc_inv ?.
        rewrite app_assoc; eauto.
    Qed.

  End path_monotone.

  Lemma path_wdec T :
      (∀x, finite (T x))
    → (∀ x y, wdec (x = y))
    → (∀ x p y, wdec (path T x p y)).
  Proof.
    intros HT eqdec x p z.
    induction p as [ | y p IHp ] in x |- *.
    + destruct (eqdec x z) as [ <- | C ]; eauto.
      right; now intros <-%path_inv.
    + destruct (HT x) as (l & Hl).
      destruct (list_in_wdec l (fun z _ => eqdec y z))
        as [ ?%Hl | ].
      2: right; now intros [ ?%Hl _ ]%path_inv.
      destruct (IHp y); eauto.
      right; now intros[]%path_inv.
  Qed.

End path.

Arguments path {_}.

#[local] Hint Constructors path : core.

Section representation_of_relations_by_trees.

  (** When the length of paths is bounded,
      the paths from x of a finitary relation
      are representable by the branches
      of tree rooted with x. *)

  Variables (X : Type).

  Implicit Type (T : rel₂ X) (x : X).

  (* The notion of representation that
     comes to mind first. *)
  Definition strong_represents T P x t :=
      root t = x
    ∧ ∀ p y, branch t p y ↔ path T x p y ∧ P p y.

  (** strong_represents is too strong as it entails
      that P is weakly decidable on T-paths from x,
      when X is a discrete type, eg when X = nat *)
  Lemma strong_represents_entails_wdec T P x t :
       (∀ x y, wdec (x = y))
     → strong_represents T P x t
     → ∀ p y, path T x p y → wdec (P p y).
  Proof.
    intros eqdec (_ & E) p y Hp.
    destruct (branch_wdec eqdec t p y) as [ []%E | H ]; auto.
    rewrite E in H; tauto.
  Qed.

  (** So we favor this definition for representation
      of the relation T at root x by a tree, on the
      paths that satisfy P. 

      This means that t may contain branches that
      do not satisfy P. *)
  Definition represents T P x t :=
      root t = x
    ∧ ∀ p y, P p y → (branch t p y ↔ path T x p y ).

  (* A strong representation is a representation *)
  Fact strong_represents__represents T P x :
      strong_represents T P x ⊆₁ represents T P x.
  Proof. 
    intros ? (? & H); split; auto.
    intros ? ? ?; rewrite H; tauto.
  Qed.

  Variables (T : rel₂ X) (Tfin : ∀x, finite (T x)).

  (** length bounded path can be strongly represented
      because this is a (weakly) decidable predicate *)
  Theorem bounded_length_strongly_represented n x :
       ∃t, strong_represents T (λ p _, ⌊p⌋ ≤ n) x t.
  Proof.
    induction n as [ | n IHn ] in x |- *.
    + exists ⟨x|[]⟩; split; simpl; auto.
      intros p y; split.
      * destruct p; intros H%branch_inv; subst; simpl; auto.
        destruct H as (_ & [] & _).
      * destruct p; intros (?%path_inv & ?); simpl in *; subst; auto; lia.
    + destruct (Tfin x) as [ lx Hlx ].
      set (R x t := strong_represents T (λ p _, ⌊p⌋ ≤ n) x t).
      destruct (forall_ex_Forall2 R lx) as (lt & Hlt); eauto.
      exists ⟨x|lt⟩; split; auto.
      intros [ | y l ] z; split.
      * intros <-%branch_inv; simpl; split; auto; lia.
      * intros (<-%path_inv & _); auto.
      * intros (s & Hs & <- & H2)%branch_inv; simpl in Hs |- *.
        destruct (Forall2_in_right_inv Hlt Hs) as (y & H3 & <- & H4).
        apply H4 in H2 as [].
        split; try lia.
        constructor 2; auto.
        now apply Hlx.
      * simpl; intros ((H1%Hlx & H2)%path_inv & H3).
        destruct (Forall2_in_left_inv Hlt H1) as ([y' m] & ? & ? & G); subst; simpl; eauto.
        constructor 2 with m; auto.
        apply G; split; auto; lia.
  Qed.

  (** (T,P,x) is represented iff T-paths from x that satisfy P have
      a (globally) bounded length *)
  Theorem finitary_represented_iff_bounded P x :
       (∃t, represents T P x t)
     ↔ (∃n, ∀ p y, path T x p y → P p y → ⌊p⌋ < n).
  Proof.
    split.
    + intros (t & <- & Ht).
      exists (tree_ht t).
      intros p y H1 H2.
      apply Ht in H1; auto.
      revert H1; apply branch_length_tree_ht.
    + intros (n & Hn).
      destruct (bounded_length_strongly_represented n x)
        as (t & <- & Ht).
      exists t; split; auto.
      intros p y Hp; split.
      * now intros []%Ht.
      * intros ?; apply Ht; split; auto.
        eapply Hn in H; eauto; lia.
  Qed.

  Variables (x : X) (P : list X → X → Prop)
            (HP1 : ∀ p y z, T y z → P p y → P (p++[z]) z)
            (n : nat) (Hn : ∀ p y, path T x p y → n = ⌊p⌋ → P p y).

  Local Lemma paths_outside_circle p y : path T x p y → n ≤ ⌊p⌋ → P p y.
  Proof.
    intros H2 H3.
    destruct list_length_split
      with (m := p) (a := n) (b := ⌊p⌋-n)
      as (l & r & -> & H4 & H5); [ lia | clear H3 H5 ].
    apply path_app_inv in H2 as (z & H6 & H7).
    apply path_monotone with (2 := H7); eauto.
  Qed.

  Hint Resolve paths_outside_circle : core.

  Lemma short_paths p y : path T x p y → ¬ P p y → ⌊p⌋ < n.
  Proof.
    intros H1 H2.
    destruct (le_lt_dec n ⌊p⌋); auto.
    destruct H2; eauto.
  Qed.

End representation_of_relations_by_trees.

Arguments represents {X}.

Section konig_cover.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x)) 
            (P : rel₁ X) (Pupc : upclosed T P) 
            (x : X) (Hx : cover T P x).

  (* The circle of radius n: the points T-reachable from x with paths of length n *)
  Local Definition circle n := λ y, ∃p, path T x p y ∧ n = ⌊p⌋.

  (* There is only x on the circle of radius 0 *)
  Local Fact circle_0_spec z : circle 0 z ↔ x = z.
  Proof.
    split.
    + now intros ([] & ?%path_inv & ?).
    + intros <-; exists []; auto.
  Qed.

  (* circle (S n) is at one T-transition from circle n *)
  Local Fact circle_S_spec n z : circle (S n) z ↔ ∃y, T y z ∧ circle n y.
  Proof.
    split.
    + intros (p & H1 & H2).
      destruct p as [ | a p _ ] using rev_ind; [ easy | ].
      apply path_snoc_inv in H1 as (y & H3 & H4 & ->).
      exists y; split; auto.
      exists p; split; auto.
      rewrite app_length in H2; simpl in H2; lia.
    + intros (y & H1 & p & H2 & H3).
      exists (p++[z]); split.
      * eapply path_app; eauto.
      * rewrite app_length; simpl; lia.
  Qed.

  (* Each circle is finite *)
  Local Lemma circle_finite n : finite (circle n).
  Proof.
    induction n.
    + apply finite_equiv with (1 := circle_0_spec), finite_eq.
    + apply finite_equiv with (1 := circle_S_spec _), finite_compose; eauto.
  Qed.

  (* Q is the set of lists l that collect one circle,
     ie it is the collection of all the list representations
     of the circle of radius n for some n *)
  Let Q l := ∃n, ∀x, circle n x ↔ x ∈ l.

  (* There is a list (collecting some circle n) which satisfies ⋀₁P,
     ie which meets P uniformly. We use cover_negative here !!*)
  Local Lemma Q_meets_Forall_P : ∃l, ⋀₁P l ∧ Q l.
  Proof.
    apply cover_negative with (x := [x]) (T := T†).
    + apply FAN_cover; auto.
    + exists 0; intro; rewrite circle_0_spec; simpl; tauto.
    + intros l (n & Hn).
      destruct (circle_finite (S n)) as (m & Hm).
      exists m; split.
      * now exists (S n).
      * intros ? (? & ? & ?%Hn)%Hm%circle_S_spec; eauto.
  Qed.

  (* There is a circle in P *)
  Local Corollary P_contains_some_circle : ∃n, circle n ⊆₁ P.
  Proof.
    destruct Q_meets_Forall_P as (l & H1 & n & H2).
    rewrite Forall_forall in H1.
    exists n.
    intros ? ?%H2; auto.
  Qed.

  (* As a consequence, the paths which do not end in P are those of a finite tree *)
  Theorem konig_cover : ∃t, represents T (λ _ y, ¬ P y) x t.
  Proof.
    apply finitary_represented_iff_bounded; auto.
    destruct P_contains_some_circle as (n & Hn).
    exists n.
    apply short_paths; auto.
    intros p ? ? ?; apply Hn; now exists p.
  Qed.

End konig_cover.

Check konig_cover.

(** The finitary version of König's lemma w/o XM or choice 
    see https://fr.wikipedia.org/wiki/Lemme_de_K%C3%B6nig
    and https://books.google.fr/books?id=N7BvXVUCQk8C&printsec=frontcover&redir_esc=y#v=onepage&q&f=false
*)

Section acc_rel.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x))
            (x : X) (Hx : acc T x).

  Theorem konig_acc : ∃t, root t = x ∧ ∀ p y, branch t p y ↔ path T x p y .
  Proof.
    destruct konig_cover
      with (1 := Tfin) (P := λ _ : X, False) (x := x)
      as (? & []); eauto.
    now apply acc_iff_cover_empty in Hx.
  Qed.

End acc_rel.

Check konig_acc.

Section konig_bar.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x))
            (P : rel₁ (list X)) (Pmono : monotone P)
            (Hr : bar P []).

  (* The circle of center x and of radius n is contained in a list *)
  Local Fact circle_bounded n x : ∃lp, ∀p y, path T x p y → ⌊p⌋ = n → y ∈ lp.
  Proof.
    destruct (circle_finite _ Tfin x n) as (lp & Hlp).
    exists lp.
    intros p y H1 H2; apply Hlp; exists p; auto.
  Qed.

  (* Q x lc if every path from the center x to a point on the circle 
     of radius ⌊lc⌋ is a choice list for lc, ie FAN lc includes all the
     paths from x of length ⌊lc⌋. *)
  Let Q x lc := ∀ p y, path T x p y → ⌊p⌋ = ⌊lc⌋ → FAN lc (rev p).

  (* There is a choice list of P-accepted paths (read reversed) which
     includes all the paths from x of that given length. 
     We use bar_negative here !! *)
  Local Lemma choice_list_in_P_meets_Q x : ∃lc, FAN lc ⊆₁ P ∧ Q x lc.
  Proof.
    apply bar_negative with (Q := Q x).
    + now apply FAN_bar.
    + now intros []; simpl; auto.
    + intros lc Hlc.
      destruct (circle_bounded (1+⌊lc⌋) x) as (l & Hl).
      exists l; intros p.
      destruct p as [ | z p _ ] using rev_ind; try easy.
      rewrite app_length; simpl.
      intros y (u & ? & ? & ->)%path_snoc_inv E.
      rewrite rev_app_distr; simpl; constructor.
      * apply Hl with (p++[y]); auto.
        - apply path_app with u; eauto.
        - now rewrite app_length.
      * red in Hlc; eapply Hlc; eauto; lia.
  Qed.

  (* P contains all the paths from x to points on a circle *)
  Local Corollary P_contains_some_disk x : ∃n, ∀p y, path T x p y → n = ⌊p⌋ → P (rev p).
  Proof.
    destruct (choice_list_in_P_meets_Q x) as (lc & H & ?).
    exists ⌊lc⌋.
    intros ? ? ? ?; apply H; eauto.
  Qed.

  (* Hence, only short paths can satisfy ¬ P *)
  Theorem konig_bar x : ∃t, represents T (λ p _, ¬ P (rev p)) x t.
  Proof.
    apply finitary_represented_iff_bounded; auto.
    destruct (P_contains_some_disk x) as (n & Hn).
    exists n.
    apply short_paths; auto.
    intros; rewrite rev_app_distr; simpl; auto.
  Qed.

End konig_bar.

Check konig_bar.

(** Conclude with almost full relations and irredundant sequences *)

Notation "R ↑ u" := (λ x y, R x y ∨ R u x) (at level 1, left associativity, format "R ↑ u").

Section good_irred.

  (* FO characterization of good, there is an equivalent inductive one
     irred stands for irredundant *) 

  Variable (X : Type).

  Implicit Type (R : rel₂ X).

  Definition good R p := ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Definition irred R p := ∀ l x m y r, p = l++x::m++y::r → R x y → False.

  Fact good_monotone R x p : good R p → good R (x::p).
  Proof. intros (l & u & m & v & r & -> & ?); exists (x::l), u, m, v, r; auto. Qed.

  Hint Resolve good_monotone : core.

  Fact good_app_left R l m : good R m → good R (l++m).
  Proof. induction l; simpl; eauto. Qed.

  (* good R [α_{n-1};...;α₀] iff R α_i α_j for some i < j < n 
     remember the pfx grows from the left *)
  Fact good_pfx_iff R α n : good R (pfx α n) ↔ ∃ i j, i < j < n ∧ R (α i) (α j).
  Proof.
    split.
    + intros (l & x & m & y & r & E & ?).
      symmetry in E.
      generalize E; intros F.
      apply f_equal with (f := length) in F.
      rewrite pfx_length in F.
      repeat (rewrite app_length in F; simpl in F).
      apply pfx_split in E as (E1 & E2); simpl in E2.
      apply cons_inj in E2 as (-> & E2).
      apply pfx_split in E2 as (E2 & E3); simpl in E3.
      apply cons_inj in E3 as (-> & E3).
      exists ⌊r⌋, ⌊m ++ α ⌊r⌋ :: r⌋; split; auto.
      rewrite app_length; simpl; lia.
    + intros (i & j & H1 & H2).
      exists (pfx (λ a, α (a+(1+j))) (n-j-1)), (α j),
             (pfx (λ a, α (a+(1+i))) (j-i-1)), (α i),
             (pfx α i); split; trivial.
      rewrite <- pfx_fix, <- pfx_add.
      replace (j-i-1+(1+i)) with j by lia.
      rewrite <- pfx_fix, <- pfx_add.
      f_equal; lia.
  Qed.

  (* irredundant lists are (reversed) bad lists *)
  Fact not_good_iff_irred R p : ¬ good R (rev p) ↔ irred R p.
  Proof.
    unfold good, irred; split.
    + intros H l x m y r ? ?; apply H; exists (rev r), y, (rev m), x, (rev l).
      subst; repeat (rewrite rev_app_distr; simpl); repeat rewrite <- app_assoc; auto.
    + intros H (l & x & m & y & r & H1%(f_equal (@rev _)) & H2).
      revert H1.
      rewrite rev_involutive.
      repeat (rewrite rev_app_distr; simpl); repeat rewrite <- app_assoc.
      simpl; eauto.
  Qed.

  Fact good_lift R u p : good R↑u p → good R (p++[u]).
  Proof.
    intros (l & x & m & y & r & -> & []);
      repeat (rewrite <- app_assoc; simpl).
    + exists l, x, m, y, (r++[u]); auto.
    + exists (l++x::m), y, r, u, [].
      now repeat (rewrite <- app_assoc; simpl).
  Qed.

  Hint Resolve good_lift : core.

  (** The generalization is bar (good R↑xₙ...↑x₁) p → bar (good R) (p++[x₁;...;xₙ]) *)
  Lemma bar_good_lift R p u : bar (good R↑u) p → bar (good R) (p++[u]).
  Proof. induction 1; eauto. Qed.

End good_irred.

Arguments good {X}.
Arguments irred {X}.

Section af.

  Variables (X : Type).

  Implicit Type (R : rel₂ X).

  Inductive af R : Prop :=
    | af_full : (∀ x y, R x y) → af R
    | af_lift : (∀u, af R↑u) → af R.

  Hint Constructors af : core.

  Hint Resolve bar_good_lift : core.

  Lemma af__bar_good_nil R : af R → bar (good R) [].
  Proof.
    induction 1; eauto.
    + constructor 2; intro x.
      constructor 2; intro y.
      constructor 1.
      exists [], y, [], x, []; auto.
    + constructor 2; intro.
      apply bar_good_lift with (p := []); auto.
  Qed.

  Lemma af_sequences R : af R → ∀α, ∃ i j, i < j ∧ R (α i) (α j).
  Proof.
    intros ?%af__bar_good_nil α.
    destruct (bar_sequences H α)
      as (n & (i & j & [] & ?)%good_pfx_iff); eauto.
  Qed.

End af.

Arguments af {X}.

#[local] Hint Constructors af : core.

Section choice_list.

  Variable (X : Type).

  (** A fixpoint specification equivalent to

       choice_list P [x₀;...;xₙ] = P 0 x₀ ∧ ... ∧ P n xₙ 

      which is a generalization of Forall2, 
      see choice_list_iff below. *)

  Implicit Type (P Q : nat → rel₁ X).

  Fixpoint choice_list P l :=
    match l with 
    | []   => True
    | x::l => P 0 x ∧ choice_list (λ n, P (1+n)) l
    end.

  Fact choice_list_mono P Q : P ⊆₂ Q → choice_list P ⊆₁ choice_list Q.
  Proof.
    intros H l; revert P Q H.
    induction l as [ | x l IHl ]; intros P Q H; simpl; auto.
    intros (? & HP); split; auto.
    revert HP; apply IHl; auto.
  Qed.

  Fact choice_list_app P l m : choice_list P (l++m) ↔ choice_list P l ∧ choice_list (λ n, P (⌊l⌋+n)) m.
  Proof.
    induction l as [ | x l IHl ] in P |- *; simpl; try easy.
    rewrite IHl; tauto.
  Qed.

  Fact choice_list_snoc P l x :  choice_list P (l++[x]) ↔ choice_list P l ∧ P ⌊l⌋ x.
  Proof.
    rewrite choice_list_app; simpl.
    rewrite Nat.add_0_r; tauto.
  Qed.

  (* Computes the list [0+a;...;n-1+a] *)
  Fixpoint list_an a n :=
    match n with
    | 0   => []
    | S n => a :: list_an (1+a) n
    end.

  (* Computes the list [0;...;n-1] *)
  Definition list_n := list_an 0.

  Lemma choice_list_charac P l a : choice_list (λ n, P (a+n)) l ↔ ⋀₂P (list_an a ⌊l⌋) l.
  Proof.
    induction l as [ | x l IHl ] in a |- *; simpl.
    + split; auto.
    + rewrite Forall2_cons_iff.
      rewrite Nat.add_0_r.
      apply and_iff_compat_l.
      rewrite <- IHl.
      split; apply choice_list_mono.
      all: intros ? ?; rewrite Nat.add_succ_r; auto.
  Qed.

  Corollary choice_list_iff P l : choice_list P l ↔ ⋀₂P (list_n ⌊l⌋) l.
  Proof. apply choice_list_charac with (a := 0). Qed.

End choice_list.

Fact double_choice_list X Y (P : nat → rel₁ X) (Q : nat → rel₁ Y) (R : X → Y → Prop) :
    (∀n x y, P n x → Q n y → R x y)
  → ∀ l m, ⌊l⌋ = ⌊m⌋ → choice_list P l → choice_list Q m → ⋀₂R l m.
Proof.
  intros H l m E H1%choice_list_iff%Forall2_swap H2%choice_list_iff.
  rewrite E in H1.
  generalize (Forall2_compose H1 H2).
  apply Forall2_mono.
  intros ? ? (? & []); eauto.
Qed.

Section af_konig_choice.

  Variables (X : Type) (R : rel₂ X) (afR : af R)
            (P : nat → rel₁ X) (finP : ∀n, finite (P n)).

  (* we apply the FAN theorem for bars *)
  Local Lemma bar_good_FAN : bar (λ lc, FAN lc ⊆₁ good R) [].
  Proof.
    apply FAN_bar.
    + apply good_monotone.
    + now apply af__bar_good_nil.
  Qed.

  (* the support n l if l is a supporting list for P n,
     ie support n are the lists l which witness that P n is finite *)
  Local Definition support n l := ∀x, P n x ↔ x ∈ l.

  (* We use bar_negative apply to  bar (λ lc, FAN lc ⊆₁ good R) []
     with Q := λ lc, choice_list support (rev lc), ie, 
     lc is [lₙ;...;l₀] with lₙ support of P 0, ... l₀ support of P n 
     Then Q meets λ lc, FAN lc ⊆₁ good R, ie there is a sequence lc
     of supports for P 0, ... , P n such than any choice sequence
     in those supports in good R. 

     As a consequence, any choice list for P of length ⌊lc⌋ is good R *)
  Local Lemma good_uniform_over_FAN : ∃n, ∀l, choice_list P l → ⌊l⌋ = n → good R (rev l).
  Proof.
    destruct (bar_negative bar_good_FAN)
      with (Q := λ lc, choice_list support (rev lc))
      as (lc & H1 & H2).
    + now simpl.
    + intros l Hl.
      destruct (finP ⌊l⌋) as (lc & Hlc).
      exists lc; simpl.
      rewrite choice_list_snoc, rev_length; auto.
    + exists ⌊lc⌋.
      intros l; pattern l; revert l; apply list_rev_forall.
      intros l.
      rewrite rev_involutive, <- (rev_length lc).
      intros H3 H4.
      apply H1, Forall2_rev_iff; clear H1.
      revert H3 H2; apply double_choice_list; auto.
      intros n x y H1 H2; now apply H2.
  Qed.

  (* So good R is met uniformly at length n over choice lists for P,
     irredundant choice lists must be shorter than n *) 
  Theorem af_konig_choice : ∃n, ∀l, choice_list P l → irred R l → ⌊l⌋ < n.
  Proof.
    destruct good_uniform_over_FAN as (n & Hn).
    exists n; intros l H1 H2%not_good_iff_irred.
    destruct (le_lt_dec n ⌊l⌋) as [ H | ]; auto.
    destruct H2.
    destruct (list_length_split l n (⌊l⌋-n)) as (l1 & l2 & -> & E & _); try lia.
    apply choice_list_app in H1 as (H1 & _).
    rewrite rev_app_distr.
    apply good_app_left; eauto.
  Qed.

End af_konig_choice.

Check af_konig_choice.
