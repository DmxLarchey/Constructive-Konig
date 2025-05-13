(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Arith Lia Permutation Utf8.

Import ListNotations.

Set Implicit Arguments.

(** Notations for Base based logical connectives, see below *)

#[local] Reserved Notation "⊥ₜ" (at level 0).
#[local] Reserved Notation "x '∨ₜ' y" (at level 80, right associativity).
#[local] Reserved Notation "x '∧ₜ' y" (at level 80, right associativity).
#[local] Reserved Notation "P '⇄ₜ' Q" (at level 95, no associativity).
#[local] Reserved Notation "'∃ₜ' x .. y , p" (at level 200, x binder, right associativity).

#[local] Reserved Notation "x ∈ₜ l" (at level 70, no associativity, format "x  ∈ₜ  l").
#[local] Reserved Notation "l ~ₜ m" (at level 70, no associativity, format "l  ~ₜ  m").

(** Choice of the Base sort, either Base := Prop or Base := Type *)

(* Base := Type based implementation of connectives *)

Module Base_is_Type.

  Notation Base := Type (only parsing).
  Notation Absurd := Empty_set (only parsing).
  Notation DepSum := sigT (only parsing).
  Notation NonDepSum := sum (only parsing).
  Notation NonDepProd := prod (only parsing).

End Base_is_Type.

(* Base := Prop based implementation of connectives *)

Module Base_is_Prop.

  Notation Base := Prop (only parsing).
  Notation Absurd := False (only parsing).
  Notation DepSum := ex (only parsing).
  Notation NonDepSum := or (only parsing).
  Notation NonDepProd := and (only parsing).

End Base_is_Prop.

(** Here is the point where the choice is actually performed *)
Import Base_is_Type.

(* The alternate choice could be "Import Base_is_Prop" but some
   proofs below are specific/simpler in the Base := Type case *)

#[local] Notation "⊥ₜ" := Absurd (only parsing) : type_scope.
#[local] Notation "x ∨ₜ y" := (NonDepSum x y) (only parsing) : type_scope.
#[local] Notation "x ∧ₜ y" := (NonDepProd x y) (only parsing) : type_scope.
#[local] Notation "∃ₜ x .. y , p" := (DepSum (fun x => .. (DepSum (fun y => p)) ..)) (only parsing) : type_scope.
#[local] Notation "P ⇄ₜ Q" := ((P → Q) ∧ₜ (Q → P))%type (only parsing) : type_scope.

(* False and True propositions *)
#[local] Notation "⊤" := True.
#[local] Notation "⊥" := False.

(* Finitary conjunction over: ⋀₁P a list, or ⋀₂R a pair of lists *)
#[local] Notation "⋀₁ P" := (Forall P)  (at level 0, right associativity, format "⋀₁ P").
#[local] Notation "⋀₂ R" := (Forall2 R) (at level 0, right associativity, format "⋀₂ R").

(* Notations for homogeneous unary and binary relations *)
#[local] Notation rel₁ X := (X → Prop).
#[local] Notation rel₂ X := (X → X → Prop).

(* Inclusion for relations and the converse relation *)
#[local] Notation "P ⊆₁ Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[local] Notation "R ⊆₂ T" := (∀ x y, R x y → T x y) (at level 70, no associativity, format "R  ⊆₂  T").
#[local] Notation "R ⁻¹" := (λ x y, R y x) (at level 1, left associativity, format "R ⁻¹").

Arguments In {_}.
Arguments length {_}.
Arguments cons {_}.

(* Usual notations for length, membership and permutations *)
#[local] Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").
#[local] Notation "x ∈ l" := (In x l) (at level 70, no associativity, format "x  ∈  l").
#[local] Notation "l ~ₚ m" := (@Permutation _ l m) (at level 70, no associativity, format "l  ~ₚ  m").

(* Usual hints for membership, inclusion of lists and permutations *)
#[local] Hint Resolve in_eq in_cons in_or_app incl_refl incl_tl : core.
#[local] Hint Constructors Permutation : core.
#[local] Hint Resolve Permutation_middle Permutation_cons_app Permutation_in Permutation_sym : core.

(** Utilities: notice that some of the facts below might exist, possibly under
    a different name, in the Coq standard library but they might not exist
    as such in every version of the StdLib from 8.14 to 8.20, hence they are
    possibly (re)proved here. *)

(** List utilities *)

Section In_Base.

  Variables (X : Type).

  Implicit Type (x : X).

  Fixpoint In_Base x l : Base :=
    match l with
    | []   => ⊥ₜ
    | y::l => y = x ∨ₜ x ∈ₜ l
    end
  where "x ∈ₜ l" := (In_Base x l).

  Fact In_iff_inhabited_In_Base x l : x ∈ l ↔ inhabited (x ∈ₜ l).
  Proof. 
    split.
    + induction l as [ | y l IH ].
      * now simpl.
      * intros [ | []%IH ]; simpl; constructor; auto.
    + intros [H]; revert H.
      induction l; simpl; intros []; subst; auto. 
  Qed.
   
  Fact In_Base_eq x l : x ∈ₜ x::l.
  Proof. now left. Qed.
  
  Fact In_Base_cons x y l : y ∈ₜ l → y ∈ₜ x::l.
  Proof. now right. Qed.

  Fact In_Base_app_iff x l m : x ∈ₜ l++m ⇄ₜ x ∈ₜ l ∨ₜ x ∈ₜ m.
  Proof.
    split.
    + induction l as [ | y l IH ]; simpl; auto.
      intros [ | []%IH ]; eauto.
    + intros [ H | H ]; revert H.
      * induction l as [ | y l IH ]; simpl; intros []; eauto.
      * induction l; simpl; eauto.
  Qed.

End In_Base.

#[local] Notation "x ∈ₜ l" := (@In_Base _ x l) (only parsing) : type_scope.
#[local] Hint Resolve In_Base_eq In_Base_cons : core.

Section Permutation_Base.

  Variables (X : Type).

  Inductive Permutation_Base : list X → list X → Base :=
    | permb_nil  : [] ~ₜ []
    | permb_skip x l m : l ~ₜ m → x::l ~ₜ x::m
    | permb_swap x y l : y::x::l ~ₜ x::y:: l
    | permb_trans l m k :  l ~ₜ m → m ~ₜ k → l ~ₜ k
  where "l ~ₜ m" := (Permutation_Base l m).
  
  Hint Constructors Permutation_Base inhabited : core.

  Fact Permutation_iff_inhabited_Permutation_Base l m : l ~ₚ m ↔ inhabited (l ~ₜ m).
  Proof.
    split.
    + induction 1 as [ | ? ? ? _ [] | | ? ? ? _ [] _ [] ]; eauto.
    + intros [H]; revert H; induction 1; eauto.
  Qed.

  Fact Permutation_Base_refl l : l ~ₜ l.
  Proof. induction l; simpl; auto. Qed.

  Fact Permutation_Base_sym l m : l ~ₜ m → m ~ₜ l.
  Proof. induction 1; eauto. Qed.
  
  Hint Resolve Permutation_Base_refl : core.

  Fact Permutation_Base_middle l m x : x::l++m ~ₜ l++x::m.
  Proof.
    induction l; simpl; auto.
    apply permb_trans with (1 := permb_swap _ _ _); auto.
  Qed.

  Hint Resolve Permutation_Base_middle : core.

  Fact Permutation_Base_cons_app l m k x : l ~ₜ m++k → x::l ~ₜ m++x::k.
  Proof. eauto. Qed.

  Fact Permutation_Base_In_Base l m x : l ~ₜ m → x ∈ₜ l → x ∈ₜ m.
  Proof.
    induction 1; simpl; eauto.
    + intros []; auto.
    + intros [ | [] ]; auto.
  Qed.

End Permutation_Base.

#[local] Notation "l ~ₜ m" := (@Permutation_Base _ l m).
#[local] Hint Constructors Permutation_Base : core.

#[local] Hint Resolve Permutation_Base_refl
                      Permutation_Base_sym 
                      Permutation_Base_cons_app
                      Permutation_Base_In_Base : core. 

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

Fact Forall_forall_In_Base X (P : rel₁ X) l : ⋀₁P l ↔ ∀x, x ∈ₜ l → P x.
Proof.
  split.
  + induction 1; simpl; intros ? []; subst; auto.
  + induction l; simpl; auto.
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

Fact forall_ex_Forall2_Base X Y (R : X → Y → Prop) l : (∀x, x ∈ₜ l → ∃ₜ y, R x y) → ∃ₜ m, ⋀₂R l m.
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
Proof. split; inversion 1; eauto. Qed.

(* Forall2 swap *)
Fact Forall2_swap X Y (R : X → Y → Prop) l m : ⋀₂R l m ↔ ⋀₂(R⁻¹) m l.
Proof. split; induction 1; eauto. Qed.

(* Forall2 and rev(erse) *)
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
  induction 1 in p |- *.
  + intros ->%Forall2_nil_left_inv; auto.
  + intros (? & ? & -> & [])%Forall2_cons_left_inv; eauto.
Qed.

(** The three below definitions of accessibility are the same:
      - founded 
      - acc 
      - Acc
    apart from the orientation of the relation 
    or from superfluous premises. *)

Inductive acc {X} (R : X → X → Base) x : Base :=
  | acc_intro : (∀y, R x y → acc R y) → acc R x.

Fact acc_irrefl X (R : rel₂ X) x : acc R x → ¬ R x x.
Proof. unfold not; induction 1; eauto. Qed.

(** This is the notion "R-founded" defined in [SC], Definition 3.1 p 74

    [SC] Claudio Sacerdoti Coen and Silvio Valentini. "General Recursion and Formal Topology." 
         PAR-10. Partiality and Recursion in Interactive Theorem Provers, volume 5 of 
         EPiC Series in Computing, pages 72–83. EasyChair, 2012. doi:10.29007/hl75. *)

Inductive founded {X} (R : X → X → Base) x : Base :=
  | founded_intro : ¬ R x x → (∀y, R x y → founded R y) → founded R x.

(* This is Coq standard definition of Acc R (ported to Base)
   which uses the reversed relation as compared to acc R *)

Inductive Acc {X} (R : X → X → Base) x : Base :=
  | Acc_intro : (∀y, R y x → Acc R y) → Acc R x.

Section founded_vs_acc_vs_Acc.

  Variables (X : Type).

  Implicit Type (R : rel₂ X).

  Hint Constructors acc founded Acc : core.

  Fact founded_iff_acc R x : founded R x ⇄ₜ acc R x.
  Proof.
    split.
    + induction 1; auto.
    + induction 1; eauto.
      constructor; auto.
      now intros ?%acc_irrefl.
  Qed.

  Remark Acc_rev_iff_acc R x : Acc R⁻¹ x ⇄ₜ acc R x.
  Proof. split; induction 1; eauto. Qed.

  Remark acc_rev_iff_Acc R x : acc R⁻¹ x ⇄ₜ Acc R x.
  Proof. split; apply Acc_rev_iff_acc. Qed.

End founded_vs_acc_vs_Acc.

(** The notion of being upward closed for T *)

#[local] Notation upclosed T P := (∀ x y, T x y → P x → P y).

Fact Forall_upclosed_perm X (P : rel₁ X) : upclosed (λ l m, l ~ₜ m) ⋀₁P.
Proof. intros ? ? ?; rewrite !Forall_forall_In_Base; eauto. Qed.

(** The cover inductive predicate is given by two rules *)

Unset Elimination Schemes.

Inductive cover	{X} (T : X → X → Base) (P : rel₁ X) x : Base :=
  | cover_stop : P x → cover T P x
  | cover_next : (∀y, T x y → cover T P y) → cover T P x.

Set Elimination Schemes.

#[local] Hint Constructors cover : core.

Arguments cover_stop {_ _ _ _}.
Arguments cover_next {_ _ _ _}.

Section cover_rect.

  (* This one is usually auto-generated by Coq
     (but "Unset Elimination Schemes" prevents that)
     So let us review the code here. *)

  Variables (X : Type)
            (T : X → X → Base)
            (P : rel₁ X)
            (Q : X → Base)
            (Qs : P ⊆₁ Q)
            (Qn : ∀y, T y ⊆₁ Q → Q y).

  Fixpoint cover_rect x (d : cover T P x) : Q x :=
    match d with
    | cover_stop p => Qs p
    | cover_next n => Qn (λ y hy, cover_rect (n y hy))
    end.

End cover_rect.

Definition cover_ind X T P (Q : X → Prop) := @cover_rect X T P Q.

Section cover_morphism.

  (* Transfert of the cover predicate using a morphism *)

  Variables (X Y : Type) (R : X → X → Base) (T : Y → Y → Base)
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

  Implicit Type (R T : X → X → Base) (P Q : rel₁ X) (K : X → Base).

  (* cover T P is antitonic in T and monotonic in P *)
  Fact cover_mono R T P Q : T ⊆₂ R → P ⊆₁ Q → cover R P ⊆₁ cover T Q.
  Proof. intros ? ? ?; now apply cover_morphism with (f := λ x, x). Qed.

  (* It preserves upward closed predicates *)
  Fact cover_upclosed T P : upclosed T P → upclosed T (cover T P).
  Proof. intros ? ? y H2 H3; revert H3 y H2; induction 1; eauto. Qed.

  (*
  Fact cover_idempotent T P : cover T (cover T P) ⊆₁ cover T P.
  Proof. induction 1; eauto. Qed.
  *)

  Hint Constructors acc : core.

  (* The cover inductive predicate subsumes the acc(essibility) predicate *)
  Theorem acc_iff_cover_empty T x : acc T x ⇄ₜ cover T (λ _, ⊥) x.
  Proof. split; induction 1; now eauto. Qed.

  (* Positive characterization of cover T P x is ∀K, cover_pos T P x K *)
  Definition cover_pos T P x := λ K, P ⊆₁ K → (∀y, T y ⊆₁ K → K y) → K x.

  (* The positive characterization is just a reformulation 
     of the inductive principle cover_ind for cover T P x,
     obtained by reordering the hypotheses. *)
  Fact cover_iff_cover_pos T P x : cover T P x ⇄ₜ ∀K, cover_pos T P x K.
  Proof.
    split.
    + intros Hx Q HQ0 HQ1; revert X T P Q HQ0 HQ1 x Hx; exact cover_rect.
    + intros H; apply H; auto.
  Qed.

  (* The negative characterization of cover T P x is ∀K, cover_neg T P x K

     This characterization reads as: if a predicate Q is such that
       - K contains x
       - K is T-unstoppable
     then K meets P *)
  Definition cover_neg T P x := λ K, K x → (∀y, K y → ∃ₜ z, K z ∧ₜ T y z) → ∃ₜ y, P y ∧ₜ K y.

  (* The positive characterization implies the negative characterization *)
  Lemma cover_pos__cover_neg T P x : (∀K, cover_pos T P x K) → ∀K, cover_neg T P x K.
  Proof.
    unfold cover_neg.
    intros H.
    apply H; clear x H.
    + intros x; now exists x.
    + intros x IH Q H1 H2.
      destruct (H2 _ H1) as (? & []); eauto.
  Qed.

  Theorem cover_negative T P x : cover T P x → ∀K, K x → (∀y, K y → ∃ₜ z, K z ∧ₜ T y z) → ∃ₜ y, P y ∧ₜ K y.
  Proof. intro; now apply cover_pos__cover_neg, cover_iff_cover_pos. Qed.

  (* The sequential characterization of cover T P x is ∀ρ, cover_seq T P x ρ.
     This reads as any T-sequence starting at x meets P *)
  Definition cover_seq T P x := λ ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → ∃ₜ n, P (ρ n).

  (* For a T-sequence ρ starting at x, its direct image 
     Q := λ x, ∃ₜ n, x = ρ n, satisfies
       - Q contains x
       - Q is T-unstoppable
     Hence Q meets P, which entails that ρ meets P *)
  Lemma cover_seq_direct_image T P x ρ : cover_neg T P x (λ x, ∃ₜ n, x = ρ n) → cover_seq T P x ρ.
  Proof. 
    intros H H1 H2.
    destruct H as (? & ? & ? & ->); eauto.
    intros ? (? & ->); eauto.
  Qed.

  Corollary cover_neg__cover_seq T P x : (∀K, cover_neg T P x K) → ∀ρ, cover_seq T P x ρ.
  Proof. intros H ρ; apply cover_seq_direct_image, H. Qed.

  Theorem cover_sequences T P x : cover T P x → ∀ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → ∃ₜ n, P (ρ n).
  Proof. intro; apply cover_neg__cover_seq; unfold cover_neg; now apply cover_negative. Qed.

  Section cover_seq__cover_neg__only_when_Base_is_Type.
  
    (** When Base is Type, we do not need dependent choice *)
  
    Variables (T : X → X → Base) (P : rel₁ X) (x : X) (Hx : ∀ρ, cover_seq T P x ρ)
              (K : X → Type) (HK1 : K x) (HK2 : ∀y, K y → { z : X & K z * T y z }%type).

    Let f : sigT K → sigT K.
    Proof.
      intros (y & hy).
      destruct (@HK2 _ hy) as (z & H1 & H2).
      now exists z.
    Defined.
 
    Local Fact f_T y : T (projT1 y) (projT1 (f y)).
    Proof.
      unfold f; destruct y as (y & hy).
      now destruct (@HK2 _ hy) as (? & []).
    Qed.

    Let rho := @nat_rect (fun _ => sigT K) (existT _ x HK1) (fun _ => f).
    Let ρ n := projT1 (rho n).
    
    Lemma cover_seq__cover_neg__Base_is_Type : { y : X & P y * K y }%type.
    Proof.
      destruct (Hx ρ) as (n & Hn).
      + reflexivity.
      + intro; apply f_T.
      + exists (ρ n); split; auto.
        apply (projT2 _).
    Qed.

  End cover_seq__cover_neg__only_when_Base_is_Type.
  
  Theorem cover_neg_iff_cover_seq__Base_is_Type T P x : (∀K, cover_neg T P x K) ⇄ₜ ∀ρ, cover_seq T P x ρ.
  Proof.
    split.
    + apply cover_neg__cover_seq.
    + exact (@cover_seq__cover_neg__Base_is_Type T P x).
  Qed.

End cover_extra.

(** acc inductive predicate specializations *)

Section acc_instances.

  Variables (X : Type) (R : rel₂ X).

  Implicit Types (K : X → Base) (ρ : nat → X).

  Lemma acc_negative x : acc R x → ∀K, K x → (∀y, K y → ∃ₜ z, K z ∧ₜ R y z) → ⊥.
  Proof.
    intros H%acc_iff_cover_empty Q H1 H2.
    now destruct (cover_negative H _ H1 H2) as (? & []).
  Qed.

  Lemma acc_sequences x : acc R x → ∀ρ, ρ 0 = x → (∀n, R (ρ n) (ρ (S n))) → ⊥.
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

Definition fimage {X} (T : X → X → Base) l m := ∀y, y ∈ₜ m → ∃ₜ x, x ∈ₜ l ∧ₜ T x y.

#[local] Notation "T †" := (fimage T) (at level 1, left associativity, format "T †").

Notation inclₜ l m := (∀x, x ∈ₜ l → x ∈ₜ m).

Section finitary_image.

  Variable (X : Type) (T : X → X → Base).

  Implicit Type (l : list X) (P : rel₁ X).

  Fact fimage_mono l₁ l₂ m₁ m₂ : inclₜ l₁ l₂ → inclₜ m₂ m₁ → T† l₁ m₁ → T† l₂ m₂.
  Proof. intros ? ? H y ?; destruct (H y) as (? & []); eauto. Qed.

  Fact fimage_in_r_inv l m : T† l m → ∀y, y ∈ₜ m → T† l [y].
  Proof. intros ? ? ? ? [ <- | [] ]; eauto. Qed.

  Fact fimage_sg_inv x y : T† [x] [y] → T x y.
  Proof. intros H; destruct (H y) as (? & [ <- | [] ] & ?); auto. Qed.

  Fact fimage_sg_r l x y : T x y → x ∈ₜ l → T† l [y].
  Proof. intros ? ? ? [ <- | [] ]; eauto. Qed.

  Hint Resolve fimage_sg_inv fimage_in_r_inv : core.

  Fact fimage_sg_l_inv x m : T† [x] m → ∀y, y ∈ₜ m → T x y.
  Proof. eauto. Qed.

  (* The critical lemma explaining how finite images interact with splitting *)
  Lemma fimage_split_inv l₁ l₂ m : T† (l₁++l₂) m → ∃ₜ m₁ m₂, m ~ₜ m₁++m₂ ∧ₜ T† l₁ m₁ ∧ₜ T† l₂ m₂.
  Proof.
    induction m as [ | x m IHm ]; intros H1.
    + exists nil, nil; repeat split; auto; intros ? [].
    + destruct IHm as (m1 & m2 & H3 & H4 & H5).
      * intros ? ?; apply H1; right; auto.
      * destruct (H1 x) as (y & []%In_Base_app_iff & H7); auto.
        - exists (x::m1), m2; repeat split; simpl; eauto.
          intros ? [ <- | ]; eauto.
        - exists m1, (x::m2); repeat split; auto.
          intros ? [ <- | ]; eauto.
  Qed.

  Fact fimage_upclosed_perm_left k : upclosed (λ l m, l ~ₜ m) (λ l, T† l k).
  Proof. intros ? ? ? H ? (? & [])%H; eauto. Qed.

  Fact Forall_upclosed_fimage P : upclosed T P → upclosed T† ⋀₁P.
  Proof.
    intros ? ? ? H; do 2 rewrite Forall_forall_In_Base.
    intros ? ? (? & [])%H; eauto.
  Qed.

End finitary_image.

Section FAN_cover.

  (** We give an original proof of a quite general formulation of
      the FAN theorem for cover inductive predicates. *)

  Variables (X : Type) (T : X → X → Base) (P : rel₁ X) (HP : upclosed T P).

  Hint Resolve fimage_upclosed_perm_left Forall_upclosed_fimage Forall_upclosed_perm cover_upclosed : core.

  Fact cover_fimage_Forall_upclosed_perm : upclosed (λ l m, l ~ₜ m) (cover T† ⋀₁P).
  Proof. intros l m H1 H2; revert H2 m H1; induction 1; eauto. Qed.

  Hint Resolve fimage_sg_r : core.

  Hint Resolve cover_fimage_Forall_upclosed_perm : core.

  (* The key lemma: the T†-cover of ⋀₁P is stable under binary union *)
  Lemma cover_fimage_union l r : cover T† ⋀₁P l → cover T† ⋀₁P r → cover T† ⋀₁P (l++r).
  Proof.
    induction 1 as [ l Hl | ] in r |- *.
    + induction 1 in l, Hl |- *; eauto.
      * constructor 1; apply Forall_app; eauto.
      * constructor 2; intros ? (? & ? & ?%Permutation_Base_sym & [])%fimage_split_inv; eauto.
    + constructor 2; intros ? (? & ? & ?%Permutation_Base_sym & [])%fimage_split_inv; eauto.
  Qed.

  Corollary cover_fimage_Forall_cons x m : cover T† ⋀₁P [x] → cover T† ⋀₁P m → cover T† ⋀₁P (x::m).
  Proof. apply cover_fimage_union with (l := [_]). Qed.

  Hint Resolve fimage_mono
               fimage_in_r_inv
               cover_fimage_Forall_cons : core.

  Corollary cover_fimage_Forall l : (∀x, x ∈ₜ l → cover T† ⋀₁P [x]) → cover T† ⋀₁P l.
  Proof. induction l; simpl; intro; eauto; apply cover_fimage_Forall_cons; eauto. Qed.

  (* If x is in the T-cover of P then [x] is in the T†-cover of ⋀₁P
     hence P will be satisfied uniformly over all the iterates of
     the direct images of x, provided we only allow finitely
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

  Theorem FAN_cover_many l : (∀x, x ∈ₜ l → cover T P x) → cover T† ⋀₁P l.
  Proof. intros Hl; apply cover_fimage_Forall; eauto. Qed.
 
  (** This characterization looks like the characterization
      of Accessibility wrt. to e.g. list ordering, such as

      https://github.com/DmxLarchey/Hydra/blob/a387860ba85490cd925c4488ab2f5b3e8fddbbcf/theories/hydra.v#L222

      Remark by DLW: remains to be further investigated,
        could Acc_lo_iff be derived from cover_fimage_iff below ? *)

  Fact cover_fimage_Forall_Forall l : cover T† ⋀₁P l → ∀x, x ∈ₜ l → cover T P x.
  Proof. 
    induction 1 as [ l Hl | ]; eauto.
    rewrite Forall_forall_In_Base in Hl; eauto.
  Qed.

  Hint Resolve FAN_cover_many cover_fimage_Forall_Forall : core.

  Theorem cover_fimage_iff l : cover T† ⋀₁P l ⇄ₜ ∀x, x ∈ₜ l → cover T P x.
  Proof. split; auto; apply cover_fimage_Forall_Forall. Qed.

End FAN_cover.

(** The (reverse) n-prefixes of sequences
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

(** the extends relation between lists *)

Section extends.

  Variable (X : Type).

  Implicit Type (l : list X).

  Inductive extends l : list X → Base :=
    | extends_intro x : extends l (x::l).

  Hint Constructors extends : core.

  Fact extends_inv (l m : list X) :
      extends l m
    → match m with
      | []   => ⊥
      | _::m => l = m
      end.
  Proof. now induction 1. Qed.

  Fact extends_iff l m : extends l m ⇄ₜ ∃ₜ x, m = x::l.
  Proof.
    split.
    + induction 1; eauto.
    + intros (? & ->); auto.
  Qed.

  Fact hd_extends l m : extends l m → { x | m = x::l }.
  Proof. revert m; intros [] []%extends_inv; eauto. Qed.

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
  Fact pfx_extends (ρ : nat → X) : pfx ρ 0 = [] ∧ₜ ∀n, extends (pfx ρ n) (pfx ρ (S n)).
  Proof. split; constructor. Qed.

End extends.

Arguments extends {X}.

#[local] Hint Constructors extends : core.

(** cover inductive predicate specialized to lists are bar inductive predicates *)

(* Monotone predicates on lists *)
#[local] Notation monotone P := (∀x l, P l → P (x::l)).

Section bar.

  Variables (X : Type).

  Implicit Type (P Q : rel₁ (list X)) (l : list X) (K : list X → Base).

  (* Monotone is just an instance of upward-closed *)
  Fact upclosed_extends_iff_monotone K : upclosed extends K ⇄ₜ monotone K.
  Proof.
    split.
    + intros H ? ?; apply H; constructor.
    + induction 2; auto.
  Qed.

  Inductive bar P l : Base :=
    | bar_stop : P l → bar P l
    | bar_next : (∀x, bar P (x::l)) → bar P l.

  Hint Constructors bar : core.

  Fact bar_iff_cover_extends P l : bar P l ⇄ₜ cover extends P l.
  Proof.
    split.
    + induction 1; eauto.
      constructor 2; induction 1; auto.
    + induction 1; eauto.
  Qed.

  Fact bar_monotone P : monotone P → monotone (bar P).
  Proof.
    intros H; apply upclosed_extends_iff_monotone.
    generalize (snd (upclosed_extends_iff_monotone P) H). 
    clear H.
    intros H ? ?.
    intros G1 G2%bar_iff_cover_extends; apply bar_iff_cover_extends.
    revert G1 G2; apply (cover_upclosed H).
  Qed.

  Fact bar_mono P Q : P ⊆₁ Q → bar P ⊆₁ bar Q.
  Proof. 
    intros ? ?.
    intros G%bar_iff_cover_extends; apply bar_iff_cover_extends; revert G.
    apply cover_mono; auto.
  Qed.

  Fact bar_negative P : bar P [] → ∀K, K [] → (∀l, K l → ∃ₜ x, K (x::l)) → ∃ₜ l, P l ∧ₜ K l.
  Proof.
    intros H%bar_iff_cover_extends Q H1 H2. 
    apply (cover_negative H); eauto.
    intros ? (? & ?)%H2; eauto.
  Qed.

  Fact bar_sequences P : bar P [] → ∀α, ∃ₜ n, P (pfx α n).
  Proof.
    intros H%bar_iff_cover_extends α.
    destruct cover_sequences
      with (ρ := λ n, pfx α n) (1 := H); eauto.
    constructor.
  Qed.

End bar.

Arguments bar {_}.

#[local] Hint Constructors bar : core.

(** The notion of finiteness defined as listability
    which is equivalent to Kuratowsky finiteness *)

(* P is a finite predicate if it is listable *)
Definition finite {X} (P : rel₁ X) := ∃ₜ l, ∀x, P x ↔ x ∈ l.

(* The carrier of a list is finite, by definition *)
Fact finite_in X (l : list X) : finite (λ x, x ∈ l).
Proof. exists l; tauto. Qed.

#[local] Hint Resolve finite_in : core.

(* The singleton is finite *)
Fact finite_eq X (x : X) : finite (λ y, x = y).
Proof. exists [x]; simpl; tauto. Qed.

(* Equivalent predicates are equi-finite *)
Fact finite_equiv X (P Q : rel₁ X) : (∀x, P x ↔ Q x) → finite Q → finite P.
Proof. intros ? (l & ?); exists l; firstorder. Qed.

(* Composition by a finitary relation *)
Lemma finite_compose X Y (P : rel₁ X) (R : X → Y → Prop) :
        finite P
      → (∀x, P x → finite (R x))
      → finite (λ y, ∃x, R x y ∧ P x).
Proof.
  intros (l & Hl) HR.
  assert (∀x, x ∈ₜ l → finite (R x)) as (m & Hm)%forall_ex_Forall2_Base.
  + intros; apply HR, Hl, In_iff_inhabited_In_Base; auto.
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

Fact FAN_finite X (lc : list (list X)) : finite (FAN lc).
Proof. apply finite_Forall2_rev; eauto. Qed.

(** Construction of the generic product and exponential 
    for lists, ie compute/spec of the list of choice lists,
    ake the concrete FAN is found in D. Fridlender's paper *)
    
Fact In_Base_map X Y (f : X → Y) x l : x ∈ₜ l → f x ∈ₜ map f l.
Proof. induction l; simpl; intros []; subst; eauto. Qed.

#[local] Hint Resolve In_Base_map : core.
#[local] Hint Constructors sum prod : core.

Fact In_Base_map_iff  X Y (f : X → Y) y l : y ∈ₜ map f l ⇄ₜ ∃ₜ x, y = f x ∧ₜ x ∈ₜ l.
Proof.
  split.
  + induction l as [ | ? ? IHl ]; simpl; intros []; subst; eauto.
    destruct IHl as (? & []); subst; eauto.
  + intros (? & -> & ?); eauto.
Qed.

Fact In_Base_flat_map_iff X Y (f : X → list Y) l y : y ∈ₜ flat_map f l ⇄ₜ ∃ₜ x, x ∈ₜ l ∧ₜ y ∈ₜ f x.
Proof.
  split.
  + induction l as [ | x l IHl ]; simpl.
    * intros [].
    * intros [ | (? & [])%IHl ]%In_Base_app_iff; eauto.
  + induction l as [ | x l IHl ]; simpl.
    * now intros (? & []).
    * intros (? & [] & ?); apply In_Base_app_iff; subst; eauto.
Qed.

Section list_prod.

  Variables (X Y Z : Type) (p : X → Y → Z).

  Definition list_prod l m := flat_map (λ x, map (p x) m) l.
  
  Hint Resolve in_map : core.
  
  Fact list_prod_spec l m z : z ∈ list_prod l m ↔ ∃ x y, z = p x y ∧ x ∈ l ∧ y ∈ m.
  Proof.
    unfold list_prod; split.
    + intros (x & H1 & (? & [])%in_map_iff)%in_flat_map; subst; eauto.
    + intros (x & ? & -> & []); apply in_flat_map; eauto.
  Qed.

  Fact list_prod_spec_Base l m z : z ∈ₜ list_prod l m ⇄ₜ ∃ₜ x y, z = p x y ∧ₜ x ∈ₜ l ∧ₜ y ∈ₜ m.
  Proof.
    unfold list_prod; split.
    + intros (x & H1 & (? & [])%In_Base_map_iff)%In_Base_flat_map_iff; subst; eauto.
    + intros (x & ? & -> & []); apply In_Base_flat_map_iff; eauto.
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

  (* list_fan gives an explicit inhabitant of finite (FAN _) *)
  Local Remark list_fan_finite_inhabits lc : finite (FAN lc).
  Proof. exists (list_fan lc); apply list_fan_spec. Qed.

  Fact list_fan_cons_inv c lc l : l ∈ list_fan (c::lc) ↔ ∃ x m, l = x::m ∧ x ∈ c ∧ m ∈ list_fan lc.
  Proof.
    rewrite <- list_fan_spec; split.
    + intros (x & m & ?)%Forall2_cons_right_inv.
      exists x, m; now rewrite <- list_fan_spec.
    + intros (x & m & -> & ? & ?%list_fan_spec); eauto.
  Qed.
  
  Fact list_fan_cons_inv_Base c lc l : l ∈ₜ list_fan (c::lc) ⇄ₜ ∃ₜ x m, l = x::m ∧ₜ x ∈ₜ c ∧ₜ m ∈ₜ list_fan lc.
  Proof.
    split.
    + simpl; intros ?%list_prod_spec_Base; auto.
    + intro; apply list_prod_spec_Base; auto.
  Qed.

  Fact extends_list_fan l m : extends l m → extends† (list_fan l) (list_fan m).
  Proof. intros [] ? (? & ? & -> & [])%list_fan_cons_inv_Base; eauto. Qed.

End list_fan.

Arguments list_fan {_}.

#[local] Hint Resolve extends_list_fan : core.

(** FAN theorem for inductive bars w/o reference to list_fan in its type *)
Theorem FAN_bar X (P : rel₁ (list X)) : monotone P → bar P [] → bar (λ l, FAN l ⊆₁ P) [].
Proof.
  intros HP HB%bar_iff_cover_extends; apply bar_iff_cover_extends.
  apply FAN_cover in HB.
  2: now apply upclosed_extends_iff_monotone.
  revert HB.
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

(** Conclude with almost full relations and irredundant sequences *)

Notation "R ↑ u" := (λ x y, R x y ∨ R u x) (at level 1, left associativity, format "R ↑ u").

Section good_irred.

  (* FO characterization of good (there is an equivalent inductive one)
     irred stands for irredundant *) 

  Variable (X : Type).

  Implicit Type (R : rel₂ X).

  Definition good R p := ∃ l x m y r, p = l++x::m++y::r ∧ R y x.
  Definition irred R p := ∀ l x m y r, p = l++x::m++y::r → R x y → ⊥.

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

  Inductive af R : Base :=
    | af_full : (∀ x y, R x y) → af R
    | af_lift : (∀u, af R↑u) → af R.

  Hint Constructors af : core.

  Hint Resolve bar_good_lift : core.

  (** The generalization is af R↑xₙ...↑x₁ ↔ bar (good R) [x₁;...;xₙ] *)
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
    intros H%af__bar_good_nil α.
    destruct (bar_sequences H α)
      as (n & (i & j & [] & ?)%good_pfx_iff); eauto.
  Qed.

End af.

Arguments af {X}.

#[local] Hint Constructors af : core.

Section choice_list.

  Variable (X : Type).

  (** A fixpoint specification equivalent to

       choice_list P [x₀;...;xₙ] = P₀ x₀ ∧ ... ∧ Pₙ xₙ 

      which is a generalization of Forall2, 
      see choice_list_iff below. *)

  Implicit Type (P Q : nat → rel₁ X).

  Fixpoint choice_list P l :=
    match l with 
    | []   => ⊤
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
  Local Lemma good_uniform_over_FAN : ∃ₜ n, ∀l, choice_list P l → ⌊l⌋ = n → good R (rev l).
  Proof.
    destruct (bar_negative bar_good_FAN)
      with (K := λ lc, choice_list support (rev lc))
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
  Theorem af_konig_choice : ∃ₜ n, ∀l, choice_list P l → irred R l → ⌊l⌋ < n.
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
