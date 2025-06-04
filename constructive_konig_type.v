(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** This is the Type-bounded version of the cover, bar and af predicates
    that carry computational information for the computation of
    the FAN functional. 
    
    We get the following types for cover, bar and af:
    
       cover {X} (T : X → X → Type) (P : X → Prop) (x : X) : Type
       bar {X} (P : list X → Prop) (l : list X) : Type
       af {X} (R : X → X → Prop) : Type
    
    The sequential interpretation now look like:
    
     cover_sequences: cover T P x → ∀ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → { n | P ρₙ }.
     bar_sequences: bar P [] → ∀α, { n | P [αₙ₋₁;...;α₀] }.
     af_sequences: af R → ∀α, { n | ∃ i j, i < j < n ∧ R αᵢ αⱼ }
     
    and we see the output of the FAN functional as { n | property of n } 
    
    The FAN for cover has exactly the same shape
    
     FAN_cover x : cover T P x → cover T† ⋀₁P [x]
     
    but the finitary image T† now has type T† : list X → list X → Type,
    as it records the position of images in the image list:
    
        T† l m := ∀y, y ∈ₜ m → { x : X & x ∈ₜ l ∧ₜ T x y }
    
    where y ∈ₜ m is the type of occurences of y in m. So T† l m
    read as the type of maps from occurences in m to a T related
    occurences in l.

    The needed conversions:
    - the list membership predicate denoted x ∈ l below
      now has a Type-bounded counterpart denoted x ∈ₜ l
      which contain not only the information of membership
      but also of "position" of x in l, hence x ∈ₜ l is the
      type of occurrences of x in l;
    - the permutatibility predicate denoted l ~ₚ m is converted
      into the type of permutations l ~ₜ m;
    - a small part of the List module and Permutation module
      most be lifted to Type-bounded as well. Notice that
      we need both verions of ∈ and ∈ₜ, but only Type-bounded
      permutations; 
    - of course cover and bar (we skip acc/Acc/founded here)
    - interesting is the DC (dependent choice) is provable
      into Type (not in Prop) hence the sequential and the
      negative characterizations are equivalent for the
      Type-bounded versions.
    - we do not study the role played by strong XM 
      ie (∀P : Type, P + (P → False)) because we think
      such an axiom is way too strong anyway !!
    - incl and fimage need to be lifted to Type
    
    - We obtain the FAN theorem for Type-bounded covers,
      for Type-bounded bars (incl Fridlender's formulation)
      and König's lemma for Type-bounded AF relations
    - These allow the computation of the FAN functional,
      eg the bound in the length of the branches of tree.
      
    - we do not adapt the part related to the representation
      of trees but this should not pose any difficulty.
*) 

From Coq Require Import List Arith Lia Utf8.

Import ListNotations.

Set Implicit Arguments.

(** Notations for Base based logical connectives, see below *)

#[local] Reserved Notation "⊥ₜ" (at level 0).
#[local] Reserved Notation "x '∨ₜ' y" (at level 80, right associativity).
#[local] Reserved Notation "x '∧ₜ' y" (at level 80, right associativity).
#[local] Reserved Notation "P '⇄ₜ' Q" (at level 95, no associativity).
#[local] Reserved Notation "'Σₜ' x .. y , p" (at level 200, x binder, right associativity).

#[local] Reserved Notation "x ∈ₜ l" (at level 70, no associativity, format "x  ∈ₜ  l").
#[local] Reserved Notation "l ~ₜ m" (at level 70, no associativity, format "l  ~ₜ  m").

(* Base := Type based implementation of connectives *)

Module Base_is_Type.

  (* Type-bounded connectives *)

  Notation Base := Type (only parsing).
  Notation Absurd := Empty_set (only parsing).  (* ⊥ₜ *)
  Notation DepSum := sigT (only parsing).       (* Σₜ *)
  Notation NonDepSum := sum (only parsing).     (* ∨ₜ *)
  Notation NonDepProd := prod (only parsing).   (* ∧ₜ *)

End Base_is_Type.

Import Base_is_Type.

#[local] Notation "⊥ₜ" := Absurd (only parsing) : type_scope.
#[local] Notation "x ∨ₜ y" := (NonDepSum x y) (only parsing) : type_scope.
#[local] Notation "x ∧ₜ y" := (NonDepProd x y) (only parsing) : type_scope.
#[local] Notation "'Σₜ' x .. y , p" := (DepSum (fun x => .. (DepSum (fun y => p)) ..)) (only parsing) : type_scope.
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

(* Usual hints for membership, inclusion of lists and permutations *)
#[local] Hint Resolve in_eq in_cons in_or_app incl_refl incl_tl : core.

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
  
  Hint Constructors Permutation_Base : core.

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

(* Base-bounded version of List.Forall_forall *) 
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

(* Base-bounded version of the above *)
Fact forall_ex_Forall2_Base X Y (R : X → Y → Prop) l : (∀x, x ∈ₜ l → Σₜ y, R x y) → Σₜ m, ⋀₂R l m.
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

(** Maximum of a list *)

(* Maximum value in a list of natural numbers *)
Definition list_max := fold_right max 0.

(* list_max and membership *)
Fact list_max_in n l : n ∈ l → n ≤ list_max l.
Proof.
  revert n; apply Forall_forall.
  induction l as [ | x l IHl ]; simpl; constructor.
  + lia.
  + revert IHl; apply Forall_impl; lia.
Qed.

(* list_max occurs in the list *)
Fact list_max_find l : l = [] ∨ list_max l ∈ l.
Proof.
  induction l as [ | x l [ -> | ] ]; auto; right; simpl.
  + lia.
  + destruct (Nat.max_spec_le x (list_max l))
      as [ (_ & ->) | (_ & ->) ]; auto.
Qed.

(** The notion of being upward closed for T *)

#[local] Notation upclosed T P := (∀ x y, T x y → P x → P y).

Fact Forall_upclosed_perm X (P : rel₁ X) : upclosed (λ l m, l ~ₜ m) ⋀₁P.
Proof. intros ? ? ?; rewrite !Forall_forall_In_Base; eauto. Qed.

(** The cover inductive predicate is given by two rules *)

Unset Elimination Schemes.

(* Both the transition relation T and the output are lifted to Base := Type *)
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

Section dependent_choice_sigma.

  (* This is Dependent Choice:
       any total relation contains a sequence
       starting at any given point. *)

  Definition DC X :=
    ∀ R : X → X → Type,
        (∀x, Σₜ y, R x y) 
       → ∀x, Σₜ ρ, ρ 0 = x ∧ₜ ∀n, R (ρ n) (ρ (S n)).
       
  Theorem DC_Type : ∀X, DC X.
  Proof.
    intros X R HR x.
    set (f x := projT1 (HR x)).
    assert (Hf : ∀x, R x (f x)).
    1: intro; apply (projT2 _).
    exists (@nat_rect _ x (fun _ => f)); split; auto.
  Qed.

  (* Below is a specialization of Dependent Choice on a Σ-type

     If R is a total relation on {x | Q x} then there is a
     R-sequence starting from any point in Q. *)

  Definition DC_Σ {X} (Q : X → Type) :=
    ∀R, (∀x, Q x → Σₜ y, Q y ∧ₜ R x y)
       → ∀x, Q x → Σₜ ρ, ρ 0 = x ∧ₜ (∀n, Q (ρ n) ∧ₜ R (ρ n) (ρ (S n))).

  Fact DC_sig__DC_Σ X (Q : X → Type) : DC {x & Q x} → DC_Σ Q.
  Proof.
    intros dc R HR x Hx.
    destruct dc
      with (R := λ u v : sigT Q, R (projT1 u) (projT1 v))
           (x := existT _ x Hx)
      as (ρ & H1 & H2).
    + intros (u & Hu); simpl.
      destruct (HR _ Hu) as (v & Hv & E).
      now exists (existT _ v Hv).
    + exists (fun n => projT1 (ρ n)); repeat split; auto.
      * now rewrite H1.
      * apply (projT2 _).
  Qed.

  Fact DC_Σ__DC X : DC_Σ (λ _ : X, ⊤) → DC X.
  Proof.
    intros dc R HR x.
    destruct (dc R) with x as (ρ & H1 & H2); eauto.
    + clear x; intros x _; destruct (HR x); eauto.
    + exists ρ; split; auto; intro; apply H2.
  Qed.

  Hint Resolve DC_sig__DC_Σ DC_Σ__DC : core.

  (* Dependent Choice and Dependent Choice on Σ-types are equivalent *)

  Corollary DC_iff_DC_Σ : (∀X, DC X) ⇄ₜ ∀ X P, @DC_Σ X P.
  Proof. split; eauto. Qed.

End dependent_choice_sigma.

Section cover_extra.

  Variables (X : Type).

  Implicit Type (R T : X → X → Base) (P Q : rel₁ X) (K : X → Base).

  (* cover T P is antitonic in T and monotonic in P *)
  Fact cover_mono R T P Q : T ⊆₂ R → P ⊆₁ Q → cover R P ⊆₁ cover T Q.
  Proof. intros ? ? ?; now apply cover_morphism with (f := λ x, x). Qed.

  (* It preserves upward closed predicates *)
  Fact cover_upclosed T P : upclosed T P → upclosed T (cover T P).
  Proof. intros ? ? y H2 H3; revert H3 y H2; induction 1; eauto. Qed.

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
  Definition cover_neg T P x := λ K, K x → (∀y, K y → Σₜ z, K z ∧ₜ T y z) → Σₜ y, P y ∧ₜ K y.

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

  Theorem cover_negative T P x : cover T P x → ∀K, K x → (∀y, K y → Σₜ z, K z ∧ₜ T y z) → Σₜ y, P y ∧ₜ K y.
  Proof. intro; now apply cover_pos__cover_neg, cover_iff_cover_pos. Qed.

  (* The sequential characterization of cover T P x is ∀ρ, cover_seq T P x ρ.
     This reads as any T-sequence starting at x meets P *)
  Definition cover_seq T P x := λ ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → Σₜ n, P (ρ n).

  (* For a T-sequence ρ starting at x, its direct image 
     Q := λ x, Σₜ n, x = ρ n, satisfies
       - Q contains x
       - Q is T-unstoppable
     Hence Q meets P, which entails that ρ meets P *)
  Lemma cover_seq_direct_image T P x ρ : cover_neg T P x (λ x, Σₜ n, x = ρ n) → cover_seq T P x ρ.
  Proof. 
    intros H H1 H2.
    destruct H as (? & ? & ? & ->); eauto.
    intros ? (? & ->); eauto.
  Qed.

  Corollary cover_neg__cover_seq T P x : (∀K, cover_neg T P x K) → ∀ρ, cover_seq T P x ρ.
  Proof. intros H ρ; apply cover_seq_direct_image, H. Qed.

  Theorem cover_sequences T P x : cover T P x → ∀ρ, ρ 0 = x → (∀n, T (ρ n) (ρ (1+n))) → Σₜ n, P (ρ n).
  Proof. intro; apply cover_neg__cover_seq; unfold cover_neg; now apply cover_negative. Qed.
  
  Section cover_seq__cover_neg_Dependent_Choice.

    (* Using D(ependent) C(hoice) on a Σ-type, but w/o excluded middle, one can get
       the negative characterization of cover T P x from the sequential one. *)
    Lemma cover_seq__cover_neg_DC T P x : (∀ρ, cover_seq T P x ρ) → ∀Q : X → Type, cover_neg T P x Q.
    Proof.
      generalize (fst DC_iff_DC_Σ DC_Type); intros dc.
      intros H Q Hx HQ.
      destruct (dc _ _ _ HQ _ Hx)
        as (rho & H1 & H2).
      destruct (H _ H1) as (n & Hn); eauto.
      + intro; apply H2.
      + exists (rho n); split; auto; apply H2.
    Qed.

  End cover_seq__cover_neg_Dependent_Choice.

  Theorem cover_neg_iff_cover_seq__Base_is_Type T P x : (∀K, cover_neg T P x K) ⇄ₜ ∀ρ, cover_seq T P x ρ.
  Proof.
    split.
    + apply cover_neg__cover_seq.
    + exact (@cover_seq__cover_neg_DC T P x).
  Qed.

End cover_extra.

(** Finitary lifting of a binary relation to lists *)

(* fimage (for finitary image) is the lifting of T to lists (viewed as finite sets)
   T† := fimage T is a way to interpret finitary FANs, defined as:

     T† l m if any member of m in a T-image of some member of l *)

Definition fimage {X} (T : X → X → Base) l m := ∀y, y ∈ₜ m → Σₜ x, x ∈ₜ l ∧ₜ T x y.

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
  Lemma fimage_split_inv l₁ l₂ m : T† (l₁++l₂) m → Σₜ m₁ m₂, m ~ₜ m₁++m₂ ∧ₜ T† l₁ m₁ ∧ₜ T† l₂ m₂.
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

  Fact extends_iff l m : extends l m ⇄ₜ Σₜ x, m = x::l.
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

  Fact bar_negative P : bar P [] → ∀K, K [] → (∀l, K l → Σₜ x, K (x::l)) → Σₜ l, P l ∧ₜ K l.
  Proof.
    intros H%bar_iff_cover_extends Q H1 H2. 
    apply (cover_negative H); eauto.
    intros ? (? & ?)%H2; eauto.
  Qed.

  Fact bar_sequences P : bar P [] → ∀α, Σₜ n, P (pfx α n).
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
Definition finite {X} (P : rel₁ X) := Σₜ l, ∀x, P x ↔ x ∈ l.

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

Fact In_Base_map_iff  X Y (f : X → Y) y l : y ∈ₜ map f l ⇄ₜ Σₜ x, y = f x ∧ₜ x ∈ₜ l.
Proof.
  split.
  + induction l as [ | ? ? IHl ]; simpl; intros []; subst; eauto.
    destruct IHl as (? & []); subst; eauto.
  + intros (? & -> & ?); eauto.
Qed.

Fact In_Base_flat_map_iff X Y (f : X → list Y) l y : y ∈ₜ flat_map f l ⇄ₜ Σₜ x, x ∈ₜ l ∧ₜ y ∈ₜ f x.
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

  Fact list_prod_spec_Base l m z : z ∈ₜ list_prod l m ⇄ₜ Σₜ x y, z = p x y ∧ₜ x ∈ₜ l ∧ₜ y ∈ₜ m.
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

  (* This proof requires more precision than the one given by list_fan_spec
     because we need to know positions in lists, not just memebership *)
  Fact list_fan_cons_inv_Base c lc l : l ∈ₜ list_fan (c::lc) ⇄ₜ Σₜ x m, l = x::m ∧ₜ x ∈ₜ c ∧ₜ m ∈ₜ list_fan lc.
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

(** list branching finite trees, ie trees nested with lists *)

Unset Elimination Schemes.
Inductive tree X : Type :=
  | node : X → list (tree X) → tree X.
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

  Fact path_cons_inv T x y p z : path T x (y::p) z ↔ T x y ∧ path T y p z.
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

  (* The notion of representation that comes to mind first. *)
  Definition strongly_represents T P x t :=
      root t = x
    ∧ ∀ p y, branch t p y ↔ path T x p y ∧ P p y.

  (** So we favor this definition for representation
      of the relation T at root x by a tree, on the
      paths that satisfy P. 

      This means that t may contain branches that
      do not satisfy P. *)
  Definition represents T P x t :=
      root t = x
    ∧ ∀ p y, P p y → (branch t p y ↔ path T x p y ).

  (* A strong representation is a representation *)
  Fact strongly_represents__represents T P x :
      strongly_represents T P x ⊆₁ represents T P x.
  Proof. 
    intros ? (? & H); split; auto.
    intros ? ? ?; rewrite H; tauto.
  Qed.

  Variables (T : rel₂ X) (Tfin : ∀x, finite (T x)).

  (** length bounded path can be strongly represented
      because this is a (weakly) decidable predicate *)
  Theorem bounded_length_strongly_represented n x :
       Σₜ t, strongly_represents T (λ p _, ⌊p⌋ ≤ n) x t.
  Proof.
    induction n as [ | n IHn ] in x |- *.
    + exists ⟨x|[]⟩; split; simpl; auto.
      intros p y; split.
      * destruct p; intros H%branch_inv; subst; simpl; auto.
        destruct H as (_ & [] & _).
      * destruct p; intros (?%path_inv & ?); simpl in *; subst; auto; lia.
    + destruct (Tfin x) as [ lx Hlx ].
      set (R x t := strongly_represents T (λ p _, ⌊p⌋ ≤ n) x t).
      destruct (forall_ex_Forall2_Base R lx) as (lt & Hlt); eauto.
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
       (Σₜ t, represents T P x t)
    ⇄ₜ (Σₜ n, ∀ p y, path T x p y → P p y → ⌊p⌋ < n).
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

Fact rev_fix A (a : A) l : rev (a::l) = rev l ++ [a].
Proof. reflexivity. Qed.

Section konig_cover.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x)) 
            (P : rel₁ X) (Pupc : upclosed T P) 
            (x : X) (Hx : cover T P x).

  Local Definition next y := projT1 (Tfin y).

  Local Fact next_spec y z : T y z ↔ z ∈ next y.
  Proof. apply (projT2 (Tfin y)). Qed.

  Local Definition circle : nat → list X := nat_rect _ [x] (λ _, flat_map next).

  Local Fact path_to_circle p y : path T x p y → y ∈ circle ⌊p⌋.
  Proof.
    induction p as [ | u p IH] in y |- * using rev_ind.
    + intros []%path_inv; simpl; auto.
    + intros (v & ? & ?%next_spec & ->)%path_snoc_inv; simpl; auto.
      rewrite length_app, Nat.add_comm; simpl.
      apply in_flat_map; eauto.
  Qed.

  Hint Resolve path_to_circle path_app : core.

  Local Fact path__FAN_circle p y : path T x p y → FAN (rev (pfx (λ n, circle (S n)) ⌊p⌋)) p.
  Proof.
    induction p as [ | u p IH] in y |- * using rev_ind.
    + intros <-%path_inv; simpl; auto.
    + intros (v & H1 & H2 & ->)%path_snoc_inv.
      rewrite app_length, Nat.add_comm; simpl plus.
      rewrite pfx_fix, rev_fix.
      apply Forall2_app; eauto.
      constructor; auto.
      replace (S ⌊p⌋) with ⌊p++[y]⌋; eauto.
      rewrite app_length; simpl; lia.
  Qed.

  (* There is a circle in P *)
  Local Lemma P_contains_some_circle : Σₜ n, ⋀₁P (circle n).
  Proof.
    apply cover_sequences with (x := [x]) (T := T†) (P := ⋀₁P); auto.
    + apply FAN_cover; auto.
    + intros ? ? (? & ? & ?%inhabits%In_iff_inhabited_In_Base%next_spec)%In_Base_flat_map_iff; eauto.
  Qed.

  (* As a consequence, the paths which do not end in P are those of a finite tree *)
  Theorem konig_cover : Σₜ t, represents T (λ _ y, ¬ P y) x t.
  Proof.
    apply finitary_represented_iff_bounded; auto.
    destruct P_contains_some_circle as (n & Hn).
    rewrite Forall_forall in Hn.
    exists n.
    apply short_paths; auto.
    intros p ? ? ?; apply Hn; subst; now apply path_to_circle.
  Qed.

End konig_cover.

Check konig_cover.

(** The finitary version of König's lemma w/o XM or choice 
    see https://fr.wikipedia.org/wiki/Lemme_de_K%C3%B6nig
    and https://books.google.fr/books?id=N7BvXVUCQk8C&printsec=frontcover&redir_esc=y#v=onepage&q&f=false *)

(*
Section acc_rel.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x))
            (x : X) (Hx : acc T x).

  Theorem konig_acc : ∃t, root t = x ∧ ∀ p y, branch t p y ↔ path T x p y .
  Proof.
    destruct konig_cover
      with (1 := Tfin) (P := λ _ : X, ⊥) (x := x)
      as (? & []); eauto.
    now apply acc_iff_cover_empty in Hx.
  Qed.

End acc_rel.

Check konig_acc.
*)

Section konig_bar.

  Variables (X : Type)
            (T : rel₂ X) (Tfin : ∀x, finite (T x))
            (P : rel₁ (list X)) (Pmono : monotone P)
            (HP : bar P []).

  (* P contains all the paths from x to points on some circle *)
  Local Lemma P_contains_some_disk x : Σₜ n, ∀p y, path T x p y → n = ⌊p⌋ → P (rev p).
  Proof.
    destruct (bar_sequences (FAN_bar Pmono HP))
      with (α := fun n => circle _ Tfin x (S n))
      as (n & Hn).
    exists n.
    intros p y Hp H.
    apply Hn.
    subst n.
    rewrite Forall2_rev_iff, rev_involutive.
    revert Hp; apply path__FAN_circle.
  Qed.

  (* Hence, only short paths can satisfy ¬ P *)
  Theorem konig_bar x : Σₜ t, represents T (λ p _, ¬ P (rev p)) x t.
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

  (** Base:=Type bounded af R predicate contains computational
      information, ie for any sequence α, one can compute a
      bound under which a good pair must occur *)
  Lemma af_sequences R : af R → ∀α, Σₜ n, ∃ i j, i < j < n ∧ R (α i) (α j).
  Proof.
    intros H%af__bar_good_nil α.
    destruct (bar_sequences H α) as (n & Hn).
    exists n; now apply good_pfx_iff.
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
  Local Lemma good_uniform_over_FAN : Σₜ n, ∀l, choice_list P l → ⌊l⌋ = n → good R (rev l).
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
  Theorem af_konig_choice : Σₜ n, ∀l, choice_list P l → irred R l → ⌊l⌋ < n.
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
