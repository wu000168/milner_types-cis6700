Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

From Exp Require Export Exp_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme ty_mono_ind' := Induction for ty_mono Sort Prop.

Combined Scheme ty_mono_mutind from ty_mono_ind'.

Scheme ty_mono_rec' := Induction for ty_mono Sort Set.

Combined Scheme ty_mono_mutrec from ty_mono_rec'.

Scheme ty_rho_ind' := Induction for ty_rho Sort Prop.

Combined Scheme ty_rho_mutind from ty_rho_ind'.

Scheme ty_rho_rec' := Induction for ty_rho Sort Set.

Combined Scheme ty_rho_mutrec from ty_rho_rec'.

Scheme ty_poly_ind' := Induction for ty_poly Sort Prop.

Combined Scheme ty_poly_mutind from ty_poly_ind'.

Scheme ty_poly_rec' := Induction for ty_poly Sort Set.

Combined Scheme ty_poly_mutrec from ty_poly_rec'.

Scheme tm_ind' := Induction for tm Sort Prop.

Combined Scheme tm_mutind from tm_ind'.

Scheme tm_rec' := Induction for tm Sort Set.

Combined Scheme tm_mutrec from tm_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_ty_mono (tau1 : ty_mono) {struct tau1} : nat :=
  match tau1 with
    | ty_mono_base => 1
    | ty_mono_var_f a1 => 1
    | ty_mono_var_b n1 => 1
    | ty_mono_func tau2 tau3 => 1 + (size_ty_mono tau2) + (size_ty_mono tau3)
  end.

Fixpoint size_ty_rho (rho1 : ty_rho) {struct rho1} : nat :=
  match rho1 with
    | ty_rho_tau tau1 => 1 + (size_ty_mono tau1)
  end.

Fixpoint size_ty_poly (sig1 : ty_poly) {struct sig1} : nat :=
  match sig1 with
    | ty_poly_rho rho1 => 1 + (size_ty_rho rho1)
    | ty_poly_poly_gen sig2 => 1 + (size_ty_poly sig2)
  end.

Fixpoint size_tm (t1 : tm) {struct t1} : nat :=
  match t1 with
    | exp_lit i1 => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs t2 => 1 + (size_tm t2)
    | exp_app t2 u1 => 1 + (size_tm t2) + (size_tm u1)
    | exp_typed_abs sig1 t2 => 1 + (size_ty_poly sig1) + (size_tm t2)
    | exp_let u1 t2 => 1 + (size_tm u1) + (size_tm t2)
    | exp_type_anno t2 sig1 => 1 + (size_tm t2) + (size_ty_poly sig1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_ty_mono_wrt_ty_mono : nat -> ty_mono -> Prop :=
  | degree_wrt_ty_mono_ty_mono_base : forall n1,
    degree_ty_mono_wrt_ty_mono n1 (ty_mono_base)
  | degree_wrt_ty_mono_ty_mono_var_f : forall n1 a1,
    degree_ty_mono_wrt_ty_mono n1 (ty_mono_var_f a1)
  | degree_wrt_ty_mono_ty_mono_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ty_mono_wrt_ty_mono n1 (ty_mono_var_b n2)
  | degree_wrt_ty_mono_ty_mono_func : forall n1 tau1 tau2,
    degree_ty_mono_wrt_ty_mono n1 tau1 ->
    degree_ty_mono_wrt_ty_mono n1 tau2 ->
    degree_ty_mono_wrt_ty_mono n1 (ty_mono_func tau1 tau2).

Scheme degree_ty_mono_wrt_ty_mono_ind' := Induction for degree_ty_mono_wrt_ty_mono Sort Prop.

Combined Scheme degree_ty_mono_wrt_ty_mono_mutind from degree_ty_mono_wrt_ty_mono_ind'.

#[export] Hint Constructors degree_ty_mono_wrt_ty_mono : core lngen.

Inductive degree_ty_rho_wrt_ty_mono : nat -> ty_rho -> Prop :=
  | degree_wrt_ty_mono_ty_rho_tau : forall n1 tau1,
    degree_ty_mono_wrt_ty_mono n1 tau1 ->
    degree_ty_rho_wrt_ty_mono n1 (ty_rho_tau tau1).

Scheme degree_ty_rho_wrt_ty_mono_ind' := Induction for degree_ty_rho_wrt_ty_mono Sort Prop.

Combined Scheme degree_ty_rho_wrt_ty_mono_mutind from degree_ty_rho_wrt_ty_mono_ind'.

#[export] Hint Constructors degree_ty_rho_wrt_ty_mono : core lngen.

Inductive degree_ty_poly_wrt_ty_mono : nat -> ty_poly -> Prop :=
  | degree_wrt_ty_mono_ty_poly_rho : forall n1 rho1,
    degree_ty_rho_wrt_ty_mono n1 rho1 ->
    degree_ty_poly_wrt_ty_mono n1 (ty_poly_rho rho1)
  | degree_wrt_ty_mono_ty_poly_poly_gen : forall n1 sig1,
    degree_ty_poly_wrt_ty_mono (S n1) sig1 ->
    degree_ty_poly_wrt_ty_mono n1 (ty_poly_poly_gen sig1).

Scheme degree_ty_poly_wrt_ty_mono_ind' := Induction for degree_ty_poly_wrt_ty_mono Sort Prop.

Combined Scheme degree_ty_poly_wrt_ty_mono_mutind from degree_ty_poly_wrt_ty_mono_ind'.

#[export] Hint Constructors degree_ty_poly_wrt_ty_mono : core lngen.

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_exp_lit : forall n1 i1,
    degree_tm_wrt_tm n1 (exp_lit i1)
  | degree_wrt_tm_exp_var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (exp_var_f x1)
  | degree_wrt_tm_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (exp_var_b n2)
  | degree_wrt_tm_exp_abs : forall n1 t1,
    degree_tm_wrt_tm (S n1) t1 ->
    degree_tm_wrt_tm n1 (exp_abs t1)
  | degree_wrt_tm_exp_app : forall n1 t1 u1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 u1 ->
    degree_tm_wrt_tm n1 (exp_app t1 u1)
  | degree_wrt_tm_exp_typed_abs : forall n1 sig1 t1,
    degree_tm_wrt_tm (S n1) t1 ->
    degree_tm_wrt_tm n1 (exp_typed_abs sig1 t1)
  | degree_wrt_tm_exp_let : forall n1 u1 t1,
    degree_tm_wrt_tm n1 u1 ->
    degree_tm_wrt_tm (S n1) t1 ->
    degree_tm_wrt_tm n1 (exp_let u1 t1)
  | degree_wrt_tm_exp_type_anno : forall n1 t1 sig1,
    degree_tm_wrt_tm n1 t1 ->
    degree_tm_wrt_tm n1 (exp_type_anno t1 sig1).

Inductive degree_tm_wrt_ty_mono : nat -> tm -> Prop :=
  | degree_wrt_ty_mono_exp_lit : forall n1 i1,
    degree_tm_wrt_ty_mono n1 (exp_lit i1)
  | degree_wrt_ty_mono_exp_var_f : forall n1 x1,
    degree_tm_wrt_ty_mono n1 (exp_var_f x1)
  | degree_wrt_ty_mono_exp_var_b : forall n1 n2,
    degree_tm_wrt_ty_mono n1 (exp_var_b n2)
  | degree_wrt_ty_mono_exp_abs : forall n1 t1,
    degree_tm_wrt_ty_mono n1 t1 ->
    degree_tm_wrt_ty_mono n1 (exp_abs t1)
  | degree_wrt_ty_mono_exp_app : forall n1 t1 u1,
    degree_tm_wrt_ty_mono n1 t1 ->
    degree_tm_wrt_ty_mono n1 u1 ->
    degree_tm_wrt_ty_mono n1 (exp_app t1 u1)
  | degree_wrt_ty_mono_exp_typed_abs : forall n1 sig1 t1,
    degree_ty_poly_wrt_ty_mono n1 sig1 ->
    degree_tm_wrt_ty_mono n1 t1 ->
    degree_tm_wrt_ty_mono n1 (exp_typed_abs sig1 t1)
  | degree_wrt_ty_mono_exp_let : forall n1 u1 t1,
    degree_tm_wrt_ty_mono n1 u1 ->
    degree_tm_wrt_ty_mono n1 t1 ->
    degree_tm_wrt_ty_mono n1 (exp_let u1 t1)
  | degree_wrt_ty_mono_exp_type_anno : forall n1 t1 sig1,
    degree_tm_wrt_ty_mono n1 t1 ->
    degree_ty_poly_wrt_ty_mono n1 sig1 ->
    degree_tm_wrt_ty_mono n1 (exp_type_anno t1 sig1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop.

Combined Scheme degree_tm_wrt_tm_mutind from degree_tm_wrt_tm_ind'.

Scheme degree_tm_wrt_ty_mono_ind' := Induction for degree_tm_wrt_ty_mono Sort Prop.

Combined Scheme degree_tm_wrt_ty_mono_mutind from degree_tm_wrt_ty_mono_ind'.

#[export] Hint Constructors degree_tm_wrt_tm : core lngen.

#[export] Hint Constructors degree_tm_wrt_ty_mono : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_ty_mono : ty_mono -> Set :=
  | lc_set_ty_mono_base :
    lc_set_ty_mono (ty_mono_base)
  | lc_set_ty_mono_var_f : forall a1,
    lc_set_ty_mono (ty_mono_var_f a1)
  | lc_set_ty_mono_func : forall tau1 tau2,
    lc_set_ty_mono tau1 ->
    lc_set_ty_mono tau2 ->
    lc_set_ty_mono (ty_mono_func tau1 tau2).

Scheme lc_ty_mono_ind' := Induction for lc_ty_mono Sort Prop.

Combined Scheme lc_ty_mono_mutind from lc_ty_mono_ind'.

Scheme lc_set_ty_mono_ind' := Induction for lc_set_ty_mono Sort Prop.

Combined Scheme lc_set_ty_mono_mutind from lc_set_ty_mono_ind'.

Scheme lc_set_ty_mono_rec' := Induction for lc_set_ty_mono Sort Set.

Combined Scheme lc_set_ty_mono_mutrec from lc_set_ty_mono_rec'.

#[export] Hint Constructors lc_ty_mono : core lngen.

#[export] Hint Constructors lc_set_ty_mono : core lngen.

Inductive lc_set_ty_rho : ty_rho -> Set :=
  | lc_set_ty_rho_tau : forall tau1,
    lc_set_ty_mono tau1 ->
    lc_set_ty_rho (ty_rho_tau tau1).

Scheme lc_ty_rho_ind' := Induction for lc_ty_rho Sort Prop.

Combined Scheme lc_ty_rho_mutind from lc_ty_rho_ind'.

Scheme lc_set_ty_rho_ind' := Induction for lc_set_ty_rho Sort Prop.

Combined Scheme lc_set_ty_rho_mutind from lc_set_ty_rho_ind'.

Scheme lc_set_ty_rho_rec' := Induction for lc_set_ty_rho Sort Set.

Combined Scheme lc_set_ty_rho_mutrec from lc_set_ty_rho_rec'.

#[export] Hint Constructors lc_ty_rho : core lngen.

#[export] Hint Constructors lc_set_ty_rho : core lngen.

Inductive lc_set_ty_poly : ty_poly -> Set :=
  | lc_set_ty_poly_rho : forall rho1,
    lc_set_ty_rho rho1 ->
    lc_set_ty_poly (ty_poly_rho rho1)
  | lc_set_ty_poly_poly_gen : forall sig1,
    (forall a1 : tyvar, lc_set_ty_poly (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1))) ->
    lc_set_ty_poly (ty_poly_poly_gen sig1).

Scheme lc_ty_poly_ind' := Induction for lc_ty_poly Sort Prop.

Combined Scheme lc_ty_poly_mutind from lc_ty_poly_ind'.

Scheme lc_set_ty_poly_ind' := Induction for lc_set_ty_poly Sort Prop.

Combined Scheme lc_set_ty_poly_mutind from lc_set_ty_poly_ind'.

Scheme lc_set_ty_poly_rec' := Induction for lc_set_ty_poly Sort Set.

Combined Scheme lc_set_ty_poly_mutrec from lc_set_ty_poly_rec'.

#[export] Hint Constructors lc_ty_poly : core lngen.

#[export] Hint Constructors lc_set_ty_poly : core lngen.

Inductive lc_set_tm : tm -> Set :=
  | lc_set_exp_lit : forall i1,
    lc_set_tm (exp_lit i1)
  | lc_set_exp_var_f : forall x1,
    lc_set_tm (exp_var_f x1)
  | lc_set_exp_abs : forall t1,
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm t1 (exp_var_f x1))) ->
    lc_set_tm (exp_abs t1)
  | lc_set_exp_app : forall t1 u1,
    lc_set_tm t1 ->
    lc_set_tm u1 ->
    lc_set_tm (exp_app t1 u1)
  | lc_set_exp_typed_abs : forall sig1 t1,
    lc_set_ty_poly sig1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm t1 (exp_var_f x1))) ->
    lc_set_tm (exp_typed_abs sig1 t1)
  | lc_set_exp_let : forall u1 t1,
    lc_set_tm u1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm t1 (exp_var_f x1))) ->
    lc_set_tm (exp_let u1 t1)
  | lc_set_exp_type_anno : forall t1 sig1,
    lc_set_tm t1 ->
    lc_set_ty_poly sig1 ->
    lc_set_tm (exp_type_anno t1 sig1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop.

Combined Scheme lc_tm_mutind from lc_tm_ind'.

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop.

Combined Scheme lc_set_tm_mutind from lc_set_tm_ind'.

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set.

Combined Scheme lc_set_tm_mutrec from lc_set_tm_rec'.

#[export] Hint Constructors lc_tm : core lngen.

#[export] Hint Constructors lc_set_tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_ty_mono_wrt_ty_mono tau1 := forall a1, lc_ty_mono (open_ty_mono_wrt_ty_mono tau1 (ty_mono_var_f a1)).

#[export] Hint Unfold body_ty_mono_wrt_ty_mono : core.

Definition body_ty_rho_wrt_ty_mono rho1 := forall a1, lc_ty_rho (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a1)).

#[export] Hint Unfold body_ty_rho_wrt_ty_mono : core.

Definition body_ty_poly_wrt_ty_mono sig1 := forall a1, lc_ty_poly (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1)).

#[export] Hint Unfold body_ty_poly_wrt_ty_mono : core.

Definition body_tm_wrt_tm t1 := forall x1, lc_tm (open_tm_wrt_tm t1 (exp_var_f x1)).

Definition body_tm_wrt_ty_mono t1 := forall a1, lc_tm (open_tm_wrt_ty_mono t1 (ty_mono_var_f a1)).

#[export] Hint Unfold body_tm_wrt_tm : core.

#[export] Hint Unfold body_tm_wrt_ty_mono : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_ty_mono_min_mutual :
(forall tau1, 1 <= size_ty_mono tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ty_mono_min :
forall tau1, 1 <= size_ty_mono tau1.
Proof.
pose proof size_ty_mono_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_mono_min : lngen.

(* begin hide *)

Lemma size_ty_rho_min_mutual :
(forall rho1, 1 <= size_ty_rho rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ty_rho_min :
forall rho1, 1 <= size_ty_rho rho1.
Proof.
pose proof size_ty_rho_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_rho_min : lngen.

(* begin hide *)

Lemma size_ty_poly_min_mutual :
(forall sig1, 1 <= size_ty_poly sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ty_poly_min :
forall sig1, 1 <= size_ty_poly sig1.
Proof.
pose proof size_ty_poly_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_poly_min : lngen.

(* begin hide *)

Lemma size_tm_min_mutual :
(forall t1, 1 <= size_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_tm_min :
forall t1, 1 <= size_tm t1.
Proof.
pose proof size_tm_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_min : lngen.

(* begin hide *)

Lemma size_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 a1 n1,
  size_ty_mono (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) = size_ty_mono tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_mono_close_ty_mono_wrt_ty_mono_rec :
forall tau1 a1 n1,
  size_ty_mono (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) = size_ty_mono tau1.
Proof.
pose proof size_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_mono_close_ty_mono_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite size_ty_mono_close_ty_mono_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 a1 n1,
  size_ty_rho (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) = size_ty_rho rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_close_ty_rho_wrt_ty_mono_rec :
forall rho1 a1 n1,
  size_ty_rho (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) = size_ty_rho rho1.
Proof.
pose proof size_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_rho_close_ty_rho_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite size_ty_rho_close_ty_rho_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 a1 n1,
  size_ty_poly (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) = size_ty_poly sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_close_ty_poly_wrt_ty_mono_rec :
forall sig1 a1 n1,
  size_ty_poly (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) = size_ty_poly sig1.
Proof.
pose proof size_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_poly_close_ty_poly_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite size_ty_poly_close_ty_poly_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 t1) = size_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 t1) = size_tm t1.
Proof.
pose proof size_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  size_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) = size_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  size_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) = size_tm t1.
Proof.
pose proof size_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_ty_mono_close_ty_mono_wrt_ty_mono :
forall tau1 a1,
  size_ty_mono (close_ty_mono_wrt_ty_mono a1 tau1) = size_ty_mono tau1.
Proof.
unfold close_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_mono_close_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite size_ty_mono_close_ty_mono_wrt_ty_mono using solve [auto] : lngen.

Lemma size_ty_rho_close_ty_rho_wrt_ty_mono :
forall rho1 a1,
  size_ty_rho (close_ty_rho_wrt_ty_mono a1 rho1) = size_ty_rho rho1.
Proof.
unfold close_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_rho_close_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite size_ty_rho_close_ty_rho_wrt_ty_mono using solve [auto] : lngen.

Lemma size_ty_poly_close_ty_poly_wrt_ty_mono :
forall sig1 a1,
  size_ty_poly (close_ty_poly_wrt_ty_mono a1 sig1) = size_ty_poly sig1.
Proof.
unfold close_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_poly_close_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite size_ty_poly_close_ty_poly_wrt_ty_mono using solve [auto] : lngen.

Lemma size_tm_close_tm_wrt_tm :
forall t1 x1,
  size_tm (close_tm_wrt_tm x1 t1) = size_tm t1.
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma size_tm_close_tm_wrt_ty_mono :
forall t1 a1,
  size_tm (close_tm_wrt_ty_mono a1 t1) = size_tm t1.
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_ty_mono using solve [auto] : lngen.

(* begin hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 tau2 n1,
  size_ty_mono tau1 <= size_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono_rec :
forall tau1 tau2 n1,
  size_ty_mono tau1 <= size_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1).
Proof.
pose proof size_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_mono_open_ty_mono_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 tau1 n1,
  size_ty_rho rho1 <= size_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono_rec :
forall rho1 tau1 n1,
  size_ty_rho rho1 <= size_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1).
Proof.
pose proof size_ty_rho_open_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_rho_open_ty_rho_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 tau1 n1,
  size_ty_poly sig1 <= size_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono_rec :
forall sig1 tau1 n1,
  size_ty_poly sig1 <= size_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1).
Proof.
pose proof size_ty_poly_open_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_poly_open_ty_poly_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_mutual :
(forall t1 t2 n1,
  size_tm t1 <= size_tm (open_tm_wrt_tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec :
forall t1 t2 n1,
  size_tm t1 <= size_tm (open_tm_wrt_tm_rec n1 t2 t1).
Proof.
pose proof size_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 n1,
  size_tm t1 <= size_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_ty_mono_rec :
forall t1 tau1 n1,
  size_tm t1 <= size_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1).
Proof.
pose proof size_tm_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono :
forall tau1 tau2,
  size_ty_mono tau1 <= size_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2).
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_mono_open_ty_mono_wrt_ty_mono : lngen.

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono :
forall rho1 tau1,
  size_ty_rho rho1 <= size_ty_rho (open_ty_rho_wrt_ty_mono rho1 tau1).
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_rho_open_ty_rho_wrt_ty_mono : lngen.

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono :
forall sig1 tau1,
  size_ty_poly sig1 <= size_ty_poly (open_ty_poly_wrt_ty_mono sig1 tau1).
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_poly_open_ty_poly_wrt_ty_mono : lngen.

Lemma size_tm_open_tm_wrt_tm :
forall t1 t2,
  size_tm t1 <= size_tm (open_tm_wrt_tm t1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm : lngen.

Lemma size_tm_open_tm_wrt_ty_mono :
forall t1 tau1,
  size_tm t1 <= size_tm (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono_rec_var_mutual :
(forall tau1 a1 n1,
  size_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1) = size_ty_mono tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono_rec_var :
forall tau1 a1 n1,
  size_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1) = size_ty_mono tau1.
Proof.
pose proof size_ty_mono_open_ty_mono_wrt_ty_mono_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_mono_open_ty_mono_wrt_ty_mono_rec_var : lngen.
#[export] Hint Rewrite size_ty_mono_open_ty_mono_wrt_ty_mono_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono_rec_var_mutual :
(forall rho1 a1 n1,
  size_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1) = size_ty_rho rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono_rec_var :
forall rho1 a1 n1,
  size_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1) = size_ty_rho rho1.
Proof.
pose proof size_ty_rho_open_ty_rho_wrt_ty_mono_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_rho_open_ty_rho_wrt_ty_mono_rec_var : lngen.
#[export] Hint Rewrite size_ty_rho_open_ty_rho_wrt_ty_mono_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono_rec_var_mutual :
(forall sig1 a1 n1,
  size_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1) = size_ty_poly sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono_rec_var :
forall sig1 a1 n1,
  size_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1) = size_ty_poly sig1.
Proof.
pose proof size_ty_poly_open_ty_poly_wrt_ty_mono_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ty_poly_open_ty_poly_wrt_ty_mono_rec_var : lngen.
#[export] Hint Rewrite size_ty_poly_open_ty_poly_wrt_ty_mono_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var_mutual :
(forall t1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1) = size_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var :
forall t1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1) = size_tm t1.
Proof.
pose proof size_tm_open_tm_wrt_tm_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_ty_mono_rec_var_mutual :
(forall t1 a1 n1,
  size_tm (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1) = size_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_ty_mono_rec_var :
forall t1 a1 n1,
  size_tm (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1) = size_tm t1.
Proof.
pose proof size_tm_open_tm_wrt_ty_mono_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_ty_mono_rec_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_ty_mono_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_ty_mono_open_ty_mono_wrt_ty_mono_var :
forall tau1 a1,
  size_ty_mono (open_ty_mono_wrt_ty_mono tau1 (ty_mono_var_f a1)) = size_ty_mono tau1.
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_mono_open_ty_mono_wrt_ty_mono_var : lngen.
#[export] Hint Rewrite size_ty_mono_open_ty_mono_wrt_ty_mono_var using solve [auto] : lngen.

Lemma size_ty_rho_open_ty_rho_wrt_ty_mono_var :
forall rho1 a1,
  size_ty_rho (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a1)) = size_ty_rho rho1.
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_rho_open_ty_rho_wrt_ty_mono_var : lngen.
#[export] Hint Rewrite size_ty_rho_open_ty_rho_wrt_ty_mono_var using solve [auto] : lngen.

Lemma size_ty_poly_open_ty_poly_wrt_ty_mono_var :
forall sig1 a1,
  size_ty_poly (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1)) = size_ty_poly sig1.
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_ty_poly_open_ty_poly_wrt_ty_mono_var : lngen.
#[export] Hint Rewrite size_ty_poly_open_ty_poly_wrt_ty_mono_var using solve [auto] : lngen.

Lemma size_tm_open_tm_wrt_tm_var :
forall t1 x1,
  size_tm (open_tm_wrt_tm t1 (exp_var_f x1)) = size_tm t1.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.

Lemma size_tm_open_tm_wrt_ty_mono_var :
forall t1 a1,
  size_tm (open_tm_wrt_ty_mono t1 (ty_mono_var_f a1)) = size_tm t1.
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_ty_mono_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_ty_mono_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_S_mutual :
(forall n1 tau1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono (S n1) tau1).
Proof.
apply_mutual_ind degree_ty_mono_wrt_ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_S :
forall n1 tau1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono (S n1) tau1.
Proof.
pose proof degree_ty_mono_wrt_ty_mono_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_S : lngen.

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_S_mutual :
(forall n1 rho1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_rho_wrt_ty_mono (S n1) rho1).
Proof.
apply_mutual_ind degree_ty_rho_wrt_ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ty_rho_wrt_ty_mono_S :
forall n1 rho1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_rho_wrt_ty_mono (S n1) rho1.
Proof.
pose proof degree_ty_rho_wrt_ty_mono_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_S : lngen.

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_S_mutual :
(forall n1 sig1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_poly_wrt_ty_mono (S n1) sig1).
Proof.
apply_mutual_ind degree_ty_poly_wrt_ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ty_poly_wrt_ty_mono_S :
forall n1 sig1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_poly_wrt_ty_mono (S n1) sig1.
Proof.
pose proof degree_ty_poly_wrt_ty_mono_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_S : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_S_mutual :
(forall n1 t1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) t1).
Proof.
apply_mutual_ind degree_tm_wrt_tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_tm_wrt_tm_S :
forall n1 t1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) t1.
Proof.
pose proof degree_tm_wrt_tm_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_S : lngen.

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_S_mutual :
(forall n1 t1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono (S n1) t1).
Proof.
apply_mutual_ind degree_tm_wrt_ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_tm_wrt_ty_mono_S :
forall n1 t1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono (S n1) t1.
Proof.
pose proof degree_tm_wrt_ty_mono_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_S : lngen.

Lemma degree_ty_mono_wrt_ty_mono_O :
forall n1 tau1,
  degree_ty_mono_wrt_ty_mono O tau1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_O : lngen.

Lemma degree_ty_rho_wrt_ty_mono_O :
forall n1 rho1,
  degree_ty_rho_wrt_ty_mono O rho1 ->
  degree_ty_rho_wrt_ty_mono n1 rho1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_O : lngen.

Lemma degree_ty_poly_wrt_ty_mono_O :
forall n1 sig1,
  degree_ty_poly_wrt_ty_mono O sig1 ->
  degree_ty_poly_wrt_ty_mono n1 sig1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_O : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 t1,
  degree_tm_wrt_tm O t1 ->
  degree_tm_wrt_tm n1 t1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_O : lngen.

Lemma degree_tm_wrt_ty_mono_O :
forall n1 t1,
  degree_tm_wrt_ty_mono O t1 ->
  degree_tm_wrt_ty_mono n1 t1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_O : lngen.

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono (S n1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
  default_simp. constructor. apply lt_n_S. auto.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec :
forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono (S n1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1).
Proof.
pose proof degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_rho_wrt_ty_mono (S n1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec :
forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_rho_wrt_ty_mono (S n1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1).
Proof.
pose proof degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_poly_wrt_ty_mono (S n1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec :
forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_poly_wrt_ty_mono (S n1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1).
Proof.
pose proof degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp. constructor. apply lt_n_S. apply H2.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1).
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1 n2,
  degree_tm_wrt_tm n2 t1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_ty_mono_rec n1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1 n2,
  degree_tm_wrt_tm n2 t1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_ty_mono_rec n1 a1 t1).
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1 n2,
  degree_tm_wrt_ty_mono n2 t1 ->
  degree_tm_wrt_ty_mono n2 (close_tm_wrt_tm_rec n1 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec :
forall t1 x1 n1 n2,
  degree_tm_wrt_ty_mono n2 t1 ->
  degree_tm_wrt_ty_mono n2 (close_tm_wrt_tm_rec n1 x1 t1).
Proof.
pose proof degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono (S n1) (close_tm_wrt_ty_mono_rec n1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono (S n1) (close_tm_wrt_ty_mono_rec n1 a1 t1).
Proof.
pose proof degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono :
forall tau1 a1,
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  degree_ty_mono_wrt_ty_mono 1 (close_ty_mono_wrt_ty_mono a1 tau1).
Proof.
unfold close_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono : lngen.

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono :
forall rho1 a1,
  degree_ty_rho_wrt_ty_mono 0 rho1 ->
  degree_ty_rho_wrt_ty_mono 1 (close_ty_rho_wrt_ty_mono a1 rho1).
Proof.
unfold close_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono : lngen.

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono :
forall sig1 a1,
  degree_ty_poly_wrt_ty_mono 0 sig1 ->
  degree_ty_poly_wrt_ty_mono 1 (close_ty_poly_wrt_ty_mono a1 sig1).
Proof.
unfold close_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall t1 x1,
  degree_tm_wrt_tm 0 t1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 t1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono :
forall t1 a1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (close_tm_wrt_ty_mono a1 t1).
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_ty_mono : lngen.

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm :
forall t1 x1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 (close_tm_wrt_tm x1 t1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_close_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono :
forall t1 a1,
  degree_tm_wrt_ty_mono 0 t1 ->
  degree_tm_wrt_ty_mono 1 (close_tm_wrt_ty_mono a1 t1).
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_inv_mutual :
(forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono (S n1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) ->
  degree_ty_mono_wrt_ty_mono n1 tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
  default_simp; eauto with lngen.
- constructor. admit.
- constructor. apply lt_S_n. assumption.
Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_inv :
forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono (S n1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) ->
  degree_ty_mono_wrt_ty_mono n1 tau1.
Proof.
pose proof degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_inv_mutual :
(forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono (S n1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) ->
  degree_ty_rho_wrt_ty_mono n1 rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_inv :
forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono (S n1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) ->
  degree_ty_rho_wrt_ty_mono n1 rho1.
Proof.
pose proof degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_inv_mutual :
(forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono (S n1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) ->
  degree_ty_poly_wrt_ty_mono n1 sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_inv :
forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono (S n1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) ->
  degree_ty_poly_wrt_ty_mono n1 sig1.
Proof.
pose proof degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_tm n1 t1).
Proof.
apply_mutual_ind tm_mutind;
  default_simp; eauto with lngen.
- constructor. admit.
- constructor. apply lt_S_n. apply H2.
Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv :
forall t1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_tm n1 t1.
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_inv_mutual :
(forall t1 a1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_ty_mono_rec n1 a1 t1) ->
  degree_tm_wrt_tm n2 t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_inv :
forall t1 a1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_ty_mono_rec n1 a1 t1) ->
  degree_tm_wrt_tm n2 t1.
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_inv_mutual :
(forall t1 x1 n1 n2,
  degree_tm_wrt_ty_mono n2 (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_ty_mono n2 t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_inv :
forall t1 x1 n1 n2,
  degree_tm_wrt_ty_mono n2 (close_tm_wrt_tm_rec n1 x1 t1) ->
  degree_tm_wrt_ty_mono n2 t1.
Proof.
pose proof degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_inv_mutual :
(forall t1 a1 n1,
  degree_tm_wrt_ty_mono (S n1) (close_tm_wrt_ty_mono_rec n1 a1 t1) ->
  degree_tm_wrt_ty_mono n1 t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_inv :
forall t1 a1 n1,
  degree_tm_wrt_ty_mono (S n1) (close_tm_wrt_ty_mono_rec n1 a1 t1) ->
  degree_tm_wrt_ty_mono n1 t1.
Proof.
pose proof degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_inv :
forall tau1 a1,
  degree_ty_mono_wrt_ty_mono 1 (close_ty_mono_wrt_ty_mono a1 tau1) ->
  degree_ty_mono_wrt_ty_mono 0 tau1.
Proof.
unfold close_ty_mono_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono_inv : lngen.

Lemma degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_inv :
forall rho1 a1,
  degree_ty_rho_wrt_ty_mono 1 (close_ty_rho_wrt_ty_mono a1 rho1) ->
  degree_ty_rho_wrt_ty_mono 0 rho1.
Proof.
unfold close_ty_rho_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono_inv : lngen.

Lemma degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_inv :
forall sig1 a1,
  degree_ty_poly_wrt_ty_mono 1 (close_ty_poly_wrt_ty_mono a1 sig1) ->
  degree_ty_poly_wrt_ty_mono 0 sig1.
Proof.
unfold close_ty_poly_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono_inv : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall t1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 t1) ->
  degree_tm_wrt_tm 0 t1.
Proof.
unfold close_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_ty_mono_inv :
forall t1 a1 n1,
  degree_tm_wrt_tm n1 (close_tm_wrt_ty_mono a1 t1) ->
  degree_tm_wrt_tm n1 t1.
Proof.
unfold close_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_ty_mono_inv : lngen.

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_tm_inv :
forall t1 x1 n1,
  degree_tm_wrt_ty_mono n1 (close_tm_wrt_tm x1 t1) ->
  degree_tm_wrt_ty_mono n1 t1.
Proof.
unfold close_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_close_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_inv :
forall t1 a1,
  degree_tm_wrt_ty_mono 1 (close_tm_wrt_ty_mono a1 t1) ->
  degree_tm_wrt_ty_mono 0 t1.
Proof.
unfold close_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_close_tm_wrt_ty_mono_inv : lngen.

(* begin hide *)

Lemma lt_neq : forall a b (H1: a <> b) (H2: a <= b), a < b.
Proof.
  intros. Search "<=". apply le_lt_eq_dec in H2. destruct H2.
  + assumption.
  + apply H1 in e. destruct e.
Qed.

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 tau2 n1,
  degree_ty_mono_wrt_ty_mono (S n1) tau1 ->
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  degree_ty_mono_wrt_ty_mono n1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
  default_simp.
constructor. apply lt_n_Sm_le in H3. apply not_eq_sym in n0. apply (lt_neq _ _ n0 H3).
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec :
forall tau1 tau2 n1,
  degree_ty_mono_wrt_ty_mono (S n1) tau1 ->
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  degree_ty_mono_wrt_ty_mono n1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1).
Proof.
pose proof degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono (S n1) rho1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_rho_wrt_ty_mono n1 (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec :
forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono (S n1) rho1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_rho_wrt_ty_mono n1 (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1).
Proof.
pose proof degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono (S n1) sig1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_poly_wrt_ty_mono n1 (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec :
forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono (S n1) sig1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_poly_wrt_ty_mono n1 (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1).
Proof.
pose proof degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual :
(forall t1 t2 n1,
  degree_tm_wrt_tm (S n1) t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind tm_mutind;
  default_simp.
constructor. apply lt_n_Sm_le in H3. apply not_eq_sym in n0. apply (lt_neq _ _ n0 H3).
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec :
forall t1 t2 n1,
  degree_tm_wrt_tm (S n1) t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1).
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 n1 n2,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono_rec n2 tau1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec :
forall t1 tau1 n1 n2,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono_rec n2 tau1 t1).
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_mutual :
(forall t1 t2 n1 n2,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 t2 ->
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm_rec n2 t2 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec :
forall t1 t2 n1 n2,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 t2 ->
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm_rec n2 t2 t1).
Proof.
pose proof degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 n1,
  degree_tm_wrt_ty_mono (S n1) t1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_ty_mono_rec n1 tau1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec :
forall t1 tau1 n1,
  degree_tm_wrt_ty_mono (S n1) t1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_ty_mono_rec n1 tau1 t1).
Proof.
pose proof degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono :
forall tau1 tau2,
  degree_ty_mono_wrt_ty_mono 1 tau1 ->
  degree_ty_mono_wrt_ty_mono 0 tau2 ->
  degree_ty_mono_wrt_ty_mono 0 (open_ty_mono_wrt_ty_mono tau1 tau2).
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono : lngen.

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono :
forall rho1 tau1,
  degree_ty_rho_wrt_ty_mono 1 rho1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  degree_ty_rho_wrt_ty_mono 0 (open_ty_rho_wrt_ty_mono rho1 tau1).
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono : lngen.

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono :
forall sig1 tau1,
  degree_ty_poly_wrt_ty_mono 1 sig1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  degree_ty_poly_wrt_ty_mono 0 (open_ty_poly_wrt_ty_mono sig1 tau1).
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall t1 t2,
  degree_tm_wrt_tm 1 t1 ->
  degree_tm_wrt_tm 0 t2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm t1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono :
forall t1 tau1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_ty_mono : lngen.

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm :
forall t1 t2 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 t2 ->
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm t1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_open_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono :
forall t1 tau1,
  degree_tm_wrt_ty_mono 1 t1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  degree_tm_wrt_ty_mono 0 (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_inv_mutual :
(forall tau1 tau2 n1,
  degree_ty_mono_wrt_ty_mono n1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1) ->
  degree_ty_mono_wrt_ty_mono (S n1) tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_inv :
forall tau1 tau2 n1,
  degree_ty_mono_wrt_ty_mono n1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1) ->
  degree_ty_mono_wrt_ty_mono (S n1) tau1.
Proof.
pose proof degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_inv_mutual :
(forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono n1 (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1) ->
  degree_ty_rho_wrt_ty_mono (S n1) rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_inv :
forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono n1 (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1) ->
  degree_ty_rho_wrt_ty_mono (S n1) rho1.
Proof.
pose proof degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_inv_mutual :
(forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono n1 (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1) ->
  degree_ty_poly_wrt_ty_mono (S n1) sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_inv :
forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono n1 (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1) ->
  degree_ty_poly_wrt_ty_mono (S n1) sig1.
Proof.
pose proof degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual :
(forall t1 t2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1) ->
  degree_tm_wrt_tm (S n1) t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv :
forall t1 t2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 t2 t1) ->
  degree_tm_wrt_tm (S n1) t1.
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_inv_mutual :
(forall t1 tau1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono_rec n2 tau1 t1) ->
  degree_tm_wrt_tm n1 t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_inv :
forall t1 tau1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono_rec n2 tau1 t1) ->
  degree_tm_wrt_tm n1 t1.
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_inv_mutual :
(forall t1 t2 n1 n2,
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm_rec n2 t2 t1) ->
  degree_tm_wrt_ty_mono n1 t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_inv :
forall t1 t2 n1 n2,
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm_rec n2 t2 t1) ->
  degree_tm_wrt_ty_mono n1 t1.
Proof.
pose proof degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_inv_mutual :
(forall t1 tau1 n1,
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_ty_mono_rec n1 tau1 t1) ->
  degree_tm_wrt_ty_mono (S n1) t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_inv :
forall t1 tau1 n1,
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_ty_mono_rec n1 tau1 t1) ->
  degree_tm_wrt_ty_mono (S n1) t1.
Proof.
pose proof degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_rec_inv : lngen.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_inv :
forall tau1 tau2,
  degree_ty_mono_wrt_ty_mono 0 (open_ty_mono_wrt_ty_mono tau1 tau2) ->
  degree_ty_mono_wrt_ty_mono 1 tau1.
Proof.
unfold open_ty_mono_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono_inv : lngen.

Lemma degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_inv :
forall rho1 tau1,
  degree_ty_rho_wrt_ty_mono 0 (open_ty_rho_wrt_ty_mono rho1 tau1) ->
  degree_ty_rho_wrt_ty_mono 1 rho1.
Proof.
unfold open_ty_rho_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono_inv : lngen.

Lemma degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_inv :
forall sig1 tau1,
  degree_ty_poly_wrt_ty_mono 0 (open_ty_poly_wrt_ty_mono sig1 tau1) ->
  degree_ty_poly_wrt_ty_mono 1 sig1.
Proof.
unfold open_ty_poly_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono_inv : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall t1 t2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm t1 t2) ->
  degree_tm_wrt_tm 1 t1.
Proof.
unfold open_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_ty_mono_inv :
forall t1 tau1 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_ty_mono t1 tau1) ->
  degree_tm_wrt_tm n1 t1.
Proof.
unfold open_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_ty_mono_inv : lngen.

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_tm_inv :
forall t1 t2 n1,
  degree_tm_wrt_ty_mono n1 (open_tm_wrt_tm t1 t2) ->
  degree_tm_wrt_ty_mono n1 t1.
Proof.
unfold open_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_open_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_inv :
forall t1 tau1,
  degree_tm_wrt_ty_mono 0 (open_tm_wrt_ty_mono t1 tau1) ->
  degree_tm_wrt_ty_mono 1 t1.
Proof.
unfold open_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_ty_mono_open_tm_wrt_ty_mono_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_inj_mutual :
(forall tau1 tau2 a1 n1,
  close_ty_mono_wrt_ty_mono_rec n1 a1 tau1 = close_ty_mono_wrt_ty_mono_rec n1 a1 tau2 ->
  tau1 = tau2).
Proof.
apply_mutual_ind ty_mono_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
  default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_inj :
forall tau1 tau2 a1 n1,
  close_ty_mono_wrt_ty_mono_rec n1 a1 tau1 = close_ty_mono_wrt_ty_mono_rec n1 a1 tau2 ->
  tau1 = tau2.
Proof.
pose proof close_ty_mono_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ty_mono_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_inj_mutual :
(forall rho1 rho2 a1 n1,
  close_ty_rho_wrt_ty_mono_rec n1 a1 rho1 = close_ty_rho_wrt_ty_mono_rec n1 a1 rho2 ->
  rho1 = rho2).
Proof.
apply_mutual_ind ty_rho_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_inj :
forall rho1 rho2 a1 n1,
  close_ty_rho_wrt_ty_mono_rec n1 a1 rho1 = close_ty_rho_wrt_ty_mono_rec n1 a1 rho2 ->
  rho1 = rho2.
Proof.
pose proof close_ty_rho_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ty_rho_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_inj_mutual :
(forall sig1 sig2 a1 n1,
  close_ty_poly_wrt_ty_mono_rec n1 a1 sig1 = close_ty_poly_wrt_ty_mono_rec n1 a1 sig2 ->
  sig1 = sig2).
Proof.
apply_mutual_ind ty_poly_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_inj :
forall sig1 sig2 a1 n1,
  close_ty_poly_wrt_ty_mono_rec n1 a1 sig1 = close_ty_poly_wrt_ty_mono_rec n1 a1 sig2 ->
  sig1 = sig2.
Proof.
pose proof close_ty_poly_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ty_poly_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj_mutual :
(forall t1 t2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 t1 = close_tm_wrt_tm_rec n1 x1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj :
forall t1 t2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 t1 = close_tm_wrt_tm_rec n1 x1 t2 ->
  t1 = t2.
Proof.
pose proof close_tm_wrt_tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_inj_mutual :
(forall t1 t2 a1 n1,
  close_tm_wrt_ty_mono_rec n1 a1 t1 = close_tm_wrt_ty_mono_rec n1 a1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_inj :
forall t1 t2 a1 n1,
  close_tm_wrt_ty_mono_rec n1 a1 t1 = close_tm_wrt_ty_mono_rec n1 a1 t2 ->
  t1 = t2.
Proof.
pose proof close_tm_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_tm_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

Lemma close_ty_mono_wrt_ty_mono_inj :
forall tau1 tau2 a1,
  close_ty_mono_wrt_ty_mono a1 tau1 = close_ty_mono_wrt_ty_mono a1 tau2 ->
  tau1 = tau2.
Proof.
unfold close_ty_mono_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate close_ty_mono_wrt_ty_mono_inj : lngen.

Lemma close_ty_rho_wrt_ty_mono_inj :
forall rho1 rho2 a1,
  close_ty_rho_wrt_ty_mono a1 rho1 = close_ty_rho_wrt_ty_mono a1 rho2 ->
  rho1 = rho2.
Proof.
unfold close_ty_rho_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate close_ty_rho_wrt_ty_mono_inj : lngen.

Lemma close_ty_poly_wrt_ty_mono_inj :
forall sig1 sig2 a1,
  close_ty_poly_wrt_ty_mono a1 sig1 = close_ty_poly_wrt_ty_mono a1 sig2 ->
  sig1 = sig2.
Proof.
unfold close_ty_poly_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate close_ty_poly_wrt_ty_mono_inj : lngen.

Lemma close_tm_wrt_tm_inj :
forall t1 t2 x1,
  close_tm_wrt_tm x1 t1 = close_tm_wrt_tm x1 t2 ->
  t1 = t2.
Proof.
unfold close_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate close_tm_wrt_tm_inj : lngen.

Lemma close_tm_wrt_ty_mono_inj :
forall t1 t2 a1,
  close_tm_wrt_ty_mono a1 t1 = close_tm_wrt_ty_mono a1 t2 ->
  t1 = t2.
Proof.
unfold close_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate close_tm_wrt_ty_mono_inj : lngen.

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 a1 n1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono_rec n1 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1) = tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec :
forall tau1 a1 n1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono_rec n1 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1) = tau1.
Proof.
pose proof close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 a1 n1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono_rec n1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1) = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec :
forall rho1 a1 n1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono_rec n1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1) = rho1.
Proof.
pose proof close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 a1 n1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono_rec n1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1) = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec :
forall sig1 a1 n1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono_rec n1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1) = sig1.
Proof.
pose proof close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1) = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall t1 x1 n1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1) = t1.
Proof.
pose proof close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono_rec n1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1) = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono_rec n1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1) = t1.
Proof.
pose proof close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono :
forall tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono a1 (open_ty_mono_wrt_ty_mono tau1 (ty_mono_var_f a1)) = tau1.
Proof.
unfold close_ty_mono_wrt_ty_mono; unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono using solve [auto] : lngen.

Lemma close_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono :
forall rho1 a1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono a1 (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a1)) = rho1.
Proof.
unfold close_ty_rho_wrt_ty_mono; unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono using solve [auto] : lngen.

Lemma close_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono :
forall sig1 a1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono a1 (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1)) = sig1.
Proof.
unfold close_ty_poly_wrt_ty_mono; unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono using solve [auto] : lngen.

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall t1 x1,
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm t1 (exp_var_f x1)) = t1.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

Lemma close_tm_wrt_ty_mono_open_tm_wrt_ty_mono :
forall t1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono a1 (open_tm_wrt_ty_mono t1 (ty_mono_var_f a1)) = t1.
Proof.
unfold close_tm_wrt_ty_mono; unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_ty_mono_open_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_tm_wrt_ty_mono_open_tm_wrt_ty_mono using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_close_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 a1 n1,
  open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) = tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_close_ty_mono_wrt_ty_mono_rec :
forall tau1 a1 n1,
  open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) = tau1.
Proof.
pose proof open_ty_mono_wrt_ty_mono_rec_close_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_mono_wrt_ty_mono_rec_close_ty_mono_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite open_ty_mono_wrt_ty_mono_rec_close_ty_mono_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_close_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 a1 n1,
  open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_close_ty_rho_wrt_ty_mono_rec :
forall rho1 a1 n1,
  open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) = rho1.
Proof.
pose proof open_ty_rho_wrt_ty_mono_rec_close_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_rho_wrt_ty_mono_rec_close_ty_rho_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite open_ty_rho_wrt_ty_mono_rec_close_ty_rho_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_close_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 a1 n1,
  open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_close_ty_poly_wrt_ty_mono_rec :
forall sig1 a1 n1,
  open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) = sig1.
Proof.
pose proof open_ty_poly_wrt_ty_mono_rec_close_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_poly_wrt_ty_mono_rec_close_ty_poly_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite open_ty_poly_wrt_ty_mono_rec_close_ty_poly_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  open_tm_wrt_tm_rec n1 (exp_var_f x1) (close_tm_wrt_tm_rec n1 x1 t1) = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  open_tm_wrt_tm_rec n1 (exp_var_f x1) (close_tm_wrt_tm_rec n1 x1 t1) = t1.
Proof.
pose proof open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_tm_wrt_ty_mono_rec n1 a1 t1) = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) (close_tm_wrt_ty_mono_rec n1 a1 t1) = t1.
Proof.
pose proof open_tm_wrt_ty_mono_rec_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_ty_mono_rec_close_tm_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite open_tm_wrt_ty_mono_rec_close_tm_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono :
forall tau1 a1,
  open_ty_mono_wrt_ty_mono (close_ty_mono_wrt_ty_mono a1 tau1) (ty_mono_var_f a1) = tau1.
Proof.
unfold close_ty_mono_wrt_ty_mono; unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_mono_wrt_ty_mono_close_ty_mono_wrt_ty_mono using solve [auto] : lngen.

Lemma open_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono :
forall rho1 a1,
  open_ty_rho_wrt_ty_mono (close_ty_rho_wrt_ty_mono a1 rho1) (ty_mono_var_f a1) = rho1.
Proof.
unfold close_ty_rho_wrt_ty_mono; unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_rho_wrt_ty_mono_close_ty_rho_wrt_ty_mono using solve [auto] : lngen.

Lemma open_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono :
forall sig1 a1,
  open_ty_poly_wrt_ty_mono (close_ty_poly_wrt_ty_mono a1 sig1) (ty_mono_var_f a1) = sig1.
Proof.
unfold close_ty_poly_wrt_ty_mono; unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_poly_wrt_ty_mono_close_ty_poly_wrt_ty_mono using solve [auto] : lngen.

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall t1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 t1) (exp_var_f x1) = t1.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma open_tm_wrt_ty_mono_close_tm_wrt_ty_mono :
forall t1 a1,
  open_tm_wrt_ty_mono (close_tm_wrt_ty_mono a1 t1) (ty_mono_var_f a1) = t1.
Proof.
unfold close_tm_wrt_ty_mono; unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_ty_mono_close_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_tm_wrt_ty_mono_close_tm_wrt_ty_mono using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_inj_mutual :
(forall tau2 tau1 a1 n1,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau2 = open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1 ->
  tau2 = tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_inj :
forall tau2 tau1 a1 n1,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau2 = open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1 ->
  tau2 = tau1.
Proof.
pose proof open_ty_mono_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ty_mono_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_inj_mutual :
(forall rho2 rho1 a1 n1,
  a1 `notin` ftv_mono_ty_rho rho2 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho2 = open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1 ->
  rho2 = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_inj :
forall rho2 rho1 a1 n1,
  a1 `notin` ftv_mono_ty_rho rho2 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho2 = open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1 ->
  rho2 = rho1.
Proof.
pose proof open_ty_rho_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ty_rho_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_inj_mutual :
(forall sig2 sig1 a1 n1,
  a1 `notin` ftv_mono_ty_poly sig2 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig2 = open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1 ->
  sig2 = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_inj :
forall sig2 sig1 a1 n1,
  a1 `notin` ftv_mono_ty_poly sig2 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig2 = open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1 ->
  sig2 = sig1.
Proof.
pose proof open_ty_poly_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ty_poly_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj_mutual :
(forall t2 t1 x1 n1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 (exp_var_f x1) t2 = open_tm_wrt_tm_rec n1 (exp_var_f x1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 (exp_var_f x1) t2 = open_tm_wrt_tm_rec n1 (exp_var_f x1) t1 ->
  t2 = t1.
Proof.
pose proof open_tm_wrt_tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_inj_mutual :
(forall t2 t1 a1 n1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t2 = open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_inj :
forall t2 t1 a1 n1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t2 = open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1 ->
  t2 = t1.
Proof.
pose proof open_tm_wrt_ty_mono_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_tm_wrt_ty_mono_rec_inj : lngen.

(* end hide *)

Lemma open_ty_mono_wrt_ty_mono_inj :
forall tau2 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono tau2 (ty_mono_var_f a1) = open_ty_mono_wrt_ty_mono tau1 (ty_mono_var_f a1) ->
  tau2 = tau1.
Proof.
unfold open_ty_mono_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate open_ty_mono_wrt_ty_mono_inj : lngen.

Lemma open_ty_rho_wrt_ty_mono_inj :
forall rho2 rho1 a1,
  a1 `notin` ftv_mono_ty_rho rho2 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono rho2 (ty_mono_var_f a1) = open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a1) ->
  rho2 = rho1.
Proof.
unfold open_ty_rho_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate open_ty_rho_wrt_ty_mono_inj : lngen.

Lemma open_ty_poly_wrt_ty_mono_inj :
forall sig2 sig1 a1,
  a1 `notin` ftv_mono_ty_poly sig2 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono sig2 (ty_mono_var_f a1) = open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1) ->
  sig2 = sig1.
Proof.
unfold open_ty_poly_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate open_ty_poly_wrt_ty_mono_inj : lngen.

Lemma open_tm_wrt_tm_inj :
forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm t2 (exp_var_f x1) = open_tm_wrt_tm t1 (exp_var_f x1) ->
  t2 = t1.
Proof.
unfold open_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate open_tm_wrt_tm_inj : lngen.

Lemma open_tm_wrt_ty_mono_inj :
forall t2 t1 a1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono t2 (ty_mono_var_f a1) = open_tm_wrt_ty_mono t1 (ty_mono_var_f a1) ->
  t2 = t1.
Proof.
unfold open_tm_wrt_ty_mono; eauto with lngen.
Qed.

#[export] Hint Immediate open_tm_wrt_ty_mono_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_ty_mono_wrt_ty_mono_of_lc_ty_mono_mutual :
(forall tau1,
  lc_ty_mono tau1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1).
Proof.
apply_mutual_ind lc_ty_mono_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ty_mono_wrt_ty_mono_of_lc_ty_mono :
forall tau1,
  lc_ty_mono tau1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1.
Proof.
pose proof degree_ty_mono_wrt_ty_mono_of_lc_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_mono_wrt_ty_mono_of_lc_ty_mono : lngen.

(* begin hide *)

Lemma degree_ty_rho_wrt_ty_mono_of_lc_ty_rho_mutual :
(forall rho1,
  lc_ty_rho rho1 ->
  degree_ty_rho_wrt_ty_mono 0 rho1).
Proof.
apply_mutual_ind lc_ty_rho_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ty_rho_wrt_ty_mono_of_lc_ty_rho :
forall rho1,
  lc_ty_rho rho1 ->
  degree_ty_rho_wrt_ty_mono 0 rho1.
Proof.
pose proof degree_ty_rho_wrt_ty_mono_of_lc_ty_rho_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_rho_wrt_ty_mono_of_lc_ty_rho : lngen.

(* begin hide *)

Lemma degree_ty_poly_wrt_ty_mono_of_lc_ty_poly_mutual :
(forall sig1,
  lc_ty_poly sig1 ->
  degree_ty_poly_wrt_ty_mono 0 sig1).
Proof.
apply_mutual_ind lc_ty_poly_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ty_poly_wrt_ty_mono_of_lc_ty_poly :
forall sig1,
  lc_ty_poly sig1 ->
  degree_ty_poly_wrt_ty_mono 0 sig1.
Proof.
pose proof degree_ty_poly_wrt_ty_mono_of_lc_ty_poly_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ty_poly_wrt_ty_mono_of_lc_ty_poly : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_of_lc_tm_mutual :
(forall t1,
  lc_tm t1 ->
  degree_tm_wrt_tm 0 t1).
Proof.
apply_mutual_ind lc_tm_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_tm_wrt_tm_of_lc_tm :
forall t1,
  lc_tm t1 ->
  degree_tm_wrt_tm 0 t1.
Proof.
pose proof degree_tm_wrt_tm_of_lc_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_ty_mono_of_lc_tm_mutual :
(forall t1,
  lc_tm t1 ->
  degree_tm_wrt_ty_mono 0 t1).
Proof.
apply_mutual_ind lc_tm_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_tm_wrt_ty_mono_of_lc_tm :
forall t1,
  lc_tm t1 ->
  degree_tm_wrt_ty_mono 0 t1.
Proof.
pose proof degree_tm_wrt_ty_mono_of_lc_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_ty_mono_of_lc_tm : lngen.

(* begin hide *)

Lemma lc_ty_mono_of_degree_size_mutual :
forall i1,
(forall tau1,
  size_ty_mono tau1 = i1 ->
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  lc_ty_mono tau1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_mono_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_mono_of_degree :
forall tau1,
  degree_ty_mono_wrt_ty_mono 0 tau1 ->
  lc_ty_mono tau1.
Proof.
intros tau1; intros;
pose proof (lc_ty_mono_of_degree_size_mutual (size_ty_mono tau1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_mono_of_degree : lngen.

(* begin hide *)

Lemma lc_ty_rho_of_degree_size_mutual :
forall i1,
(forall rho1,
  size_ty_rho rho1 = i1 ->
  degree_ty_rho_wrt_ty_mono 0 rho1 ->
  lc_ty_rho rho1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_rho_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_rho_of_degree :
forall rho1,
  degree_ty_rho_wrt_ty_mono 0 rho1 ->
  lc_ty_rho rho1.
Proof.
intros rho1; intros;
pose proof (lc_ty_rho_of_degree_size_mutual (size_ty_rho rho1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_rho_of_degree : lngen.

(* begin hide *)

Lemma lc_ty_poly_of_degree_size_mutual :
forall i1,
(forall sig1,
  size_ty_poly sig1 = i1 ->
  degree_ty_poly_wrt_ty_mono 0 sig1 ->
  lc_ty_poly sig1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_poly_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_poly_of_degree :
forall sig1,
  degree_ty_poly_wrt_ty_mono 0 sig1 ->
  lc_ty_poly sig1.
Proof.
intros sig1; intros;
pose proof (lc_ty_poly_of_degree_size_mutual (size_ty_poly sig1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_poly_of_degree : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_size_mutual :
forall i1,
(forall t1,
  size_tm t1 = i1 ->
  degree_tm_wrt_tm 0 t1 ->
  degree_tm_wrt_ty_mono 0 t1 ->
  lc_tm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind tm_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_tm_of_degree :
forall t1,
  degree_tm_wrt_tm 0 t1 ->
  degree_tm_wrt_ty_mono 0 t1 ->
  lc_tm t1.
Proof.
intros t1; intros;
pose proof (lc_tm_of_degree_size_mutual (size_tm t1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_of_degree : lngen.

Ltac ty_mono_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ty_mono_wrt_ty_mono_of_lc_ty_mono in J1; clear H
          end).

Ltac ty_rho_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ty_rho_wrt_ty_mono_of_lc_ty_rho in J1; clear H
          end).

Ltac ty_poly_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ty_poly_wrt_ty_mono_of_lc_ty_poly in J1; clear H
          end).

Ltac tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1;
              let J2 := fresh in pose proof H as J2; apply degree_tm_wrt_ty_mono_of_lc_tm in J2; clear H
          end).

Lemma lc_ty_poly_poly_gen_exists :
forall a1 sig1,
  lc_ty_poly (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1)) ->
  lc_ty_poly (ty_poly_poly_gen sig1).
Proof.
intros; ty_poly_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 t1,
  lc_tm (open_tm_wrt_tm t1 (exp_var_f x1)) ->
  lc_tm (exp_abs t1).
Proof.
intros; tm_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_typed_abs_exists :
forall x1 sig1 t1,
  lc_ty_poly sig1 ->
  lc_tm (open_tm_wrt_tm t1 (exp_var_f x1)) ->
  lc_tm (exp_typed_abs sig1 t1).
Proof.
intros; tm_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_let_exists :
forall x1 u1 t1,
  lc_tm u1 ->
  lc_tm (open_tm_wrt_tm t1 (exp_var_f x1)) ->
  lc_tm (exp_let u1 t1).
Proof.
intros; tm_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_ty_poly (ty_poly_poly_gen _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_ty_poly_poly_gen_exists a1) : core.

#[export] Hint Extern 1 (lc_tm (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (exp_typed_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_typed_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (exp_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_let_exists x1) : core.

Lemma lc_body_ty_mono_wrt_ty_mono :
forall tau1 tau2,
  body_ty_mono_wrt_ty_mono tau1 ->
  lc_ty_mono tau2 ->
  lc_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2).
Proof.
unfold body_ty_mono_wrt_ty_mono;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
ty_mono_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ty_mono_wrt_ty_mono : lngen.

Lemma lc_body_ty_rho_wrt_ty_mono :
forall rho1 tau1,
  body_ty_rho_wrt_ty_mono rho1 ->
  lc_ty_mono tau1 ->
  lc_ty_rho (open_ty_rho_wrt_ty_mono rho1 tau1).
Proof.
unfold body_ty_rho_wrt_ty_mono;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
ty_rho_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ty_rho_wrt_ty_mono : lngen.

Lemma lc_body_ty_poly_wrt_ty_mono :
forall sig1 tau1,
  body_ty_poly_wrt_ty_mono sig1 ->
  lc_ty_mono tau1 ->
  lc_ty_poly (open_ty_poly_wrt_ty_mono sig1 tau1).
Proof.
unfold body_ty_poly_wrt_ty_mono;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
ty_poly_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ty_poly_wrt_ty_mono : lngen.

Lemma lc_body_tm_wrt_tm :
forall t1 t2,
  body_tm_wrt_tm t1 ->
  lc_tm t2 ->
  lc_tm (open_tm_wrt_tm t1 t2).
Proof.
unfold body_tm_wrt_tm;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
tm_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_tm_wrt_ty_mono :
forall t1 tau1,
  body_tm_wrt_ty_mono t1 ->
  lc_ty_mono tau1 ->
  lc_tm (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold body_tm_wrt_ty_mono;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
tm_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_tm_wrt_ty_mono : lngen.

Lemma lc_body_ty_poly_poly_gen_1 :
forall sig1,
  lc_ty_poly (ty_poly_poly_gen sig1) ->
  body_ty_poly_wrt_ty_mono sig1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_ty_poly_poly_gen_1 : lngen.

Lemma lc_body_exp_abs_1 :
forall t1,
  lc_tm (exp_abs t1) ->
  body_tm_wrt_tm t1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_abs_1 : lngen.

Lemma lc_body_exp_typed_abs_2 :
forall sig1 t1,
  lc_tm (exp_typed_abs sig1 t1) ->
  body_tm_wrt_tm t1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_typed_abs_2 : lngen.

Lemma lc_body_exp_let_2 :
forall u1 t1,
  lc_tm (exp_let u1 t1) ->
  body_tm_wrt_tm t1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_let_2 : lngen.

(* begin hide *)

Lemma lc_ty_mono_unique_mutual :
(forall tau1 (proof2 proof3 : lc_ty_mono tau1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ty_mono_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ty_mono_unique :
forall tau1 (proof2 proof3 : lc_ty_mono tau1), proof2 = proof3.
Proof.
pose proof lc_ty_mono_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_mono_unique : lngen.

(* begin hide *)

Lemma lc_ty_rho_unique_mutual :
(forall rho1 (proof2 proof3 : lc_ty_rho rho1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ty_rho_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ty_rho_unique :
forall rho1 (proof2 proof3 : lc_ty_rho rho1), proof2 = proof3.
Proof.
pose proof lc_ty_rho_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_rho_unique : lngen.

(* begin hide *)

Lemma lc_ty_poly_unique_mutual :
(forall sig1 (proof2 proof3 : lc_ty_poly sig1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ty_poly_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ty_poly_unique :
forall sig1 (proof2 proof3 : lc_ty_poly sig1), proof2 = proof3.
Proof.
pose proof lc_ty_poly_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_poly_unique : lngen.

(* begin hide *)

Lemma lc_tm_unique_mutual :
(forall t1 (proof2 proof3 : lc_tm t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_tm_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_tm_unique :
forall t1 (proof2 proof3 : lc_tm t1), proof2 = proof3.
Proof.
pose proof lc_tm_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_unique : lngen.

(* begin hide *)

Lemma lc_ty_mono_of_lc_set_ty_mono_mutual :
(forall tau1, lc_set_ty_mono tau1 -> lc_ty_mono tau1).
Proof.
apply_mutual_ind lc_set_ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_mono_of_lc_set_ty_mono :
forall tau1, lc_set_ty_mono tau1 -> lc_ty_mono tau1.
Proof.
pose proof lc_ty_mono_of_lc_set_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_mono_of_lc_set_ty_mono : lngen.

(* begin hide *)

Lemma lc_ty_rho_of_lc_set_ty_rho_mutual :
(forall rho1, lc_set_ty_rho rho1 -> lc_ty_rho rho1).
Proof.
apply_mutual_ind lc_set_ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_rho_of_lc_set_ty_rho :
forall rho1, lc_set_ty_rho rho1 -> lc_ty_rho rho1.
Proof.
pose proof lc_ty_rho_of_lc_set_ty_rho_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_rho_of_lc_set_ty_rho : lngen.

(* begin hide *)

Lemma lc_ty_poly_of_lc_set_ty_poly_mutual :
(forall sig1, lc_set_ty_poly sig1 -> lc_ty_poly sig1).
Proof.
apply_mutual_ind lc_set_ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_poly_of_lc_set_ty_poly :
forall sig1, lc_set_ty_poly sig1 -> lc_ty_poly sig1.
Proof.
pose proof lc_ty_poly_of_lc_set_ty_poly_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ty_poly_of_lc_set_ty_poly : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_mutual :
(forall t1, lc_set_tm t1 -> lc_tm t1).
Proof.
apply_mutual_ind lc_set_tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall t1, lc_set_tm t1 -> lc_tm t1.
Proof.
pose proof lc_tm_of_lc_set_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_of_lc_set_tm : lngen.

(* begin hide *)

Lemma lc_set_ty_mono_of_lc_ty_mono_size_mutual :
forall i1,
(forall tau1,
  size_ty_mono tau1 = i1 ->
  lc_ty_mono tau1 ->
  lc_set_ty_mono tau1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_mono_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_mono_of_lc_ty_mono];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_ty_mono_of_lc_ty_mono :
forall tau1,
  lc_ty_mono tau1 ->
  lc_set_ty_mono tau1.
Proof.
intros tau1; intros;
pose proof (lc_set_ty_mono_of_lc_ty_mono_size_mutual (size_ty_mono tau1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ty_mono_of_lc_ty_mono : lngen.

(* begin hide *)

Lemma lc_set_ty_rho_of_lc_ty_rho_size_mutual :
forall i1,
(forall rho1,
  size_ty_rho rho1 = i1 ->
  lc_ty_rho rho1 ->
  lc_set_ty_rho rho1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_rho_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_rho_of_lc_ty_rho
 | apply lc_set_ty_mono_of_lc_ty_mono];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_ty_rho_of_lc_ty_rho :
forall rho1,
  lc_ty_rho rho1 ->
  lc_set_ty_rho rho1.
Proof.
intros rho1; intros;
pose proof (lc_set_ty_rho_of_lc_ty_rho_size_mutual (size_ty_rho rho1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ty_rho_of_lc_ty_rho : lngen.

(* begin hide *)

Lemma lc_set_ty_poly_of_lc_ty_poly_size_mutual :
forall i1,
(forall sig1,
  size_ty_poly sig1 = i1 ->
  lc_ty_poly sig1 ->
  lc_set_ty_poly sig1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_poly_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_rho_of_lc_ty_rho
 | apply lc_set_ty_poly_of_lc_ty_poly
 | apply lc_set_ty_mono_of_lc_ty_mono];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_ty_poly_of_lc_ty_poly :
forall sig1,
  lc_ty_poly sig1 ->
  lc_set_ty_poly sig1.
Proof.
intros sig1; intros;
pose proof (lc_set_ty_poly_of_lc_ty_poly_size_mutual (size_ty_poly sig1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ty_poly_of_lc_ty_poly : lngen.

(* begin hide *)

Lemma lc_set_tm_of_lc_tm_size_mutual :
forall i1,
(forall t1,
  size_tm t1 = i1 ->
  lc_tm t1 ->
  lc_set_tm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind tm_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_rho_of_lc_ty_rho
 | apply lc_set_ty_poly_of_lc_ty_poly
 | apply lc_set_tm_of_lc_tm
 | apply lc_set_ty_mono_of_lc_ty_mono];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_tm_of_lc_tm :
forall t1,
  lc_tm t1 ->
  lc_set_tm t1.
Proof.
intros t1; intros;
pose proof (lc_set_tm_of_lc_tm_size_mutual (size_tm t1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_tm_of_lc_tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono_mutual :
(forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono_rec n1 a1 tau1 = tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono :
forall tau1 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono_rec n1 a1 tau1 = tau1.
Proof.
pose proof close_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono_mutual :
(forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono_rec n1 a1 rho1 = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono :
forall rho1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono_rec n1 a1 rho1 = rho1.
Proof.
pose proof close_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono_mutual :
(forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono_rec n1 a1 sig1 = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono :
forall sig1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono_rec n1 a1 sig1 = sig1.
Proof.
pose proof close_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 t1 = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall t1 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm_rec n1 x1 t1 = t1.
Proof.
pose proof close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono_mutual :
(forall t1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono_rec n1 a1 t1 = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono :
forall t1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono_rec n1 a1 t1 = t1.
Proof.
pose proof close_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite close_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

Lemma close_ty_mono_wrt_ty_mono_lc_ty_mono :
forall tau1 a1,
  lc_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  close_ty_mono_wrt_ty_mono a1 tau1 = tau1.
Proof.
unfold close_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_mono_wrt_ty_mono_lc_ty_mono : lngen.
#[export] Hint Rewrite close_ty_mono_wrt_ty_mono_lc_ty_mono using solve [auto] : lngen.

Lemma close_ty_rho_wrt_ty_mono_lc_ty_rho :
forall rho1 a1,
  lc_ty_rho rho1 ->
  a1 `notin` ftv_mono_ty_rho rho1 ->
  close_ty_rho_wrt_ty_mono a1 rho1 = rho1.
Proof.
unfold close_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_rho_wrt_ty_mono_lc_ty_rho : lngen.
#[export] Hint Rewrite close_ty_rho_wrt_ty_mono_lc_ty_rho using solve [auto] : lngen.

Lemma close_ty_poly_wrt_ty_mono_lc_ty_poly :
forall sig1 a1,
  lc_ty_poly sig1 ->
  a1 `notin` ftv_mono_ty_poly sig1 ->
  close_ty_poly_wrt_ty_mono a1 sig1 = sig1.
Proof.
unfold close_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_ty_poly_wrt_ty_mono_lc_ty_poly : lngen.
#[export] Hint Rewrite close_ty_poly_wrt_ty_mono_lc_ty_poly using solve [auto] : lngen.

Lemma close_tm_wrt_tm_lc_tm :
forall t1 x1,
  lc_tm t1 ->
  x1 `notin` fv_tm t1 ->
  close_tm_wrt_tm x1 t1 = t1.
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma close_tm_wrt_ty_mono_lc_tm :
forall t1 a1,
  lc_tm t1 ->
  a1 `notin` ftv_mono_tm t1 ->
  close_tm_wrt_ty_mono a1 t1 = t1.
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_ty_mono_lc_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_ty_mono_lc_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono_mutual :
(forall tau2 tau1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  open_ty_mono_wrt_ty_mono_rec n1 tau1 tau2 = tau2).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono :
forall tau2 tau1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  open_ty_mono_wrt_ty_mono_rec n1 tau1 tau2 = tau2.
Proof.
pose proof open_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_mono_wrt_ty_mono_rec_degree_ty_mono_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono_mutual :
(forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1 = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono :
forall rho1 tau1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1 = rho1.
Proof.
pose proof open_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_rho_wrt_ty_mono_rec_degree_ty_rho_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono_mutual :
(forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1 = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono :
forall sig1 tau1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1 = sig1.
Proof.
pose proof open_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_ty_poly_wrt_ty_mono_rec_degree_ty_poly_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall t2 t1 n1,
  degree_tm_wrt_tm n1 t2 ->
  open_tm_wrt_tm_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall t2 t1 n1,
  degree_tm_wrt_tm n1 t2 ->
  open_tm_wrt_tm_rec n1 t1 t2 = t2.
Proof.
pose proof open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono_mutual :
(forall t1 tau1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  open_tm_wrt_ty_mono_rec n1 tau1 t1 = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono :
forall t1 tau1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  open_tm_wrt_ty_mono_rec n1 tau1 t1 = t1.
Proof.
pose proof open_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite open_tm_wrt_ty_mono_rec_degree_tm_wrt_ty_mono using solve [auto] : lngen.

(* end hide *)

Lemma open_ty_mono_wrt_ty_mono_lc_ty_mono :
forall tau2 tau1,
  lc_ty_mono tau2 ->
  open_ty_mono_wrt_ty_mono tau2 tau1 = tau2.
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_mono_wrt_ty_mono_lc_ty_mono : lngen.
#[export] Hint Rewrite open_ty_mono_wrt_ty_mono_lc_ty_mono using solve [auto] : lngen.

Lemma open_ty_rho_wrt_ty_mono_lc_ty_rho :
forall rho1 tau1,
  lc_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono rho1 tau1 = rho1.
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_rho_wrt_ty_mono_lc_ty_rho : lngen.
#[export] Hint Rewrite open_ty_rho_wrt_ty_mono_lc_ty_rho using solve [auto] : lngen.

Lemma open_ty_poly_wrt_ty_mono_lc_ty_poly :
forall sig1 tau1,
  lc_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono sig1 tau1 = sig1.
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_ty_poly_wrt_ty_mono_lc_ty_poly : lngen.
#[export] Hint Rewrite open_ty_poly_wrt_ty_mono_lc_ty_poly using solve [auto] : lngen.

Lemma open_tm_wrt_tm_lc_tm :
forall t2 t1,
  lc_tm t2 ->
  open_tm_wrt_tm t2 t1 = t2.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma open_tm_wrt_ty_mono_lc_tm :
forall t1 tau1,
  lc_tm t1 ->
  open_tm_wrt_ty_mono t1 tau1 = t1.
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_ty_mono_lc_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_ty_mono_lc_tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau1 a1 n1,
  ftv_mono_ty_mono (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) [=] remove a1 (ftv_mono_ty_mono tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec :
forall tau1 a1 n1,
  ftv_mono_ty_mono (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1) [=] remove a1 (ftv_mono_ty_mono tau1).
Proof.
pose proof ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 a1 n1,
  ftv_mono_ty_rho (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) [=] remove a1 (ftv_mono_ty_rho rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec :
forall rho1 a1 n1,
  ftv_mono_ty_rho (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1) [=] remove a1 (ftv_mono_ty_rho rho1).
Proof.
pose proof ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 a1 n1,
  ftv_mono_ty_poly (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) [=] remove a1 (ftv_mono_ty_poly sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec :
forall sig1 a1 n1,
  ftv_mono_ty_poly (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1) [=] remove a1 (ftv_mono_ty_poly sig1).
Proof.
pose proof ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] remove x1 (fv_tm t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] remove x1 (fv_tm t1).
Proof.
pose proof fv_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  fv_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) [=] fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  fv_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) [=] fv_tm t1.
Proof.
pose proof fv_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 x1 n1,
  ftv_mono_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] ftv_mono_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_close_tm_wrt_tm_rec :
forall t1 x1 n1,
  ftv_mono_tm (close_tm_wrt_tm_rec n1 x1 t1) [=] ftv_mono_tm t1.
Proof.
pose proof ftv_mono_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite ftv_mono_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 a1 n1,
  ftv_mono_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) [=] remove a1 (ftv_mono_tm t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_close_tm_wrt_ty_mono_rec :
forall t1 a1 n1,
  ftv_mono_tm (close_tm_wrt_ty_mono_rec n1 a1 t1) [=] remove a1 (ftv_mono_tm t1).
Proof.
pose proof ftv_mono_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_close_tm_wrt_ty_mono_rec : lngen.
#[export] Hint Rewrite ftv_mono_tm_close_tm_wrt_ty_mono_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono :
forall tau1 a1,
  ftv_mono_ty_mono (close_ty_mono_wrt_ty_mono a1 tau1) [=] remove a1 (ftv_mono_ty_mono tau1).
Proof.
unfold close_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono : lngen.
#[export] Hint Rewrite ftv_mono_ty_mono_close_ty_mono_wrt_ty_mono using solve [auto] : lngen.

Lemma ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono :
forall rho1 a1,
  ftv_mono_ty_rho (close_ty_rho_wrt_ty_mono a1 rho1) [=] remove a1 (ftv_mono_ty_rho rho1).
Proof.
unfold close_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono : lngen.
#[export] Hint Rewrite ftv_mono_ty_rho_close_ty_rho_wrt_ty_mono using solve [auto] : lngen.

Lemma ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono :
forall sig1 a1,
  ftv_mono_ty_poly (close_ty_poly_wrt_ty_mono a1 sig1) [=] remove a1 (ftv_mono_ty_poly sig1).
Proof.
unfold close_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono : lngen.
#[export] Hint Rewrite ftv_mono_ty_poly_close_ty_poly_wrt_ty_mono using solve [auto] : lngen.

Lemma fv_tm_close_tm_wrt_tm :
forall t1 x1,
  fv_tm (close_tm_wrt_tm x1 t1) [=] remove x1 (fv_tm t1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_close_tm_wrt_ty_mono :
forall t1 a1,
  fv_tm (close_tm_wrt_ty_mono a1 t1) [=] fv_tm t1.
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_ty_mono using solve [auto] : lngen.

Lemma ftv_mono_tm_close_tm_wrt_tm :
forall t1 x1,
  ftv_mono_tm (close_tm_wrt_tm x1 t1) [=] ftv_mono_tm t1.
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite ftv_mono_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma ftv_mono_tm_close_tm_wrt_ty_mono :
forall t1 a1,
  ftv_mono_tm (close_tm_wrt_ty_mono a1 t1) [=] remove a1 (ftv_mono_tm t1).
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_close_tm_wrt_ty_mono : lngen.
#[export] Hint Rewrite ftv_mono_tm_close_tm_wrt_ty_mono using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_lower_mutual :
(forall tau1 tau2 n1,
  ftv_mono_ty_mono tau1 [<=] ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_lower :
forall tau1 tau2 n1,
  ftv_mono_ty_mono tau1 [<=] ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1).
Proof.
pose proof ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_lower_mutual :
(forall rho1 tau1 n1,
  ftv_mono_ty_rho rho1 [<=] ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_lower :
forall rho1 tau1 n1,
  ftv_mono_ty_rho rho1 [<=] ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1).
Proof.
pose proof ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_lower_mutual :
(forall sig1 tau1 n1,
  ftv_mono_ty_poly sig1 [<=] ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_lower :
forall sig1 tau1 n1,
  ftv_mono_ty_poly sig1 [<=] ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1).
Proof.
pose proof ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall t1 t2 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower :
forall t1 t2 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm_rec n1 t2 t1).
Proof.
pose proof fv_tm_open_tm_wrt_tm_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_ty_mono_rec_lower_mutual :
(forall t1 tau1 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_ty_mono_rec_lower :
forall t1 tau1 n1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1).
Proof.
pose proof fv_tm_open_tm_wrt_ty_mono_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_ty_mono_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall t1 t2 n1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_tm_rec n1 t2 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_tm_rec_lower :
forall t1 t2 n1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_tm_rec n1 t2 t1).
Proof.
pose proof ftv_mono_tm_open_tm_wrt_tm_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_rec_lower_mutual :
(forall t1 tau1 n1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_rec_lower :
forall t1 tau1 n1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1).
Proof.
pose proof ftv_mono_tm_open_tm_wrt_ty_mono_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_ty_mono_rec_lower : lngen.

(* end hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_lower :
forall tau1 tau2,
  ftv_mono_ty_mono tau1 [<=] ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2).
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_lower : lngen.

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_lower :
forall rho1 tau1,
  ftv_mono_ty_rho rho1 [<=] ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono rho1 tau1).
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_lower : lngen.

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_lower :
forall sig1 tau1,
  ftv_mono_ty_poly sig1 [<=] ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono sig1 tau1).
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_lower : lngen.

Lemma fv_tm_open_tm_wrt_tm_lower :
forall t1 t2,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_tm t1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_lower : lngen.

Lemma fv_tm_open_tm_wrt_ty_mono_lower :
forall t1 tau1,
  fv_tm t1 [<=] fv_tm (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_ty_mono_lower : lngen.

Lemma ftv_mono_tm_open_tm_wrt_tm_lower :
forall t1 t2,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_tm t1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_tm_lower : lngen.

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_lower :
forall t1 tau1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (open_tm_wrt_ty_mono t1 tau1).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_ty_mono_lower : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_upper_mutual :
(forall tau1 tau2 n1,
  ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1) [<=] ftv_mono_ty_mono tau2 `union` ftv_mono_ty_mono tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_upper :
forall tau1 tau2 n1,
  ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1) [<=] ftv_mono_ty_mono tau2 `union` ftv_mono_ty_mono tau1.
Proof.
pose proof ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_upper_mutual :
(forall rho1 tau1 n1,
  ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_rho rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_upper :
forall rho1 tau1 n1,
  ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_rho rho1.
Proof.
pose proof ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_upper_mutual :
(forall sig1 tau1 n1,
  ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_poly sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_upper :
forall sig1 tau1 n1,
  ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_poly sig1.
Proof.
pose proof ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall t1 t2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] fv_tm t2 `union` fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper :
forall t1 t2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] fv_tm t2 `union` fv_tm t1.
Proof.
pose proof fv_tm_open_tm_wrt_tm_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_ty_mono_rec_upper_mutual :
(forall t1 tau1 n1,
  fv_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1) [<=] fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_ty_mono_rec_upper :
forall t1 tau1 n1,
  fv_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1) [<=] fv_tm t1.
Proof.
pose proof fv_tm_open_tm_wrt_ty_mono_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_ty_mono_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall t1 t2 n1,
  ftv_mono_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] ftv_mono_tm t2 `union` ftv_mono_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_tm_rec_upper :
forall t1 t2 n1,
  ftv_mono_tm (open_tm_wrt_tm_rec n1 t2 t1) [<=] ftv_mono_tm t2 `union` ftv_mono_tm t1.
Proof.
pose proof ftv_mono_tm_open_tm_wrt_tm_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_rec_upper_mutual :
(forall t1 tau1 n1,
  ftv_mono_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_rec_upper :
forall t1 tau1 n1,
  ftv_mono_tm (open_tm_wrt_ty_mono_rec n1 tau1 t1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_tm t1.
Proof.
pose proof ftv_mono_tm_open_tm_wrt_ty_mono_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_ty_mono_rec_upper : lngen.

(* end hide *)

Lemma ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_upper :
forall tau1 tau2,
  ftv_mono_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2) [<=] ftv_mono_ty_mono tau2 `union` ftv_mono_ty_mono tau1.
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_open_ty_mono_wrt_ty_mono_upper : lngen.

Lemma ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_upper :
forall rho1 tau1,
  ftv_mono_ty_rho (open_ty_rho_wrt_ty_mono rho1 tau1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_rho rho1.
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_open_ty_rho_wrt_ty_mono_upper : lngen.

Lemma ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_upper :
forall sig1 tau1,
  ftv_mono_ty_poly (open_ty_poly_wrt_ty_mono sig1 tau1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_ty_poly sig1.
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_upper : lngen.

Lemma fv_tm_open_tm_wrt_tm_upper :
forall t1 t2,
  fv_tm (open_tm_wrt_tm t1 t2) [<=] fv_tm t2 `union` fv_tm t1.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_upper : lngen.

Lemma fv_tm_open_tm_wrt_ty_mono_upper :
forall t1 tau1,
  fv_tm (open_tm_wrt_ty_mono t1 tau1) [<=] fv_tm t1.
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_ty_mono_upper : lngen.

Lemma ftv_mono_tm_open_tm_wrt_tm_upper :
forall t1 t2,
  ftv_mono_tm (open_tm_wrt_tm t1 t2) [<=] ftv_mono_tm t2 `union` ftv_mono_tm t1.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_tm_upper : lngen.

Lemma ftv_mono_tm_open_tm_wrt_ty_mono_upper :
forall t1 tau1,
  ftv_mono_tm (open_tm_wrt_ty_mono t1 tau1) [<=] ftv_mono_ty_mono tau1 `union` ftv_mono_tm t1.
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve ftv_mono_tm_open_tm_wrt_ty_mono_upper : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_fresh_mutual :
(forall tau1 tau2 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1) [=] ftv_mono_ty_mono tau1).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_fresh :
forall tau1 tau2 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1) [=] ftv_mono_ty_mono tau1.
Proof.
pose proof ftv_mono_ty_mono_subst_ty_mono_ty_mono_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_subst_ty_mono_ty_mono_fresh : lngen.
#[export] Hint Rewrite ftv_mono_ty_mono_subst_ty_mono_ty_mono_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_fresh_mutual :
(forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1) [=] ftv_mono_ty_rho rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_fresh :
forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1) [=] ftv_mono_ty_rho rho1.
Proof.
pose proof ftv_mono_ty_rho_subst_ty_mono_ty_rho_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_subst_ty_mono_ty_rho_fresh : lngen.
#[export] Hint Rewrite ftv_mono_ty_rho_subst_ty_mono_ty_rho_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_fresh_mutual :
(forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1) [=] ftv_mono_ty_poly sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_fresh :
forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1) [=] ftv_mono_ty_poly sig1.
Proof.
pose proof ftv_mono_ty_poly_subst_ty_mono_ty_poly_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_subst_ty_mono_ty_poly_fresh : lngen.
#[export] Hint Rewrite ftv_mono_ty_poly_subst_ty_mono_ty_poly_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_fresh_mutual :
(forall t1 t2 x1,
  x1 `notin` fv_tm t1 ->
  fv_tm (subst_tm t2 x1 t1) [=] fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_fresh :
forall t1 t2 x1,
  x1 `notin` fv_tm t1 ->
  fv_tm (subst_tm t2 x1 t1) [=] fv_tm t1.
Proof.
pose proof fv_tm_subst_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_fresh : lngen.
#[export] Hint Rewrite fv_tm_subst_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_tm_fresh_mutual :
(forall t1 tau1 a1,
  fv_tm (subst_ty_mono_tm tau1 a1 t1) [=] fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_tm_fresh :
forall t1 tau1 a1,
  fv_tm (subst_ty_mono_tm tau1 a1 t1) [=] fv_tm t1.
Proof.
pose proof ftv_mono_tm_subst_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_tm_fresh : lngen.
#[export] Hint Rewrite ftv_mono_tm_subst_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_fresh_mutual :
(forall t1 tau1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1) [=] ftv_mono_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_fresh :
forall t1 tau1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1) [=] ftv_mono_tm t1.
Proof.
pose proof ftv_mono_tm_subst_ty_mono_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_ty_mono_tm_fresh : lngen.
#[export] Hint Rewrite ftv_mono_tm_subst_ty_mono_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_lower_mutual :
(forall tau1 tau2 a1,
  remove a1 (ftv_mono_ty_mono tau1) [<=] ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_lower :
forall tau1 tau2 a1,
  remove a1 (ftv_mono_ty_mono tau1) [<=] ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1).
Proof.
pose proof ftv_mono_ty_mono_subst_ty_mono_ty_mono_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_subst_ty_mono_ty_mono_lower : lngen.

(* begin hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_lower_mutual :
(forall rho1 tau1 a1,
  remove a1 (ftv_mono_ty_rho rho1) [<=] ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_lower :
forall rho1 tau1 a1,
  remove a1 (ftv_mono_ty_rho rho1) [<=] ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof ftv_mono_ty_rho_subst_ty_mono_ty_rho_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_subst_ty_mono_ty_rho_lower : lngen.

(* begin hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_lower_mutual :
(forall sig1 tau1 a1,
  remove a1 (ftv_mono_ty_poly sig1) [<=] ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_lower :
forall sig1 tau1 a1,
  remove a1 (ftv_mono_ty_poly sig1) [<=] ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof ftv_mono_ty_poly_subst_ty_mono_ty_poly_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_subst_ty_mono_ty_poly_lower : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_lower_mutual :
(forall t1 t2 x1,
  remove x1 (fv_tm t1) [<=] fv_tm (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_lower :
forall t1 t2 x1,
  remove x1 (fv_tm t1) [<=] fv_tm (subst_tm t2 x1 t1).
Proof.
pose proof fv_tm_subst_tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_subst_ty_mono_tm_lower_mutual :
(forall t1 tau1 a1,
  fv_tm t1 [<=] fv_tm (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_ty_mono_tm_lower :
forall t1 tau1 a1,
  fv_tm t1 [<=] fv_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof fv_tm_subst_ty_mono_tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_ty_mono_tm_lower : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_tm_lower_mutual :
(forall t1 t2 x1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_tm_lower :
forall t1 t2 x1,
  ftv_mono_tm t1 [<=] ftv_mono_tm (subst_tm t2 x1 t1).
Proof.
pose proof ftv_mono_tm_subst_tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_tm_lower : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_lower_mutual :
(forall t1 tau1 a1,
  remove a1 (ftv_mono_tm t1) [<=] ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_lower :
forall t1 tau1 a1,
  remove a1 (ftv_mono_tm t1) [<=] ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof ftv_mono_tm_subst_ty_mono_tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_ty_mono_tm_lower : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_notin_mutual :
(forall tau1 tau2 a1 a2,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_notin :
forall tau1 tau2 a1 a2,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1).
Proof.
pose proof ftv_mono_ty_mono_subst_ty_mono_ty_mono_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_subst_ty_mono_ty_mono_notin : lngen.

(* begin hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_notin_mutual :
(forall rho1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_rho rho1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_notin :
forall rho1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_rho rho1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof ftv_mono_ty_rho_subst_ty_mono_ty_rho_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_subst_ty_mono_ty_rho_notin : lngen.

(* begin hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_notin_mutual :
(forall sig1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_poly sig1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_notin :
forall sig1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_poly sig1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof ftv_mono_ty_poly_subst_ty_mono_ty_poly_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_subst_ty_mono_ty_poly_notin : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_notin_mutual :
(forall t1 t2 x1 x2,
  x2 `notin` fv_tm t1 ->
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_notin :
forall t1 t2 x1 x2,
  x2 `notin` fv_tm t1 ->
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm (subst_tm t2 x1 t1).
Proof.
pose proof fv_tm_subst_tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_notin : lngen.

(* begin hide *)

Lemma fv_tm_subst_ty_mono_tm_notin_mutual :
(forall t1 tau1 a1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_ty_mono_tm_notin :
forall t1 tau1 a1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof fv_tm_subst_ty_mono_tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_ty_mono_tm_notin : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_tm_notin_mutual :
(forall t1 t2 x1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_tm_notin :
forall t1 t2 x1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm (subst_tm t2 x1 t1).
Proof.
pose proof ftv_mono_tm_subst_tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_tm_notin : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_notin_mutual :
(forall t1 tau1 a1 a2,
  a2 `notin` ftv_mono_tm t1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_notin :
forall t1 tau1 a1 a2,
  a2 `notin` ftv_mono_tm t1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof ftv_mono_tm_subst_ty_mono_tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_ty_mono_tm_notin : lngen.

(* begin hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_upper_mutual :
(forall tau1 tau2 a1,
  ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1) [<=] ftv_mono_ty_mono tau2 `union` remove a1 (ftv_mono_ty_mono tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_mono_subst_ty_mono_ty_mono_upper :
forall tau1 tau2 a1,
  ftv_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1) [<=] ftv_mono_ty_mono tau2 `union` remove a1 (ftv_mono_ty_mono tau1).
Proof.
pose proof ftv_mono_ty_mono_subst_ty_mono_ty_mono_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_mono_subst_ty_mono_ty_mono_upper : lngen.

(* begin hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_upper_mutual :
(forall rho1 tau1 a1,
  ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_ty_rho rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_rho_subst_ty_mono_ty_rho_upper :
forall rho1 tau1 a1,
  ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_ty_rho rho1).
Proof.
pose proof ftv_mono_ty_rho_subst_ty_mono_ty_rho_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_rho_subst_ty_mono_ty_rho_upper : lngen.

(* begin hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_upper_mutual :
(forall sig1 tau1 a1,
  ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_ty_poly sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_ty_poly_subst_ty_mono_ty_poly_upper :
forall sig1 tau1 a1,
  ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_ty_poly sig1).
Proof.
pose proof ftv_mono_ty_poly_subst_ty_mono_ty_poly_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_ty_poly_subst_ty_mono_ty_poly_upper : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_upper_mutual :
(forall t1 t2 x1,
  fv_tm (subst_tm t2 x1 t1) [<=] fv_tm t2 `union` remove x1 (fv_tm t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_upper :
forall t1 t2 x1,
  fv_tm (subst_tm t2 x1 t1) [<=] fv_tm t2 `union` remove x1 (fv_tm t1).
Proof.
pose proof fv_tm_subst_tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_upper : lngen.

(* begin hide *)

Lemma fv_tm_subst_ty_mono_tm_upper_mutual :
(forall t1 tau1 a1,
  fv_tm (subst_ty_mono_tm tau1 a1 t1) [<=] fv_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_ty_mono_tm_upper :
forall t1 tau1 a1,
  fv_tm (subst_ty_mono_tm tau1 a1 t1) [<=] fv_tm t1.
Proof.
pose proof fv_tm_subst_ty_mono_tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_ty_mono_tm_upper : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_tm_upper_mutual :
(forall t1 t2 x1,
  ftv_mono_tm (subst_tm t2 x1 t1) [<=] ftv_mono_tm t2 `union` ftv_mono_tm t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_tm_upper :
forall t1 t2 x1,
  ftv_mono_tm (subst_tm t2 x1 t1) [<=] ftv_mono_tm t2 `union` ftv_mono_tm t1.
Proof.
pose proof ftv_mono_tm_subst_tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_tm_upper : lngen.

(* begin hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_upper_mutual :
(forall t1 tau1 a1,
  ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_tm t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_mono_tm_subst_ty_mono_tm_upper :
forall t1 tau1 a1,
  ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1) [<=] ftv_mono_ty_mono tau1 `union` remove a1 (ftv_mono_tm t1).
Proof.
pose proof ftv_mono_tm_subst_ty_mono_tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_mono_tm_subst_ty_mono_tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau2 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (close_ty_mono_wrt_ty_mono_rec n1 a2 tau2) = close_ty_mono_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_mono tau1 a1 tau2)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec :
forall tau2 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (close_ty_mono_wrt_ty_mono_rec n1 a2 tau2) = close_ty_mono_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
pose proof subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (close_ty_rho_wrt_ty_mono_rec n1 a2 rho1) = close_ty_rho_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec :
forall rho1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (close_ty_rho_wrt_ty_mono_rec n1 a2 rho1) = close_ty_rho_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (close_ty_poly_wrt_ty_mono_rec n1 a2 sig1) = close_ty_poly_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec :
forall sig1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (close_ty_poly_wrt_ty_mono_rec n1 a2 sig1) = close_ty_poly_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec : lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_mutual :
(forall t2 t1 x1 x2 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm_rec n1 x2 t2) = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_close_tm_wrt_tm_rec :
forall t2 t1 x1 x2 n1,
  degree_tm_wrt_tm n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm_rec n1 x2 t2) = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 t2).
Proof.
pose proof subst_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec : lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t2 t1 a1 x1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  x1 `notin` ftv_mono_tm t1 ->
  subst_tm t1 a1 (close_tm_wrt_ty_mono_rec n1 x1 t2) = close_tm_wrt_ty_mono_rec n1 x1 (subst_tm t1 a1 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_close_tm_wrt_ty_mono_rec :
forall t2 t1 a1 x1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  x1 `notin` ftv_mono_tm t1 ->
  subst_tm t1 a1 (close_tm_wrt_ty_mono_rec n1 x1 t2) = close_tm_wrt_ty_mono_rec n1 x1 (subst_tm t1 a1 t2).
Proof.
pose proof subst_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_ty_mono_rec : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_tm_rec_mutual :
(forall t1 tau1 x1 a1 n1,
  subst_ty_mono_tm tau1 x1 (close_tm_wrt_tm_rec n1 a1 t1) = close_tm_wrt_tm_rec n1 a1 (subst_ty_mono_tm tau1 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_tm_rec :
forall t1 tau1 x1 a1 n1,
  subst_ty_mono_tm tau1 x1 (close_tm_wrt_tm_rec n1 a1 t1) = close_tm_wrt_tm_rec n1 a1 (subst_ty_mono_tm tau1 x1 t1).
Proof.
pose proof subst_ty_mono_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_tm_rec : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (close_tm_wrt_ty_mono_rec n1 a2 t1) = close_tm_wrt_ty_mono_rec n1 a2 (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono_rec :
forall t1 tau1 a1 a2 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (close_tm_wrt_ty_mono_rec n1 a2 t1) = close_tm_wrt_ty_mono_rec n1 a2 (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_ty_mono_rec : lngen.

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono :
forall tau2 tau1 a1 a2,
  lc_ty_mono tau1 ->  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (close_ty_mono_wrt_ty_mono a2 tau2) = close_ty_mono_wrt_ty_mono a2 (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
unfold close_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono :
forall rho1 tau1 a1 a2,
  lc_ty_mono tau1 ->  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (close_ty_rho_wrt_ty_mono a2 rho1) = close_ty_rho_wrt_ty_mono a2 (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
unfold close_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono :
forall sig1 tau1 a1 a2,
  lc_ty_mono tau1 ->  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (close_ty_poly_wrt_ty_mono a2 sig1) = close_ty_poly_wrt_ty_mono a2 (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
unfold close_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono : lngen.

Lemma subst_tm_close_tm_wrt_tm :
forall t2 t1 x1 x2,
  lc_tm t1 ->  x1 <> x2 ->
  x2 `notin` fv_tm t1 ->
  subst_tm t1 x1 (close_tm_wrt_tm x2 t2) = close_tm_wrt_tm x2 (subst_tm t1 x1 t2).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm : lngen.

Lemma subst_tm_close_tm_wrt_ty_mono :
forall t2 t1 a1 x1,
  lc_tm t1 ->  x1 `notin` ftv_mono_tm t1 ->
  subst_tm t1 a1 (close_tm_wrt_ty_mono x1 t2) = close_tm_wrt_ty_mono x1 (subst_tm t1 a1 t2).
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_ty_mono : lngen.

Lemma subst_ty_mono_tm_close_tm_wrt_tm :
forall t1 tau1 x1 a1,
  lc_ty_mono tau1 ->  subst_ty_mono_tm tau1 x1 (close_tm_wrt_tm a1 t1) = close_tm_wrt_tm a1 (subst_ty_mono_tm tau1 x1 t1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_tm : lngen.

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono :
forall t1 tau1 a1 a2,
  lc_ty_mono tau1 ->  a1 <> a2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (close_tm_wrt_ty_mono a2 t1) = close_tm_wrt_ty_mono a2 (subst_ty_mono_tm tau1 a1 t1).
Proof.
unfold close_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_degree_ty_mono_wrt_ty_mono_mutual :
(forall tau1 tau2 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  degree_ty_mono_wrt_ty_mono n1 (subst_ty_mono_ty_mono tau2 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_degree_ty_mono_wrt_ty_mono :
forall tau1 tau2 a1 n1,
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_mono_wrt_ty_mono n1 tau2 ->
  degree_ty_mono_wrt_ty_mono n1 (subst_ty_mono_ty_mono tau2 a1 tau1).
Proof.
pose proof subst_ty_mono_ty_mono_degree_ty_mono_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_degree_ty_mono_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_degree_ty_rho_wrt_ty_mono_mutual :
(forall rho1 tau1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_rho_wrt_ty_mono n1 (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_degree_ty_rho_wrt_ty_mono :
forall rho1 tau1 a1 n1,
  degree_ty_rho_wrt_ty_mono n1 rho1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_rho_wrt_ty_mono n1 (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_degree_ty_rho_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_degree_ty_rho_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_degree_ty_poly_wrt_ty_mono_mutual :
(forall sig1 tau1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_poly_wrt_ty_mono n1 (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_degree_ty_poly_wrt_ty_mono :
forall sig1 tau1 a1 n1,
  degree_ty_poly_wrt_ty_mono n1 sig1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_ty_poly_wrt_ty_mono n1 (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_degree_ty_poly_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_degree_ty_poly_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_tm_degree_tm_wrt_tm_mutual :
(forall t1 t2 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_degree_tm_wrt_tm :
forall t1 t2 x1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 t2 ->
  degree_tm_wrt_tm n1 (subst_tm t2 x1 t1).
Proof.
pose proof subst_tm_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_degree_tm_wrt_ty_mono_mutual :
(forall t1 t2 x1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 t2 ->
  degree_tm_wrt_ty_mono n1 (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_degree_tm_wrt_ty_mono :
forall t1 t2 x1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_tm_wrt_ty_mono n1 t2 ->
  degree_tm_wrt_ty_mono n1 (subst_tm t2 x1 t1).
Proof.
pose proof subst_tm_degree_tm_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_degree_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_degree_tm_wrt_tm_mutual :
(forall t1 tau1 a1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_degree_tm_wrt_tm :
forall t1 tau1 a1 n1,
  degree_tm_wrt_tm n1 t1 ->
  degree_tm_wrt_tm n1 (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_degree_tm_wrt_ty_mono_mutual :
(forall t1 tau1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_tm_wrt_ty_mono n1 (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_degree_tm_wrt_ty_mono :
forall t1 tau1 a1 n1,
  degree_tm_wrt_ty_mono n1 t1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  degree_tm_wrt_ty_mono n1 (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_degree_tm_wrt_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_degree_tm_wrt_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_fresh_eq_mutual :
(forall tau2 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  subst_ty_mono_ty_mono tau1 a1 tau2 = tau2).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_fresh_eq :
forall tau2 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  subst_ty_mono_ty_mono tau1 a1 tau2 = tau2.
Proof.
pose proof subst_ty_mono_ty_mono_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_fresh_eq : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_mono_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_fresh_eq_mutual :
(forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  subst_ty_mono_ty_rho tau1 a1 rho1 = rho1).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_fresh_eq :
forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  subst_ty_mono_ty_rho tau1 a1 rho1 = rho1.
Proof.
pose proof subst_ty_mono_ty_rho_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_fresh_eq : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_rho_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_fresh_eq_mutual :
(forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  subst_ty_mono_ty_poly tau1 a1 sig1 = sig1).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_fresh_eq :
forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  subst_ty_mono_ty_poly tau1 a1 sig1 = sig1.
Proof.
pose proof subst_ty_mono_ty_poly_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_fresh_eq : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_poly_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_fresh_eq_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  subst_tm t1 x1 t2 = t2).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh_eq :
forall t2 t1 x1,
  x1 `notin` fv_tm t2 ->
  subst_tm t1 x1 t2 = t2.
Proof.
pose proof subst_tm_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_fresh_eq_mutual :
(forall t1 tau1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  subst_ty_mono_tm tau1 a1 t1 = t1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_fresh_eq :
forall t1 tau1 a1,
  a1 `notin` ftv_mono_tm t1 ->
  subst_ty_mono_tm tau1 a1 t1 = t1.
Proof.
pose proof subst_ty_mono_tm_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_ty_mono_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_fresh_same_mutual :
(forall tau2 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau1 a1 tau2)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_fresh_same :
forall tau2 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
pose proof subst_ty_mono_ty_mono_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_fresh_same_mutual :
(forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_fresh_same :
forall rho1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_fresh_same_mutual :
(forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_fresh_same :
forall sig1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_fresh_same : lngen.

(* begin hide *)

Lemma subst_tm_fresh_same_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x1 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh_same :
forall t2 t1 x1,
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x1 t2).
Proof.
pose proof subst_tm_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_fresh_same_mutual :
(forall t1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_fresh_same :
forall t1 tau1 a1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_fresh_mutual :
(forall tau2 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau1 a2 tau2)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_fresh :
forall tau2 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_mono tau2 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_mono (subst_ty_mono_ty_mono tau1 a2 tau2).
Proof.
pose proof subst_ty_mono_ty_mono_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_fresh : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_fresh_mutual :
(forall rho1 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a2 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_fresh :
forall rho1 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_rho (subst_ty_mono_ty_rho tau1 a2 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_fresh : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_fresh_mutual :
(forall sig1 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a2 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_fresh :
forall sig1 tau1 a1 a2,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_ty_poly (subst_ty_mono_ty_poly tau1 a2 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_fresh : lngen.

(* begin hide *)

Lemma subst_tm_fresh_mutual :
(forall t2 t1 x1 x2,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x2 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh :
forall t2 t1 x1 x2,
  x1 `notin` fv_tm t2 ->
  x1 `notin` fv_tm t1 ->
  x1 `notin` fv_tm (subst_tm t1 x2 t2).
Proof.
pose proof subst_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_fresh_mutual :
(forall t1 tau1 a1 a2,
  a1 `notin` ftv_mono_tm t1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a2 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_fresh :
forall t1 tau1 a1 a2,
  a1 `notin` ftv_mono_tm t1 ->
  a1 `notin` ftv_mono_ty_mono tau1 ->
  a1 `notin` ftv_mono_tm (subst_ty_mono_tm tau1 a2 t1).
Proof.
pose proof subst_ty_mono_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_fresh : lngen.

Lemma subst_ty_mono_ty_mono_lc_ty_mono :
forall tau1 tau2 a1,
  lc_ty_mono tau1 ->
  lc_ty_mono tau2 ->
  lc_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_lc_ty_mono : lngen.

Lemma subst_ty_mono_ty_rho_lc_ty_rho :
forall rho1 tau1 a1,
  lc_ty_rho rho1 ->
  lc_ty_mono tau1 ->
  lc_ty_rho (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_lc_ty_rho : lngen.

Lemma subst_ty_mono_ty_poly_lc_ty_poly :
forall sig1 tau1 a1,
  lc_ty_poly sig1 ->
  lc_ty_mono tau1 ->
  lc_ty_poly (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_lc_ty_poly : lngen.

Lemma subst_tm_lc_tm :
forall t1 t2 x1,
  lc_tm t1 ->
  lc_tm t2 ->
  lc_tm (subst_tm t2 x1 t1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_lc_tm : lngen.

Lemma subst_ty_mono_tm_lc_tm :
forall t1 tau1 a1,
  lc_tm t1 ->
  lc_ty_mono tau1 ->
  lc_tm (subst_ty_mono_tm tau1 a1 t1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_lc_tm : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau3 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau3) = open_ty_mono_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_mono tau1 a1 tau3)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec :
forall tau3 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono_rec n1 tau2 tau3) = open_ty_mono_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_mono tau1 a1 tau3).
Proof.
pose proof subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 tau2 rho1) = open_ty_rho_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec :
forall rho1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 tau2 rho1) = open_ty_rho_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 tau2 sig1) = open_ty_poly_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec :
forall sig1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 tau2 sig1) = open_ty_poly_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm_rec n1 t2 t3) = open_tm_wrt_tm_rec n1 (subst_tm t1 x1 t2) (subst_tm t1 x1 t3)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec :
forall t3 t1 t2 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm_rec n1 t2 t3) = open_tm_wrt_tm_rec n1 (subst_tm t1 x1 t2) (subst_tm t1 x1 t3).
Proof.
pose proof subst_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_ty_mono_rec_mutual :
(forall t2 t1 tau1 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_ty_mono_rec n1 tau1 t2) = open_tm_wrt_ty_mono_rec n1 tau1 (subst_tm t1 x1 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_ty_mono_rec :
forall t2 t1 tau1 x1 n1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_ty_mono_rec n1 tau1 t2) = open_tm_wrt_ty_mono_rec n1 tau1 (subst_tm t1 x1 t2).
Proof.
pose proof subst_tm_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_open_tm_wrt_tm_rec_mutual :
(forall t2 tau1 t1 a1 n1,
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm_rec n1 t1 t2) = open_tm_wrt_tm_rec n1 (subst_ty_mono_tm tau1 a1 t1) (subst_ty_mono_tm tau1 a1 t2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_open_tm_wrt_tm_rec :
forall t2 tau1 t1 a1 n1,
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm_rec n1 t1 t2) = open_tm_wrt_tm_rec n1 (subst_ty_mono_tm tau1 a1 t1) (subst_ty_mono_tm tau1 a1 t2).
Proof.
pose proof subst_ty_mono_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 tau2 t1) = open_tm_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_open_tm_wrt_ty_mono_rec :
forall t1 tau1 tau2 a1 n1,
  lc_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 tau2 t1) = open_tm_wrt_ty_mono_rec n1 (subst_ty_mono_ty_mono tau1 a1 tau2) (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

Lemma subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono :
forall tau3 tau1 tau2 a1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono tau3 tau2) = open_ty_mono_wrt_ty_mono (subst_ty_mono_ty_mono tau1 a1 tau3) (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono :
forall rho1 tau1 tau2 a1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono rho1 tau2) = open_ty_rho_wrt_ty_mono (subst_ty_mono_ty_rho tau1 a1 rho1) (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono :
forall sig1 tau1 tau2 a1,
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono sig1 tau2) = open_ty_poly_wrt_ty_mono (subst_ty_mono_ty_poly tau1 a1 sig1) (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono : lngen.

Lemma subst_tm_open_tm_wrt_tm :
forall t3 t1 t2 x1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm t3 t2) = open_tm_wrt_tm (subst_tm t1 x1 t3) (subst_tm t1 x1 t2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_open_tm_wrt_ty_mono :
forall t2 t1 tau1 x1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_ty_mono t2 tau1) = open_tm_wrt_ty_mono (subst_tm t1 x1 t2) tau1.
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_ty_mono : lngen.

Lemma subst_ty_mono_tm_open_tm_wrt_tm :
forall t2 tau1 t1 a1,
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t2 t1) = open_tm_wrt_tm (subst_ty_mono_tm tau1 a1 t2) (subst_ty_mono_tm tau1 a1 t1).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_tm : lngen.

Lemma subst_ty_mono_tm_open_tm_wrt_ty_mono :
forall t1 tau1 tau2 a1,
  lc_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono t1 tau2) = open_tm_wrt_ty_mono (subst_ty_mono_tm tau1 a1 t1) (subst_ty_mono_ty_mono tau1 a1 tau2).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_var :
forall tau2 tau1 a1 a2,
  a1 <> a2 ->
  lc_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono (subst_ty_mono_ty_mono tau1 a1 tau2) (ty_mono_var_f a2) = subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono tau2 (ty_mono_var_f a2)).
Proof.
intros; rewrite subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_open_ty_mono_wrt_ty_mono_var : lngen.

Lemma subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_var :
forall rho1 tau1 a1 a2,
  a1 <> a2 ->
  lc_ty_mono tau1 ->
  open_ty_rho_wrt_ty_mono (subst_ty_mono_ty_rho tau1 a1 rho1) (ty_mono_var_f a2) = subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a2)).
Proof.
intros; rewrite subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_open_ty_rho_wrt_ty_mono_var : lngen.

Lemma subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_var :
forall sig1 tau1 a1 a2,
  a1 <> a2 ->
  lc_ty_mono tau1 ->
  open_ty_poly_wrt_ty_mono (subst_ty_mono_ty_poly tau1 a1 sig1) (ty_mono_var_f a2) = subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a2)).
Proof.
intros; rewrite subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono_var : lngen.

Lemma subst_tm_open_tm_wrt_tm_var :
forall t2 t1 x1 x2,
  x1 <> x2 ->
  lc_tm t1 ->
  open_tm_wrt_tm (subst_tm t1 x1 t2) (exp_var_f x2) = subst_tm t1 x1 (open_tm_wrt_tm t2 (exp_var_f x2)).
Proof.
intros; rewrite subst_tm_open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_var : lngen.

Lemma subst_tm_open_tm_wrt_ty_mono_var :
forall t2 t1 x1 a1,
  lc_tm t1 ->
  open_tm_wrt_ty_mono (subst_tm t1 x1 t2) (ty_mono_var_f a1) = subst_tm t1 x1 (open_tm_wrt_ty_mono t2 (ty_mono_var_f a1)).
Proof.
intros; rewrite subst_tm_open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_ty_mono_var : lngen.

Lemma subst_ty_mono_tm_open_tm_wrt_tm_var :
forall t1 tau1 a1 x1,
  open_tm_wrt_tm (subst_ty_mono_tm tau1 a1 t1) (exp_var_f x1) = subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t1 (exp_var_f x1)).
Proof.
intros; rewrite subst_ty_mono_tm_open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_tm_var : lngen.

Lemma subst_ty_mono_tm_open_tm_wrt_ty_mono_var :
forall t1 tau1 a1 a2,
  a1 <> a2 ->
  lc_ty_mono tau1 ->
  open_tm_wrt_ty_mono (subst_ty_mono_tm tau1 a1 t1) (ty_mono_var_f a2) = subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono t1 (ty_mono_var_f a2)).
Proof.
intros; rewrite subst_ty_mono_tm_open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_open_tm_wrt_ty_mono_var : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_spec_rec_mutual :
(forall tau1 tau2 a1 n1,
  subst_ty_mono_ty_mono tau2 a1 tau1 = open_ty_mono_wrt_ty_mono_rec n1 tau2 (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_mono_spec_rec :
forall tau1 tau2 a1 n1,
  subst_ty_mono_ty_mono tau2 a1 tau1 = open_ty_mono_wrt_ty_mono_rec n1 tau2 (close_ty_mono_wrt_ty_mono_rec n1 a1 tau1).
Proof.
pose proof subst_ty_mono_ty_mono_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_spec_rec_mutual :
(forall rho1 tau1 a1 n1,
  subst_ty_mono_ty_rho tau1 a1 rho1 = open_ty_rho_wrt_ty_mono_rec n1 tau1 (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_spec_rec :
forall rho1 tau1 a1 n1,
  subst_ty_mono_ty_rho tau1 a1 rho1 = open_ty_rho_wrt_ty_mono_rec n1 tau1 (close_ty_rho_wrt_ty_mono_rec n1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_spec_rec_mutual :
(forall sig1 tau1 a1 n1,
  subst_ty_mono_ty_poly tau1 a1 sig1 = open_ty_poly_wrt_ty_mono_rec n1 tau1 (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_spec_rec :
forall sig1 tau1 a1 n1,
  subst_ty_mono_ty_poly tau1 a1 sig1 = open_ty_poly_wrt_ty_mono_rec n1 tau1 (close_ty_poly_wrt_ty_mono_rec n1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_spec_rec_mutual :
(forall t1 t2 x1 n1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm_rec n1 t2 (close_tm_wrt_tm_rec n1 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_spec_rec :
forall t1 t2 x1 n1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm_rec n1 t2 (close_tm_wrt_tm_rec n1 x1 t1).
Proof.
pose proof subst_tm_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_spec_rec_mutual :
(forall t1 tau1 a1 n1,
  subst_ty_mono_tm tau1 a1 t1 = open_tm_wrt_ty_mono_rec n1 tau1 (close_tm_wrt_ty_mono_rec n1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_spec_rec :
forall t1 tau1 a1 n1,
  subst_ty_mono_tm tau1 a1 t1 = open_tm_wrt_ty_mono_rec n1 tau1 (close_tm_wrt_ty_mono_rec n1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_spec_rec : lngen.

(* end hide *)

Lemma subst_ty_mono_ty_mono_spec :
forall tau1 tau2 a1,
  subst_ty_mono_ty_mono tau2 a1 tau1 = open_ty_mono_wrt_ty_mono (close_ty_mono_wrt_ty_mono a1 tau1) tau2.
Proof.
unfold close_ty_mono_wrt_ty_mono; unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_spec : lngen.

Lemma subst_ty_mono_ty_rho_spec :
forall rho1 tau1 a1,
  subst_ty_mono_ty_rho tau1 a1 rho1 = open_ty_rho_wrt_ty_mono (close_ty_rho_wrt_ty_mono a1 rho1) tau1.
Proof.
unfold close_ty_rho_wrt_ty_mono; unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_spec : lngen.

Lemma subst_ty_mono_ty_poly_spec :
forall sig1 tau1 a1,
  subst_ty_mono_ty_poly tau1 a1 sig1 = open_ty_poly_wrt_ty_mono (close_ty_poly_wrt_ty_mono a1 sig1) tau1.
Proof.
unfold close_ty_poly_wrt_ty_mono; unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_spec : lngen.

Lemma subst_tm_spec :
forall t1 t2 x1,
  subst_tm t2 x1 t1 = open_tm_wrt_tm (close_tm_wrt_tm x1 t1) t2.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_spec : lngen.

Lemma subst_ty_mono_tm_spec :
forall t1 tau1 a1,
  subst_ty_mono_tm tau1 a1 t1 = open_tm_wrt_ty_mono (close_tm_wrt_ty_mono a1 t1) tau1.
Proof.
unfold close_tm_wrt_ty_mono; unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_spec : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_subst_ty_mono_ty_mono_mutual :
(forall tau1 tau2 tau3 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 <> a1 ->
  subst_ty_mono_ty_mono tau2 a1 (subst_ty_mono_ty_mono tau3 a2 tau1) = subst_ty_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau3) a2 (subst_ty_mono_ty_mono tau2 a1 tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_subst_ty_mono_ty_mono :
forall tau1 tau2 tau3 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 <> a1 ->
  subst_ty_mono_ty_mono tau2 a1 (subst_ty_mono_ty_mono tau3 a2 tau1) = subst_ty_mono_ty_mono (subst_ty_mono_ty_mono tau2 a1 tau3) a2 (subst_ty_mono_ty_mono tau2 a1 tau1).
Proof.
pose proof subst_ty_mono_ty_mono_subst_ty_mono_ty_mono_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_subst_ty_mono_ty_mono : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_subst_ty_mono_ty_rho_mutual :
(forall rho1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_ty_rho tau1 a1 (subst_ty_mono_ty_rho tau2 a2 rho1) = subst_ty_mono_ty_rho (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_ty_rho tau1 a1 rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_subst_ty_mono_ty_rho :
forall rho1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_ty_rho tau1 a1 (subst_ty_mono_ty_rho tau2 a2 rho1) = subst_ty_mono_ty_rho (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_ty_rho tau1 a1 rho1).
Proof.
pose proof subst_ty_mono_ty_rho_subst_ty_mono_ty_rho_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_subst_ty_mono_ty_rho : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_subst_ty_mono_ty_poly_mutual :
(forall sig1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_ty_poly tau1 a1 (subst_ty_mono_ty_poly tau2 a2 sig1) = subst_ty_mono_ty_poly (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_ty_poly tau1 a1 sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_subst_ty_mono_ty_poly :
forall sig1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_ty_poly tau1 a1 (subst_ty_mono_ty_poly tau2 a2 sig1) = subst_ty_mono_ty_poly (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_ty_poly tau1 a1 sig1).
Proof.
pose proof subst_ty_mono_ty_poly_subst_ty_mono_ty_poly_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_subst_ty_mono_ty_poly : lngen.

(* begin hide *)

Lemma subst_tm_subst_tm_mutual :
(forall t1 t2 t3 x2 x1,
  x2 `notin` fv_tm t2 ->
  x2 <> x1 ->
  subst_tm t2 x1 (subst_tm t3 x2 t1) = subst_tm (subst_tm t2 x1 t3) x2 (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_subst_tm :
forall t1 t2 t3 x2 x1,
  x2 `notin` fv_tm t2 ->
  x2 <> x1 ->
  subst_tm t2 x1 (subst_tm t3 x2 t1) = subst_tm (subst_tm t2 x1 t3) x2 (subst_tm t2 x1 t1).
Proof.
pose proof subst_tm_subst_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_subst_tm : lngen.

(* begin hide *)

Lemma subst_tm_subst_ty_mono_tm_mutual :
(forall t1 t2 tau1 a1 x1,
  a1 `notin` ftv_mono_tm t2 ->
  subst_tm t2 x1 (subst_ty_mono_tm tau1 a1 t1) = subst_ty_mono_tm tau1 a1 (subst_tm t2 x1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_subst_ty_mono_tm :
forall t1 t2 tau1 a1 x1,
  a1 `notin` ftv_mono_tm t2 ->
  subst_tm t2 x1 (subst_ty_mono_tm tau1 a1 t1) = subst_ty_mono_tm tau1 a1 (subst_tm t2 x1 t1).
Proof.
pose proof subst_tm_subst_ty_mono_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_subst_ty_mono_tm : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_subst_tm_mutual :
(forall t1 tau1 t2 x1 a1,
  subst_ty_mono_tm tau1 a1 (subst_tm t2 x1 t1) = subst_tm (subst_ty_mono_tm tau1 a1 t2) x1 (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_subst_tm :
forall t1 tau1 t2 x1 a1,
  subst_ty_mono_tm tau1 a1 (subst_tm t2 x1 t1) = subst_tm (subst_ty_mono_tm tau1 a1 t2) x1 (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_subst_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_subst_tm : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_subst_ty_mono_tm_mutual :
(forall t1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_tm tau1 a1 (subst_ty_mono_tm tau2 a2 t1) = subst_ty_mono_tm (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_tm tau1 a1 t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_subst_ty_mono_tm :
forall t1 tau1 tau2 a2 a1,
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  subst_ty_mono_tm tau1 a1 (subst_ty_mono_tm tau2 a2 t1) = subst_ty_mono_tm (subst_ty_mono_ty_mono tau1 a1 tau2) a2 (subst_ty_mono_tm tau1 a1 t1).
Proof.
pose proof subst_ty_mono_tm_subst_ty_mono_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_subst_ty_mono_tm : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec_mutual :
(forall tau2 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_mono tau1 a1 tau2 = close_ty_mono_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a2) tau2))).
Proof.
apply_mutual_ind ty_mono_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec :
forall tau2 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_mono tau1 a1 tau2 = close_ty_mono_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a2) tau2)).
Proof.
pose proof subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_rec_open_ty_mono_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec_mutual :
(forall rho1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_rho rho1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_rho tau1 a1 rho1 = close_ty_rho_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a2) rho1))).
Proof.
apply_mutual_ind ty_rho_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec :
forall rho1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_rho rho1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_rho tau1 a1 rho1 = close_ty_rho_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a2) rho1)).
Proof.
pose proof subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_rec_open_ty_rho_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec_mutual :
(forall sig1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_poly sig1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_poly tau1 a1 sig1 = close_ty_poly_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a2) sig1))).
Proof.
apply_mutual_ind ty_poly_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec :
forall sig1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_ty_poly sig1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_ty_poly tau1 a1 sig1 = close_ty_poly_wrt_ty_mono_rec n1 a2 (subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a2) sig1)).
Proof.
pose proof subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_rec_open_ty_poly_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall t2 t1 x1 x2 n1,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x2) t2))).
Proof.
apply_mutual_ind tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall t2 t1 x1 x2 n1,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm_rec n1 x2 (subst_tm t1 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x2) t2)).
Proof.
pose proof subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual :
(forall t2 t1 x1 a1 n1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  degree_tm_wrt_ty_mono n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_ty_mono_rec n1 a1 (subst_tm t1 x1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t2))).
Proof.
apply_mutual_ind tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec :
forall t2 t1 x1 a1 n1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  degree_tm_wrt_ty_mono n1 t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_ty_mono_rec n1 a1 (subst_tm t1 x1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t2)).
Proof.
pose proof subst_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall t1 tau1 a1 x1 n1,
  x1 `notin` fv_tm t1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_tm_rec n1 x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1))).
Proof.
apply_mutual_ind tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall t1 tau1 a1 x1 n1,
  x1 `notin` fv_tm t1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_tm_rec n1 x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1)).
Proof.
pose proof subst_ty_mono_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual :
(forall t1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_tm t1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_ty_mono_rec n1 a2 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a2) t1))).
Proof.
apply_mutual_ind tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec :
forall t1 tau1 a1 a2 n1,
  a2 `notin` ftv_mono_tm t1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  degree_ty_mono_wrt_ty_mono n1 tau1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_ty_mono_rec n1 a2 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a2) t1)).
Proof.
pose proof subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_ty_mono_rec_open_tm_wrt_ty_mono_rec : lngen.

(* end hide *)

Lemma subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono :
forall tau2 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_mono tau2 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_mono tau1 a1 tau2 = close_ty_mono_wrt_ty_mono a2 (subst_ty_mono_ty_mono tau1 a1 (open_ty_mono_wrt_ty_mono tau2 (ty_mono_var_f a2))).
Proof.
unfold close_ty_mono_wrt_ty_mono; unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_close_ty_mono_wrt_ty_mono_open_ty_mono_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono :
forall rho1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_rho rho1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_rho tau1 a1 rho1 = close_ty_rho_wrt_ty_mono a2 (subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a2))).
Proof.
unfold close_ty_rho_wrt_ty_mono; unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_close_ty_rho_wrt_ty_mono_open_ty_rho_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono :
forall sig1 tau1 a1 a2,
  a2 `notin` ftv_mono_ty_poly sig1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  lc_ty_mono tau1 ->
  subst_ty_mono_ty_poly tau1 a1 sig1 = close_ty_poly_wrt_ty_mono a2 (subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a2))).
Proof.
unfold close_ty_poly_wrt_ty_mono; unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_close_ty_poly_wrt_ty_mono_open_ty_poly_wrt_ty_mono : lngen.

Lemma subst_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall t2 t1 x1 x2,
  x2 `notin` fv_tm t2 ->
  x2 `notin` fv_tm t1 ->
  x2 <> x1 ->
  lc_tm t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (exp_var_f x2))).
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_close_tm_wrt_ty_mono_open_tm_wrt_ty_mono :
forall t2 t1 x1 a1,
  a1 `notin` ftv_mono_tm t2 ->
  a1 `notin` ftv_mono_tm t1 ->
  lc_tm t1 ->
  subst_tm t1 x1 t2 = close_tm_wrt_ty_mono a1 (subst_tm t1 x1 (open_tm_wrt_ty_mono t2 (ty_mono_var_f a1))).
Proof.
unfold close_tm_wrt_ty_mono; unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_ty_mono_open_tm_wrt_ty_mono : lngen.

Lemma subst_ty_mono_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall t1 tau1 a1 x1,
  x1 `notin` fv_tm t1 ->
  lc_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_tm x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t1 (exp_var_f x1))).
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_ty_mono_tm_close_tm_wrt_ty_mono_open_tm_wrt_ty_mono :
forall t1 tau1 a1 a2,
  a2 `notin` ftv_mono_tm t1 ->
  a2 `notin` ftv_mono_ty_mono tau1 ->
  a2 <> a1 ->
  lc_ty_mono tau1 ->
  subst_ty_mono_tm tau1 a1 t1 = close_tm_wrt_ty_mono a2 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono t1 (ty_mono_var_f a2))).
Proof.
unfold close_tm_wrt_ty_mono; unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_close_tm_wrt_ty_mono_open_tm_wrt_ty_mono : lngen.

Lemma subst_ty_mono_ty_poly_ty_poly_poly_gen :
forall a2 sig1 tau1 a1,
  lc_ty_mono tau1 ->
  a2 `notin` ftv_mono_ty_mono tau1 `union` ftv_mono_ty_poly sig1 `union` singleton a1 ->
  subst_ty_mono_ty_poly tau1 a1 (ty_poly_poly_gen sig1) = ty_poly_poly_gen (close_ty_poly_wrt_ty_mono a2 (subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_ty_poly_poly_gen : lngen.

Lemma subst_tm_exp_abs :
forall x2 t2 t1 x1,
  lc_tm t1 ->
  x2 `notin` fv_tm t1 `union` fv_tm t2 `union` singleton x1 ->
  subst_tm t1 x1 (exp_abs t2) = exp_abs (close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_exp_abs : lngen.

Lemma subst_tm_exp_typed_abs :
forall x2 sig1 t2 t1 x1,
  lc_tm t1 ->
  x2 `notin` fv_tm t1 `union` fv_tm t2 `union` singleton x1 ->
  subst_tm t1 x1 (exp_typed_abs sig1 t2) = exp_typed_abs (sig1) (close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_exp_typed_abs : lngen.

Lemma subst_tm_exp_let :
forall x2 u1 t2 t1 x1,
  lc_tm t1 ->
  x2 `notin` fv_tm t1 `union` fv_tm t2 `union` singleton x1 ->
  subst_tm t1 x1 (exp_let u1 t2) = exp_let (subst_tm t1 x1 u1) (close_tm_wrt_tm x2 (subst_tm t1 x1 (open_tm_wrt_tm t2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_exp_let : lngen.

Lemma subst_ty_mono_tm_exp_abs :
forall x1 t1 tau1 a1,
  lc_ty_mono tau1 ->
  x1 `notin` fv_tm t1 ->
  subst_ty_mono_tm tau1 a1 (exp_abs t1) = exp_abs (close_tm_wrt_tm x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_exp_abs : lngen.

Lemma subst_ty_mono_tm_exp_typed_abs :
forall x1 sig1 t1 tau1 a1,
  lc_ty_mono tau1 ->
  x1 `notin` fv_tm t1 ->
  subst_ty_mono_tm tau1 a1 (exp_typed_abs sig1 t1) = exp_typed_abs (subst_ty_mono_ty_poly tau1 a1 sig1) (close_tm_wrt_tm x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_exp_typed_abs : lngen.

Lemma subst_ty_mono_tm_exp_let :
forall x1 u1 t1 tau1 a1,
  lc_ty_mono tau1 ->
  x1 `notin` fv_tm t1 ->
  subst_ty_mono_tm tau1 a1 (exp_let u1 t1) = exp_let (subst_ty_mono_tm tau1 a1 u1) (close_tm_wrt_tm x1 (subst_ty_mono_tm tau1 a1 (open_tm_wrt_tm t1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_exp_let : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_mono_intro_rec_mutual :
(forall tau1 a1 tau2 n1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1 = subst_ty_mono_ty_mono tau2 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1)).
Proof.
apply_mutual_ind ty_mono_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_mono_intro_rec :
forall tau1 a1 tau2 n1,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono_rec n1 tau2 tau1 = subst_ty_mono_ty_mono tau2 a1 (open_ty_mono_wrt_ty_mono_rec n1 (ty_mono_var_f a1) tau1).
Proof.
pose proof subst_ty_mono_ty_mono_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_intro_rec : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_mono_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_rho_intro_rec_mutual :
(forall rho1 a1 tau1 n1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1 = subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1)).
Proof.
apply_mutual_ind ty_rho_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_rho_intro_rec :
forall rho1 a1 tau1 n1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono_rec n1 tau1 rho1 = subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono_rec n1 (ty_mono_var_f a1) rho1).
Proof.
pose proof subst_ty_mono_ty_rho_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_intro_rec : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_rho_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_ty_poly_intro_rec_mutual :
(forall sig1 a1 tau1 n1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1 = subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1)).
Proof.
apply_mutual_ind ty_poly_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_ty_poly_intro_rec :
forall sig1 a1 tau1 n1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono_rec n1 tau1 sig1 = subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono_rec n1 (ty_mono_var_f a1) sig1).
Proof.
pose proof subst_ty_mono_ty_poly_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_intro_rec : lngen.
#[export] Hint Rewrite subst_ty_mono_ty_poly_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_intro_rec_mutual :
(forall t1 x1 t2 n1,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 t2 t1 = subst_tm t2 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_intro_rec :
forall t1 x1 t2 n1,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm_rec n1 t2 t1 = subst_tm t2 x1 (open_tm_wrt_tm_rec n1 (exp_var_f x1) t1).
Proof.
pose proof subst_tm_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_intro_rec : lngen.
#[export] Hint Rewrite subst_tm_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_mono_tm_intro_rec_mutual :
(forall t1 a1 tau1 n1,
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono_rec n1 tau1 t1 = subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_mono_tm_intro_rec :
forall t1 a1 tau1 n1,
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono_rec n1 tau1 t1 = subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono_rec n1 (ty_mono_var_f a1) t1).
Proof.
pose proof subst_ty_mono_tm_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_intro_rec : lngen.
#[export] Hint Rewrite subst_ty_mono_tm_intro_rec using solve [auto] : lngen.

Lemma subst_ty_mono_ty_mono_intro :
forall a1 tau1 tau2,
  a1 `notin` ftv_mono_ty_mono tau1 ->
  open_ty_mono_wrt_ty_mono tau1 tau2 = subst_ty_mono_ty_mono tau2 a1 (open_ty_mono_wrt_ty_mono tau1 (ty_mono_var_f a1)).
Proof.
unfold open_ty_mono_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_mono_intro : lngen.

Lemma subst_ty_mono_ty_rho_intro :
forall a1 rho1 tau1,
  a1 `notin` ftv_mono_ty_rho rho1 ->
  open_ty_rho_wrt_ty_mono rho1 tau1 = subst_ty_mono_ty_rho tau1 a1 (open_ty_rho_wrt_ty_mono rho1 (ty_mono_var_f a1)).
Proof.
unfold open_ty_rho_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_rho_intro : lngen.

Lemma subst_ty_mono_ty_poly_intro :
forall a1 sig1 tau1,
  a1 `notin` ftv_mono_ty_poly sig1 ->
  open_ty_poly_wrt_ty_mono sig1 tau1 = subst_ty_mono_ty_poly tau1 a1 (open_ty_poly_wrt_ty_mono sig1 (ty_mono_var_f a1)).
Proof.
unfold open_ty_poly_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_ty_poly_intro : lngen.

Lemma subst_tm_intro :
forall x1 t1 t2,
  x1 `notin` fv_tm t1 ->
  open_tm_wrt_tm t1 t2 = subst_tm t2 x1 (open_tm_wrt_tm t1 (exp_var_f x1)).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_intro : lngen.

Lemma subst_ty_mono_tm_intro :
forall a1 t1 tau1,
  a1 `notin` ftv_mono_tm t1 ->
  open_tm_wrt_ty_mono t1 tau1 = subst_ty_mono_tm tau1 a1 (open_tm_wrt_ty_mono t1 (ty_mono_var_f a1)).
Proof.
unfold open_tm_wrt_ty_mono; default_simp.
Qed.

#[export] Hint Resolve subst_ty_mono_tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
