Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.MetatheoryAtom.
Require Export Metalib.LibLNgen.

From Exp Require Export Exp_ott.
From Exp Require Export Exp_inf.

(*************************************************************************)
(** Notation, manually added *)
(*************************************************************************)

Notation "Gamma '|-' t '\in' T" := (typing Gamma t T) (at level 40).

(* Empty context is represented as an empty list *)
Definition empty : list (atom * ty_poly) := nil.

(* Int datatype in the object language *)
Definition Int : ty_poly := (ty_poly_rho (ty_rho_tau ty_mono_base)).

(** Tells Coq to create a new custom grammar Exp for parsing the object language *)
(** See Imp chapter of Software Foundations for details *)
(* Coercion exp_lit : integer >-> tm. *)

Declare Custom Entry exp.
Declare Scope exp_scope.


Notation "<{ e }>" := e (at level 0, e custom exp at level 99) : exp_scope.
Notation "( x )" := x (in custom exp, x at level 99) : exp_scope.
Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom exp at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : exp_scope.
(* Notation "'exp_lit' i" := (exp_lit i) (in custom exp at level 80) : exp_scope. *)


Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
(* Notation "S -> T" := (ty_mono_func S T) (in custom exp at level 50, right associativity) : exp_scope *)
Notation "x y" := (exp_app x y) (in custom exp at level 1, left associativity) : exp_scope.
Notation "\ x : t , y" :=
  (exp_abs x t y) (in custom exp at level 90, x at level 99,
                     t custom exp at level 99,
                     y custom exp at level 99,
                     left associativity) : exp_scope.

Local Open Scope exp_scope.                     

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x => ftv_mono_ctx x) in
  let E := gather_atoms_with (fun x => ftv_mono_tm x) in
  let F := gather_atoms_with (fun x => ftv_mono_ty_mono x) in
  let G := gather_atoms_with (fun x => ftv_mono_ty_poly x) in
  let H := gather_atoms_with (fun x => ftv_mono_ty_rho x) in
  constr:(A \u B \u C \u D \u E \u F \u G).


(*************************************************************************)
(** Lemmas, manually added *)
(*************************************************************************)


(* Special thanks to Yiyun for all the guides and coq help!!! *)

Variant mono_flag :=
  | func
  | var_f
  | var_b
  | base.

Fixpoint normalize_mono (tau : ty_mono) (mf : mono_flag) : bool :=
  match tau, mf with
  | ty_mono_base, base => true
  | ty_mono_var_b _, var_b => true
  | ty_mono_var_f _, var_f => true
  | ty_mono_func _ _, func => true
  | _, _=> false
  end.

Fixpoint normalize_rho (rho : ty_rho) (mf : mono_flag) : bool :=
  match rho with
  | ty_rho_tau tau => normalize_mono tau mf
  end.

Fixpoint normalize_poly (sig : ty_poly) (mf : mono_flag) : bool :=
  match sig with
  | ty_poly_rho rho => normalize_rho rho mf
  | ty_poly_poly_gen sig' => normalize_poly sig' mf
  end.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.

Lemma normalize_open_n_var_rec : forall (sig: ty_poly) (n : nat) (a : tyvar),
    normalize_poly (open_ty_poly_wrt_ty_mono_rec n (ty_mono_var_f a) sig) func = normalize_poly (sig) func.
Proof.
  intros sig. elim : sig.
  - intros rho. elim : rho. intros tau. elim : tau; intros; simpl; try (reflexivity). destruct (lt_eq_lt_dec).
    + destruct s; auto.
    + auto.
  - intros sig IH n a. simpl. apply IH.
Qed.

Lemma is_fun_poly_open: forall sig tau n,
    normalize_poly sig func -> normalize_poly (open_ty_poly_wrt_ty_mono_rec n tau sig) func.
Proof with eauto.
  intros sig. induction sig.
  - induction rho. induction tau; intros tau' Htau'; try (inversion tau'); auto.
  - intros. simpl in H. unfold open_ty_poly_wrt_ty_mono. simpl.
    apply IHsig. auto.
Qed.
(* Qed. *)

Fixpoint bad_fun_mono (tau : ty_mono) :=
  match tau with
  | ty_mono_var_b _ => true
  | ty_mono_var_f _ => true
  | _ => false
  end.

Fixpoint bad_fun_rho (rho : ty_rho) :=
  match rho with
  | ty_rho_tau tau => bad_fun_mono tau
  end.

Fixpoint bad_fun_poly (sig : ty_poly) :=
  match sig with
  | ty_poly_rho rho => bad_fun_rho rho
  | ty_poly_poly_gen sig' => bad_fun_poly sig'
  end.

Lemma bad_fun_poly_open_var_rec : forall (sig : ty_poly) (n : nat) (a : tyvar),
    bad_fun_poly (open_ty_poly_wrt_ty_mono_rec n (ty_mono_var_f a) sig) = bad_fun_poly (sig).
Proof.
  intros sig. elim : sig.
  - intros rho. elim : rho. intros tau0. elim : tau0; intros; simpl; try (reflexivity).
    destruct lt_eq_lt_dec.
    + destruct s; reflexivity.
    + auto.
  - intros sig IH n a. apply IH.
Qed.

Lemma bad_fun_poly_open_varb_rec : forall (sig : ty_poly) (n i : nat),
    bad_fun_poly (open_ty_poly_wrt_ty_mono_rec n (ty_mono_var_b i) sig) = bad_fun_poly (sig).
Proof.
  intros sig. elim : sig.
  - intros rho. elim : rho. intros tau. elim : tau; intros; simpl; try (reflexivity).
    destruct lt_eq_lt_dec.
    + destruct s; reflexivity.
    + auto.
  - intros sig IH n a. apply IH.
Qed.

Lemma not_bad_open_func_equiv : forall (sig: ty_poly) (n : nat) (tau : ty_mono),
    not (bad_fun_poly sig) ->
    normalize_poly (open_ty_poly_wrt_ty_mono_rec n tau sig) func = normalize_poly sig func.
Proof with eauto.
  intros sig. elim sig.
  - intros rho; elim rho. intros tau; elim tau; intros; try (simpl; reflexivity).
    simpl. destruct lt_eq_lt_dec. destruct s.
    + simpl. reflexivity.
    + simpl in H. unfold not in H. destruct H. auto.
    + simpl. reflexivity.
  - intros. simpl in H0. apply H. auto.
Qed.

Lemma bad_fun_poly_open_rec : forall (sig : ty_poly) (n : nat) (tau : ty_mono),
    not (bad_fun_poly sig) ->
    not (bad_fun_poly (open_ty_poly_wrt_ty_mono_rec n tau sig)).
Proof.
  intros sig. elim sig.
  - intros rho. elim rho. intros tau. elim tau; auto.
  - intros. apply H. auto.
Qed.

Theorem wt_no_bad_poly: forall (Gamma : ctx) (e : tm) (sig : ty_poly) (Htyping: typing Gamma e sig), 
    is_value_of_tm e -> not (bad_fun_poly sig).
Proof.
  intros Gamma e sig Htyping.
  elim Htyping; intros; auto.
  - pick fresh x.
    apply notin_union_1 in Fr as Fr1. specialize (H0 x Fr1 H1). unfold open_ty_poly_wrt_ty_mono in H0. rewrite bad_fun_poly_open_var_rec in H0. auto.
  - unfold open_ty_poly_wrt_ty_mono. apply bad_fun_poly_open_rec. auto.
Qed.

Theorem canonical_forms_fun_new: forall t T,
typing empty t T
(* -> forall T1 T2, inst T (ty_rho_tau (ty_mono_func T1 T2))  *)
  -> normalize_poly T func = true 
  -> is_value_of_tm t
  -> exists u, t = exp_abs u.
Proof with eauto.
  intros t T Ht.
  dependent induction Ht; subst; try discriminate; intros.
  - inversion H2.
  - exists t. auto.
  - inversion H0.
  - inversion H2.
  - inversion H1.
  - pick fresh x. eapply H0; try auto.
    simpl in H2. unfold open_ty_poly_wrt_ty_mono. rewrite normalize_open_n_var_rec. auto.
  - apply IHHt; auto.
    unfold open_ty_poly_wrt_ty_mono in H0. erewrite not_bad_open_func_equiv in H0.
    + auto.
    + 
      eapply wt_no_bad_poly in Ht; auto.
Qed.

Lemma empty_ctx_typing_lc: forall e T,
  typing empty e T -> lc_tm e.
Proof with eauto.
  intros e T H.
  induction H; subst...
  - destruct H...
  - destruct (atom_fresh L).
    apply (H0 x)...
Qed.

#[export] Hint Resolve empty_ctx_typing_lc : core.

Lemma empty_ctx_typing_lc_ty: forall e T,
  typing empty e T -> lc_ty_poly T.
Proof with eauto.
  intros e T H.
  dependent induction H; subst...
  - destruct H0...
  - pick fresh x. apply notin_union_1 in Fr as Fr0. specialize H0 with x. apply H0 in Fr0 as H1.
    + repeat constructor.
      ++ (* specialize H with x. apply H in Fr0 as H2. destruct tau1; try constructor. *)
        (* +++ simpl in H2. inversion H2. *) admit.
      ++ inversion H1; subst. inversion H3; subst. auto.
    + simpl. admit.
  - admit.
Admitted.

#[export] Hint Resolve empty_ctx_typing_lc : core.

Lemma empty_ctx_typing_closed: forall e T,
  typing empty e T -> fv_tm e [=] {}.
Proof with eauto.
  intros e T H.
  assert (Hlc: lc_tm e)...
  induction H; subst; simpl in *; try fsetdec.
Admitted.

Theorem progress : forall e T,
  typing empty e T ->
    is_value_of_tm e \/ exists e', step e e'.
Proof with eauto.
  intros e T H. assert (H0 := H).
  remember empty as G.
  induction H0; subst;
  try (left; constructor)...
  - right; destruct IHtyping1; destruct IHtyping2...
    + assert (Hnorm: normalize_poly (ty_poly_rho (ty_rho_tau (ty_mono_func tau1 tau2))) func). auto.
      assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun_new t (ty_poly_rho (ty_rho_tau (ty_mono_func tau1 tau2))) H0 _ Hnorm H0).}
      destruct Hlam; subst...
    + assert (Hnorm: normalize_poly (ty_poly_rho (ty_rho_tau (ty_mono_func tau1 tau2))) func). auto.
      assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun_new t (ty_poly_rho (ty_rho_tau (ty_mono_func tau1 tau2))) H0_ Hnorm H0)...}
      destruct Hlam as [t1 Hlam]; subst...
      destruct H1 as [u' H1]. eexists...
    + destruct H0 as [t' H0]. eexists...
    + destruct H0 as [t' H0]. eexists...
  - right; destruct IHtyping...
    destruct H3 as [u' H3]. exists (exp_let u' t)...
  - right; destruct IHtyping...
    + destruct H0. eexists...
    + destruct H0. destruct H2 as [t' H2]. eexists...
  - destruct (atom_fresh L).
    specialize H0 with x; specialize H1 with x.
    assert (n1 := n); apply H0 in n; apply H1 in n1...
Qed.



(* Strengthened version of the weakening lemma 
 * Referenced Stlc.Lec2_sol from Metalib repo *)
Theorem typing_weakening_strengthened : forall (E F G : ctx) t T,
  typing (G ++ E) t T 
    -> uniq (G ++ F ++ E)
    -> typing (G ++ F ++ E) t T.
Proof.
  intros E F G t T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst; auto.
  - (* exp_abs *) 
    apply typ_abs with (L := dom (G0 ++ F ++ E) \u L).
    intros x Frx.
    rewrite_env (([(x, ty_poly_rho (ty_rho_tau tau1))] ++ G0) ++ F ++ E).
    apply H0.
    + auto.
    + simpl_env. reflexivity.
    + simpl_env. apply uniq_push.
      * assumption.
      * auto.
  - eauto.
  - (* exp_let *) 
    apply (typ_let (dom (G0 ++ F ++ E) \u L) _ u t rho sig).
    + auto.
    + intros x Frx.
      rewrite_env (([(x, sig)] ++ G0) ++ F ++ E).
      apply H1.
      * auto.
      * simpl_env. reflexivity.
      * simpl_env. apply uniq_push.
        -- assumption.
        -- auto.
  - eauto. Unshelve. apply L.
Qed. 
 
(** Original statement of the weakening lemma *)
Theorem typing_weakening : forall (E F : ctx) t T,
  typing E t T -> 
  uniq (F ++ E) ->
  typing (F ++ E) t T.
Proof.
  intros E F t T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.

(** Substitution for variables: same variable *)
Lemma subst_eq_var : forall (x : var) u,
  subst_tm u x (exp_var_f x) = u.
Proof.
  intros x u.
  simpl.
  destruct eq_dec.
  - reflexivity.
  - destruct n. reflexivity.
Qed.

(** Substitution for variables: different variable *)
Lemma subst_neq_var : forall (x y : var) u,
  y <> x ->
  subst_tm u x (exp_var_f y) = exp_var_f y.
Proof.
  intros x y u.
  simpl.
  intro Hneq.
  destruct eq_dec.
  - destruct Hneq. assumption.
  - reflexivity.
Qed.

(** Substituting the same variable in an expression doesn't make a difference *)
Lemma subst_same : forall y e,
  subst_tm (exp_var_f y) y e = e.
Proof.
  induction e; simpl; intros; eauto.
  - (* exp_var_f *) destruct (x == y); subst; eauto.
  - (* exp_abs *) rewrite IHe. auto.
  - (* exp_app *) 
    rewrite IHe1. 
    rewrite IHe2. 
    reflexivity.
  - (* exp_typed_abs *)
    rewrite IHe. reflexivity.
  - (* exp_let *) 
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - (* exp_type_anno *)    
    rewrite IHe. reflexivity.
Qed. 


(** If a variable doesn't appear free in a term, 
    substituting for it has no effect. *)
Lemma subst_tm_fresh_eq : forall (x : var) e u,
  x `notin` fv_tm e ->
  subst_tm u x e = e.
Proof.
  intros x e u H.
  induction e; eauto; 
    try (simpl in *; f_equal; eauto).
  - (* exp_var_f *)
    unfold subst_tm.
    destruct (x0 == x).
    + (* x0 = x *) 
      subst. simpl fv_tm in H. fsetdec.
    + (* x0 <> x *)  
      reflexivity.
Qed.

(** Free variables are not introduced by substitution. *)
Lemma fv_tm_subst_tm_notin : forall x y u e,
  x `notin` fv_tm e ->
  x `notin` fv_tm u ->
  x `notin` fv_tm (subst_tm u y e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *; 
    try assumption.
  - (* exp_var_f *)
    destruct (x0 == y).
    + (* x0 = y *) assumption.
    + (* x0 <> y *) simpl. assumption.
  - (* exp_abs *) apply IHe. assumption.
  - (* exp_app *)
    destruct_notin.
    apply notin_union.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - (* exp_typed_abs *) apply IHe. assumption.
  - (* exp_let *) 
    destruct_notin.
    apply notin_union.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - (* exp_type_anno *) 
    apply IHe. assumption.
Qed.

(* If [x] is a fresh variable, [x] continues to be fresh we substitute all occurrences of [x] in [e] with [u]. *)
Lemma subst_tm_fresh_same : forall u e x,
  x `notin` fv_tm e ->
  x `notin` fv_tm (subst_tm u x e).
Proof.
  intros.
  induction e; simpl in *; auto.
  - (* exp_var_f *) 
    destruct (x0 == x).
    + (* x0 = x *) subst. fsetdec.
    + (* x0 <> x *) simpl. assumption.
Qed.

(* If [x] is a fresh variable, 
   the free variables of [e] after substituting 
   all occurrences of [x] in [e] with [u] are the 
   same as the free variables of [e] pre-substitution. *)
Lemma fv_tm_subst_tm_fresh : forall u e x,
  x `notin` fv_tm e ->
  fv_tm (subst_tm u x e) [=] fv_tm e.
Proof.
  intros.
  induction e; simpl in *; auto; try fsetdec.
  - (* exp_var_f *) 
    destruct (x0 == x).
    + (* x0 = x *) subst. fsetdec.
    + (* x0 <> x *) simpl. fsetdec.
  - (* exp_abs *) 
    rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    destruct_notin. 
    assumption.
    destruct_notin.
    apply H.
  - (* exp_typed_abs *) 
    rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    destruct_notin. 
    assumption.
    destruct_notin.
    apply H.
Qed.


(** We can commute free & bound variable substitution. 
    Note: the name of this lemma was automatically generated by LNgen -- see [Exp_inf.v]. 
    
    This lemma is most often used with [t2] as some fresh variable. *)
Lemma subst_tm_open_tm_wrt_tm :
forall t3 t1 t2 x1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm t3 t2) = open_tm_wrt_tm (subst_tm t1 x1 t3) (subst_tm t1 x1 t2).
Proof.
   unfold open_tm_wrt_tm;
     default_simp.
   
   Admitted. (* TODO: not sure how to proceed *) 

(** Corollary of the above lemma for fresh variables. *)  
Lemma subst_var : forall (x y : var) u e,
  y <> x ->
  lc_tm u ->
  open_tm_wrt_tm (subst_tm u x e) (exp_var_f y) = 
    subst_tm u x (open_tm_wrt_tm e (exp_var_f y)).
Proof.
  intros x y u e Hneq Hlc.
  rewrite subst_tm_open_tm_wrt_tm; auto.
  rewrite subst_neq_var; auto.
Qed.

(* Opening can be replaced with variable opening & substitution *)
Lemma subst_tm_intro : forall (x : tmvar) u e,
  x `notin` (fv_tm e) ->
  open_tm_wrt_tm e u = subst_tm u x (open_tm_wrt_tm e (exp_var_f x)).
Proof.
  intros x u e FV_TM.
  unfold open_tm_wrt_tm.
  generalize 0.
  induction e; intro n0; simpl; eauto.
  - (* var_b *)
    destruct (lt_eq_lt_dec n n0).
    + destruct s. 
      * simpl. auto.
      * rewrite subst_eq_var. auto.
    + simpl. auto.
  - (* var_f *)
    destruct (x0 == x). subst.
    simpl in FV_TM. 
    fsetdec. auto.
  - (* abs *)
    f_equal.
    simpl in FV_TM.
    apply IHe.
    assumption.
  - (* app *)
    simpl in FV_TM.
    f_equal.
    + apply IHe1. auto.
    + apply IHe2. auto.
  - (* typed_abs *)    
    f_equal.
    simpl in FV_TM.
    apply IHe. 
    assumption.
  - (* let *)
    f_equal.
    simpl in FV_TM.
    + apply IHe1. fsetdec.
    + apply IHe2. simpl in FV_TM. fsetdec.
  - (* type_anno *)   
    f_equal.
    simpl in FV_TM.
    apply IHe.
    assumption.
Qed. 
    

(** Variable case of the substitution lemma *)
Lemma typing_subst_var_case : forall (E F : ctx) u S T (z x : atom),
  binds x T (F ++ [(z, S)] ++ E) ->
  uniq (F ++ [(z, S)] ++ E) -> 
  typing E u S ->
  typing (F ++ E) (subst_tm u z (exp_var_f x)) T.
Proof.
  intros E F u S T z x Hbinds Huniq Htyp.
  simpl.
  destruct eq_dec.
  - subst. assert (T = S).
    + (* T = S *)
      eapply binds_mid_eq.
      apply Hbinds.
      apply Huniq.
    + subst.
      apply typing_weakening.
      ++ assumption.
      ++ eapply uniq_remove_mid. apply Huniq.
      Admitted.
  (* - apply typ_var.
    + eapply uniq_remove_mid. apply Huniq.
    + eapply binds_remove_mid.
      ++ apply Hbinds.
      ++ assumption.
Qed. *)

(* Well-typed terms are locally closed. *)
Lemma typing_to_lc_tm : forall E e T,
    typing E e T -> lc_tm e.
Proof.
  intros E e T H.
  dependent induction H; eauto.
  - constructor.
    + auto.
    + destruct H. auto.
  - pick fresh x. apply H0 with x.
    apply notin_union_1 in Fr. auto.
Qed.

(** Substitution lemma *)      
Lemma typing_subst : forall (E F : ctx) e u S T (z : atom), 
  typing (F ++ [(z, S)] ++ E) e T ->
  typing E u S ->
  typing (F ++ E) (subst_tm u z e) T.
Proof.
  intros E F e u S T z He Hu.
  remember (F ++ [(z, S)] ++ E) as E'.
  generalize dependent F.
  induction He; subst; auto.
  - (* typ_int *) 
    intros F Heq.
    subst.
    simpl in *.
    apply typ_int.
  - (* typ_var *)     
    intros F Heq.
    subst.
    eapply typing_subst_var_case.
    apply H0.
    apply H.
    apply Hu.
  - (* typ_abs *) 
    intros F Heq.
    subst.
    simpl.
    apply typ_abs with (L := {{z}} \u L).
    intros y Fry.
    rewrite subst_var.
    rewrite_env (([(y, ty_poly_rho (ty_rho_tau tau1))] ++ F) ++ E).
    apply H0.
    auto.
    simpl_env. reflexivity.
    auto.
    eapply typing_to_lc_tm. apply Hu.
  - (* typ_app *)
    intros F Heq. simpl. eapply typ_app.
    ++ apply (IHHe1 _ Heq).
    ++ apply (IHHe2 _ Heq).
  - (* typ_let *)
    intros F Heq. eapply typ_let with (L := {{z}} \u L).  (* pick fresh x and apply typ_let. *) fold subst_tm.
    ++ eauto.
    ++ fold subst_tm. intros x Fry.
       rewrite subst_var.
       rewrite_env (([(x, sig)] ++ F) ++ E).
       apply H0.
       auto.
       subst. auto.
       auto.
       eapply typing_to_lc_tm. apply Hu.
  - (* exp_type_anno *)
    intros F Heq.
    eapply typ_annot; auto.
  - (* typ_gen *)
    intros F Heq.
    pick fresh x and apply typ_gen.
    apply H0; eauto.
Qed.


(* Simplified version of the substitution lemma *)
Lemma typing_subst_simple : forall (E : ctx) e u S T (z : atom),
  typing ([(z, S)] ++ E) e T ->
  typing E u S ->
  typing E (subst_tm u z e) T.
Proof.
  intros E e u S T z H J.
  rewrite_env (nil ++ E).
  eapply typing_subst.
  - simpl_env. apply H.
  - apply J.
Qed.


Print subst_ty_mono_ty_poly.
Check subst_ty_mono_ty_poly.


(** Decomposes opening of type variables into opening of type variable 
    opening & type variable substitution *)
Lemma subst_ty_poly_ty_mono_intro : forall (a : tyvar) (sig: ty_poly) (tau: ty_mono),
  a `notin` ftv_mono_ty_poly sig ->
  open_ty_poly_wrt_ty_mono sig tau = subst_ty_mono_ty_poly tau a (open_ty_poly_wrt_ty_mono sig tau).
Proof.
  intros a sig tau Hfree.
  unfold open_ty_poly_wrt_ty_mono.
  generalize 0.
  induction tau; intros n0; simpl; eauto.
  - (* ty_mono_base *)
    admit. (* TODO: not sure how to proceed *)
  Admitted. 

  



(* Is this what we want? *)
Fixpoint is_fresh_tyvar (alpha: tyvar) (Gamma: ctx) : bool :=
  match Gamma with
  | nil => true
  | (x,p) :: tl => if x == alpha then false else is_fresh_tyvar alpha tl
  end.

Fixpoint subst_ty_ctx (Gamma: ctx) (alpha: tyvar) (tau': ty_mono) : ctx :=
  match Gamma with
  | nil => nil
  | (x,p) :: tl => if x == alpha then (x,ty_poly_rho (ty_rho_tau tau'))::tl else (x,p)::subst_ty_ctx tl alpha tau'
  end.
    

Fixpoint subst_ty_ctx_new (Gamma: ctx) (alpha: tyvar) (tau': ty_mono) : ctx :=
  map (fun sig => 
    subst_ty_mono_ty_poly tau' alpha sig) Gamma.

Lemma subst_ty_ctx_preserves_flags:
  forall (Gamma Gamma' : ctx) (a: tyvar) t (tau: ty_mono) T T' (mf: mono_flag),
  typing Gamma t T ->
  Gamma' = subst_ty_ctx_new Gamma a tau ->
  typing Gamma t T' ->
  normalize_ty_poly_ty_mono T mf = normalize_ty_poly_ty_mono T' mf.
Proof.
  intros Gamma Gamma' a t tau T T' mf Htyp Heq.
  generalize dependent Gamma'.
  intros Gamma' HG Ht.
  induction mf.
  - inversion Ht. (* TODO: not sure how to continue *)
  Admitted.
  


(* TODO: to prove need to implement the following auxiliary components: *)
(* [is_fresh_tyvar] : predicate on [tyvars] which checks if a type variable is fresh with respect to the context *)
(* [subst_ty_ctx] : applies a substitution of type variables across the context *)


(* We are trying to say that if
Gamma, (x:type) |- M
 *)
(* Substitution lemma for type variables *)
Lemma ty_var_subst: forall (Gamma : ctx) (alpha: tyvar) e (sig: ty_poly) (tau': ty_mono),
  is_fresh_tyvar alpha Gamma = true -> 
  typing Gamma e sig ->
  typing (subst_ty_ctx_new Gamma alpha tau') (subst_ty_mono_tm tau' alpha e) (subst_ty_mono_ty_poly tau' alpha sig). 
Proof.
  intros Gamma alpha e sig tau' Hfresh Htyp.
  remember (subst_ty_ctx_new Gamma alpha tau') as G.
  generalize dependent G.
  induction e; intros.
  - destruct sig. destruct rho. destruct tau.  
    inversion Htyp; subst.
    + simpl; constructor.
    + simpl; constructor.
    + rewrite H. 
      simpl.
      constructor.
    + simpl.
      inversion Htyp; subst; eauto.
Admitted.      
  
(** Shallow subsumption relation *)
Inductive sh : ty_poly -> ty_poly -> Prop :=    (* defn sh *)
  | sh_refl : forall (sig:ty_poly),
      lc_ty_poly sig ->
      sh sig sig
  | sh_spec : forall (rho1 rho2:ty_rho) (tau:ty_mono),
      sh  (open_ty_poly_wrt_ty_mono (ty_poly_rho rho1) tau )  (ty_poly_rho rho2) ->
      sh (ty_poly_poly_gen (ty_poly_rho rho1)) (ty_poly_rho rho2)
  | sh_skol : forall (L:vars) (sig:ty_poly) (rho:ty_rho),
        ( forall a , a \notin  L  -> sh  ( open_ty_poly_wrt_ty_mono sig (ty_mono_var_f a) )  (ty_poly_rho  ( open_ty_rho_wrt_ty_mono rho (ty_mono_var_f a) ) ) )  ->
      sh (ty_poly_poly_gen sig) (ty_poly_poly_gen (ty_poly_rho rho)).

Notation "'|-sh' sig '<=' sig'" := (sh sig sig') (at level 40).


Lemma annot_inversion : forall (Gamma : ctx) (e : tm) (sig sig': ty_poly),
  typing Gamma (exp_type_anno e sig) sig' ->
  sh sig sig' ->
  typing Gamma e sig.
Proof.
  intros Gamma e sig sig' Htyp Hsh.
  induction Hsh; inversion Htyp; subst; eauto.
  - admit.
  - pick fresh a.
    rewrite (subst_ty_poly_ty_mono_intro a).
    admit. admit.
  - admit.
  - pick fresh a. 
    assert (a `notin` L).
    { fsetdec. }
  Admitted.

Lemma abs_inversion : forall G t T1 T2 L,
  typing G (exp_abs t) (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) ->
  forall x, x \notin L -> typing ((x, ty_poly_rho (ty_rho_tau T1)) :: G) (open_tm_wrt_tm t (exp_var_f x)) (ty_poly_rho (ty_rho_tau T2)).
Proof.
  intros G t T1 T2 L Htyp.
  remember (exp_abs t).
  generalize dependent t.
  induction Htyp; intros;
    repeat discriminate Heqt0.
  - (* TODO: figure out how to prove this inversion lemma *)
    admit.
  - admit. 
Admitted.
    


        
  

(* Inversion lemmas for Let-expressions *)
Lemma let_inversion : forall (Gamma : ctx) (u e : tm) (sig' : ty_poly),
    typing Gamma (exp_let u e) sig' ->
    exists L (sig : ty_poly), typing Gamma u sig /\
    forall x, x `notin` L -> typing ((x, sig)::Gamma) e sig'. 
Proof with eauto.
  intros Gamma u e sig' Htyping. remember (exp_let u e).
  dependent induction Htyping; try (inversion Heqt). 
  + (* ty_poly_rho rho *)
    subst.
    repeat eexists.
    ++ eauto.
    ++ intros.
       specialize (H0 x H1).
       simpl in H0.
       admit.
  + (* ty_poly_poly_gen (ty_poly_rho rho) *)  
    subst.
    exists L. 
    pick fresh a.
    exists (ty_poly_rho (open_ty_rho_wrt_ty_mono rho (ty_mono_var_f a))).
    admit.
  + (* open_ty_poly_wrt_ty_mono (ty_poly_rho rho) tau *) 
    inversion Htyping; subst; eauto.
    discriminate H4.
    * discriminate H4.
    * admit. (* TODO: not sure how to relate 
    [ty_poly_poly_gen (ty_poly_rho rho) to [open_ty_rho_wrt_ty_mono rho (ty_mono_var_f a)]] *) 
Admitted.       

(* Alt version of preservation: Inducting on small-step relation *)  
Theorem preservation_alt : forall (E : ctx) e e' T,
  typing E e T ->
  step e e' ->
  typing E e' T.
Proof with eauto.
  intros E e e' T Htyp Hstep.
  generalize dependent T.
  induction Hstep.
  - (* Step_let1 *)
    intros T Htyp.
    inversion Htyp; subst. eauto.
    + (* Goal: E |- exp_let u' t \in ty_poly_poly_gen sig *) admit.
    + pick fresh a. rewrite (subst_ty_poly_ty_mono_intro a)...
      (* TODO: Here is where we need the type subsituttion lemma *)
      * admit.
      * admit.  
  - (* Step_let *)  
    intros T Htyp; inversion Htyp; subst.
    + (* rho *)
      pick fresh x.
      rewrite (subst_tm_intro x)...
      eapply typing_subst_simple... 
    + (* ty_poly_poly_gen sig *) 
      pick fresh x.
      rewrite (subst_tm_intro x)...
      eapply typing_subst_simple.
      * admit. (* TODO: not sure how to proceed *)
      * admit. (* TODO *)
    + (* open_ty_poly_wrt_ty_mono sig tau *) 
      pick fresh a. 
      rewrite (subst_ty_poly_ty_mono_intro a)...
      admit. (* TODO: apply type substitution lemma*)
      admit.
  - (* Step_app1 *) 
    intros T Htyp; inversion Htyp; subst...
    + (* open_ty_poly_wrt_ty_mono sig tau *)  
      pick fresh a. admit.
      (* TODO: apply type substitution lemma*)
    + admit.
  - (* Step_app2 *) 
    intros T Htyp; inversion Htyp; subst...
    + admit. 
    + admit.
  Admitted.

(* Original version of preservation: inducting on typing judgement *)
Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.
Proof with eauto.
  intros E e e' T Htyp.
  generalize dependent e'.
  induction Htyp; intros e' J...
  - (* Literals don't step *) 
    inversion J.
  - (* Variables don't step *)
    inversion J.
  - (* Abs case *)
    inversion J.
  - (* App case *)
    inversion J; subst; eauto.
    + inversion Htyp1; subst.
      ++ pick fresh x. rewrite (subst_tm_intro x); auto. 
      eapply typing_subst_simple; auto.
      ++ pick fresh x. rewrite (subst_tm_intro x); auto. eapply typing_subst_simple; eauto. simpl.
        admit.
    + admit.
    (* inversion J; subst; eauto. *)
    (* + inversion Htyp1; subst. *)
    (*   * pick fresh y for (L \u fv_tm t0). *)
    (*     rewrite (subst_tm_intro y); auto. *)
    (*     eapply typing_subst_simple; auto. *)
    (*   * admit. *)
    (*     (* TODO: not sure how to prove typing derivations involving opening of terms *) *)
    (* + inversion Htyp1; subst. *)
    (*   admit. (* TODO: same problem as above *)  *)
  - (* Let case *)
    inversion J; subst; eauto.
    admit. (* TODO *)
  - (* typ_annot case -- this case is discharged *)
    inversion J; subst... 
Admitted.

