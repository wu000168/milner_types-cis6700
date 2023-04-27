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
Notation "# i" := (exp_lit i) (in custom exp at level 80) : exp_scope.


Notation "$ y" := (ty_mono_var_f y) (in custom exp at level 50, right associativity) : exp_scope.
Notation "T1 -> T2" := (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) (in custom exp at level 80, right associativity) : exp_scope.
Notation "T1 -> T2" := (ty_rho_tau (ty_mono_func T1 T2)) (in custom exp at level 80, right associativity) : exp_scope.
Notation "sig ^ tau" := (open_ty_poly_wrt_ty_mono sig tau) (in custom exp at level 1, left associativity) : exp_scope.
Notation "\gen sig" := (ty_poly_poly_gen sig) (in custom exp at level 1, left associativity) : exp_scope.
Notation "{{ rho }}" := (ty_poly_rho rho) (in custom exp at level 80, left associativity) : exp_scope.
Notation "{ tau }" := (ty_rho_tau tau) (in custom exp at level 80, left associativity) : exp_scope.
Notation "tau1 { x ~> tau2 }" := (subst_ty_mono_ty_mono tau2 (ty_mono_var_f x) tau1) (in custom exp at level 70, left associativity) : exp_scope.
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

Lemma gen_inst_inv: forall sig rho tau,
  inst (ty_poly_poly_gen sig) rho
    -> inst (open_ty_poly_wrt_ty_mono sig tau) rho.
Proof with eauto.
  intros. dependent induction H. pick fresh x.
  (* rewrite (subst_ty_mono_ty_poly_intro x) in IHinst; try fsetdec.
  rewrite subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono in IHinst.
  rewrite subst_ty_mono_ty_mono_fresh_eq in IHinst.
   *)
Admitted.

Lemma gen_inst_int: forall tau sig x,
    inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau ty_mono_base)
    -> inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau ty_mono_base).
Proof with eauto.
  intros tau sig x H. 
  dependent induction H; destruct sig; try discriminate; intros.
  + destruct rho; try discriminate.
    inversion x; clear x. destruct tau0; try discriminate; try repeat constructor.
    (* destruct n; try discriminate. destruct tau; try discriminate. *)
    (* cbv in H1... *)

Admitted.

(* Lemma gen_inst_int: forall tau sig L,
  (forall x, x `notin` L ->
    inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau ty_mono_base) )
    -> inst sig (ty_rho_tau ty_mono_base).
Proof. *)
  (* (* intros tau sig L Hinst. dependent induction Hinst; intros. *)
  - destruct sig; try destruct rho.
    + simpl in x. inversion x. clear x; simpl in H2.
      induction tau0; cbv in H2; try repeat constructor.
      * 

    admit.
      (* destruct subst_ty_mono_ty_mono_fresh_eq in H1...
      destruct tau0; try discriminate. exists tau0_1. exists tau0_2.
      constructor. rewrite H1 in H... admit. *)
    + simpl in x. discriminate.
  - admit. *)

Lemma canonical_forms_int : forall (t : tm) T,
    typing empty t T ->
    inst T (ty_rho_tau ty_mono_base) ->
    is_value_of_tm t ->
    exists (i : integer), t = exp_lit i.
Proof with eauto.
  intros t T Ht Hi Hv. generalize dependent Hi.
  dependent induction Ht; intros; try destruct Hv...
  - inversion Hi; subst.
  - pick fresh x.
    specialize (H x ltac:(auto)). specialize (H0 x ltac:(auto) ltac:(eauto) Hv).
    inversion Hi; subst.
    (* rewrite (subst_ty_mono_ty_poly_intro x) in H2. *)
    (* apply (gen_inst_int _ _ x) in H2. *)
    (* apply (H0 H2). fsetdec. *)
Admitted.

Lemma lc_open_mono: forall tau1 tau2,
  degree_ty_mono_wrt_ty_mono 1 tau1 -> lc_ty_mono tau2 -> lc_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2).
Proof with eauto.
  intros tau1 tau2 H1 H2.
  induction tau1...
  - destruct n... inversion H1; subst. inversion H3; subst... inversion H0...
  - constructor...
  - inversion H1; subst. constructor...
Qed.

Lemma lc_open_mono_inv: forall tau1 tau2,
   lc_ty_mono (open_ty_mono_wrt_ty_mono tau1 tau2) -> lc_ty_mono tau2
    -> degree_ty_mono_wrt_ty_mono 1 tau1.
Proof with eauto.
  intros tau1 tau2 H1.
  dependent induction H1; intros...
  - destruct tau1; try discriminate...
    destruct n... discriminate x.
  - destruct tau1; try discriminate...
    destruct n... discriminate x.
  - destruct tau1; try discriminate...
    + destruct n... discriminate x.
    + inversion x.
      specialize (IHlc_ty_mono1 tau1_1 tau2 ltac:(auto) ltac:(auto)).
      specialize (IHlc_ty_mono2 tau1_2 tau2 ltac:(auto) ltac:(auto)).
      constructor...
Qed.

Lemma open_var_f_fun: forall sig T1 T2 x, x `notin` ftv_mono_ty_poly sig ->
  inst (open_ty_poly_wrt_ty_mono sig (ty_mono_var_f x)) (ty_rho_tau (ty_mono_func T1 T2))
    -> forall tau', lc_ty_mono tau' -> exists T1' T2', inst (open_ty_poly_wrt_ty_mono sig tau') (ty_rho_tau (ty_mono_func T1' T2')) .
Proof with eauto.
  intros sig T1 T2 x Fr Hinst.
  dependent induction Hinst; intros.
  - destruct sig; try discriminate.
    destruct rho; try discriminate.
    destruct tau; try discriminate.
    destruct n; try discriminate.
    inversion x.
    exists (open_ty_mono_wrt_ty_mono tau1 tau').
    exists (open_ty_mono_wrt_ty_mono tau2 tau').
    repeat constructor; inversion H;
    inversion H4; subst;
    apply (lc_open_mono_inv tau1 (ty_mono_var_f x0)) in H7;
    apply (lc_open_mono_inv tau2 (ty_mono_var_f x0)) in H8; eauto;
    apply lc_open_mono...
  (* - specialize (IHHinst x0 T2 T1 sig0 ltac:(auto) ltac:(auto) ltac:(auto) tau' H).
    destruct sig; try discriminate.
    inversion x; subst; clear x. specialize (H y ltac:(auto)).
    destruct sig; try discriminate; simpl in *.
    + admit.
    + admit. *)
Admitted.

Lemma open_base_fun: forall sig T1 T2 x,
  inst (subst_ty_mono_ty_poly ty_mono_base x sig) (ty_rho_tau (ty_mono_func T1 T2)) 
    -> forall tau', lc_ty_mono tau' -> exists T1' T2', inst (subst_ty_mono_ty_poly tau' x sig) (ty_rho_tau (ty_mono_func T1' T2')) .
Proof with eauto.
  intros sig T1 T2 x Hinst.
  dependent induction Hinst; intros.
  - destruct sig; try discriminate.
    destruct rho; try discriminate.
    destruct tau; try discriminate.
    destruct (eq_dec x0 a); subst.
    + inversion x. destruct (a == a); try discriminate.
    + inversion x. destruct (a == x0); try discriminate.
    + simpl.
      exists (subst_ty_mono_ty_mono tau' x0 tau1).
      exists (subst_ty_mono_ty_mono tau' x0 tau2).
      inversion x; subst. constructor. constructor.
      dependent induction H.
Admitted.

Theorem canonical_forms_fun0: forall t T1 T2,
  typing empty t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))
    -> is_value_of_tm t 
    -> exists u, t = exp_abs u.
Proof with eauto.
  intros t T1 T2 Ht.
  dependent induction Ht; try discriminate; intros...
  - destruct H1.
  - destruct H.
  - destruct H1.
  - destruct H0.
  - destruct sig. destruct rho. destruct tau0; try discriminate...
    destruct n; cbv in x. destruct tau; try discriminate.
    inversion x; subst.
Admitted.

Theorem canonical_forms_fun: forall t T,
  typing empty t T
    -> forall T1 T2, inst T (ty_rho_tau (ty_mono_func T1 T2))
    -> is_value_of_tm t 
    -> exists u, t = exp_abs u.
Proof with eauto.
  intros t T Ht.
  dependent induction Ht; try discriminate; intros.
  - inversion H.
  - inversion H2.
  - inversion H1; subst...
  - inversion H0.
  - inversion H2.
  - inversion H1.
  - remember (ty_poly_poly_gen sig) as sig'.
    remember (ty_rho_tau (ty_mono_func T1 T2)) as rho.
    induction H1; subst; try discriminate.
    inversion Heqsig'; subst. clear H3.
    pick fresh a. specialize (H1 a ltac:(auto)).
    specialize (H0 a ltac:(auto) ltac:(auto) T1 T2 H1 H2)...
  - induction sig.
    + admit.
    + specialize (IHHt ltac:(auto))...
Admitted.

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

(* Lemma uniq_type_int: forall T n,
  typing empty (exp_lit n) T
    -> inst T (ty_rho_tau ty_mono_base).
Proof with eauto.
  intros. dependent induction H...
  + pick fresh a.
    specialize (H a ltac:(auto)).
    specialize (H0 a ltac:(auto) n ltac:(auto) ltac:(auto)).
    inversion H0; subst...
  + specialize (IHtyping n ltac:(auto) ltac:(auto)).
    inversion IHtyping; subst. pick fresh x.
    rewrite (subst_ty_mono_ty_poly_intro x _ tau0) in H2...
    apply gen_inst_int in H2.

 *)

Lemma empty_ctx_typing_lc_ty: forall e T,
  typing empty e T -> lc_ty_poly T.
Proof with eauto.
  intros e. destruct T.
  dependent induction e; intros; inversion H; subst...
  - destruct sig; try discriminate H0. constructor.
    destruct rho0; destruct tau0.
    + cbv...
    + destruct n; simpl...
      simpl.
  (* - clear H0. pick fresh x; specialize (H x ltac:(auto)). *)
    (* induction t; cbv in H. inversion H; subst. *)
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
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun t _ H0_ tau1 tau2)... constructor.
        eapply empty_ctx_typing_lc_ty in H0_. inversion H0_... }
      destruct Hlam; subst...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun t _ H0_ tau1 tau2)... constructor.
      eapply empty_ctx_typing_lc_ty in H0_. inversion H0_... }
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
  induction H; intros G0 Eq Uniq; subst; eauto.
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
Qed. 
 
(** Original statemnent of the weakening lemma *)
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

(* TODO: subst_exp_intro ??? *)



   
(* NB: In the Metalib notes, [[ z ~> u ] e] denotes[subst_exp u z e] *)  


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
  - apply typ_var.
    + eapply uniq_remove_mid. apply Huniq.
    + eapply binds_remove_mid.
      ++ apply Hbinds.
      ++ assumption.
Qed.

Lemma typing_to_lc_tm : forall E e T,
    typing E e T -> lc_tm e.
Proof.
  Admitted.

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
  - intros F Heq. simpl. eapply typ_app.
    ++ apply (IHHe1 _ Heq).
    ++ apply (IHHe2 _ Heq).
  - intros F Heq. eapply typ_let with (L := {{z}} \u L).  (* pick fresh x and apply typ_let. *) fold subst_tm.
    ++ eauto.
    ++ fold subst_tm. intros x Fry.
       rewrite subst_var.
       rewrite_env (([(x, sig)] ++ F) ++ E).
       apply H0.
       auto.
       subst. auto.
       auto.
       eapply typing_to_lc_tm. apply Hu.
  - simpl. admit.
  - intros F Heq.



    
Admitted.



Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.
Proof with eauto.
  intros E e e' T Htyp Hstep.


Admitted.

