(** * HoareAsLogic: Hoare Logic as a Logic *)

Require Export Hoare.

(** The presentation of Hoare logic in chapter [Hoare] could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as _theorems_ about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Coq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic. *)

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq  : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

Tactic Notation "hoare_proof_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "H_Skip" | Case_aux c "H_Asgn" | Case_aux c "H_Seq"
  | Case_aux c "H_If" | Case_aux c "H_While" | Case_aux c "H_Consequence" ].

(** We don't need to include axioms corresponding to [hoare_consequence_pre]
    or [hoare_consequence_post], because these can be proven easily
    from [H_Consequence]. *)

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  (* FILL IN HERE *)
  intros.
  eapply H_Consequence.
  apply X.
  apply H.
  auto.
Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  (* FILL IN HERE *)
  intros.
  eapply H_Consequence.
  apply X.
  auto.
  apply H.
Qed.


(** Now, for example, let's construct a proof object representing a
    derivation for the hoare triple
      {{assn_sub X (X+1) (assn_sub X (X+2) (X=3))}} X::=X+1;; X::=X+2 {{X=3}}.
    We can use Coq's tactics to help us construct the proof object. *)

Example sample_proof
	     : hoare_proof
		 (assn_sub X (APlus (AId X) (ANum 1))
		   (assn_sub X (APlus (AId X) (ANum 2))
		     (fun st => st X = 3) ))
		 (X ::= APlus (AId X) (ANum 1);; (X ::= APlus (AId X) (ANum 2)))
		 (fun st => st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.
Print sample_proof.

(*
Print sample_proof.
====>
  H_Seq
    (assn_sub X (APlus (AId X) (ANum 1))
       (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3)))
    (X ::= APlus (AId X) (ANum 1))
    (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3))
    (X ::= APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3)
    (H_Asgn
       (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3))
       X (APlus (AId X) (ANum 1)))
    (H_Asgn (fun st : state => st X = VNat 3) X (APlus (AId X) (ANum 2)))
*)

(** **** Exercise: 2 stars (hoare_proof_sound)  *)
(** Prove that such proof objects represent true claims. *)

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *)
  intros.
  induction X; subst.
  Case "Skip". apply hoare_skip.
  Case "Assignment". apply hoare_asgn.  
  Case "Sequence". eapply hoare_seq. apply IHX2. apply IHX1.
  Case "IF". eapply hoare_if. apply IHX1. apply IHX2.
  Case "WHILE". eapply hoare_while. apply IHX.
  Case "Consequence".
      eapply hoare_consequence.
      apply IHX.
      unfold assert_implies; apply p.
      unfold assert_implies; apply q.
Qed.
(** [] *)

(** We can also use Coq's reasoning facilities to prove metatheorems
    about Hoare Logic.  For example, here are the analogs of two
    theorems we saw in chapter [Hoare] -- this time expressed in terms
    of the syntax of Hoare Logic derivations (provability) rather than
    directly in terms of the semantics of Hoare triples.

    The first one says that, for every [P] and [c], the assertion
    [{{P}} c {{True}}] is _provable_ in Hoare Logic.  Note that the
    proof is more complex than the semantic proof in [Hoare]: we
    actually need to perform an induction over the structure of the
    command [c]. *)

Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  com_cases (induction c) Case; intro P.
  Case "SKIP".
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  Case "::=".
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  Case ";;".
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  Case "IFB".
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  Case "WHILE".
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

(** Similarly, we can show that [{{False}} c {{Q}}] is provable for
    any [c] and [Q]. *)

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  (* intros [H1 H2]用来拆分合取式 H1 /\ H2，等价于intro H; destruct H.*)
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  com_cases (induction c) Case; intro Q.
  (* 如果不用pre_false_helper，需要按下面的方法，重复写几遍。 *)
  (* Case "SKIP". eapply H_Consequence_pre. apply H_Skip. intros st CONTRA. inversion CONTRA. *)
  Case "SKIP". pre_false_helper H_Skip.
  Case "::=". pre_false_helper H_Asgn.
  Case ";;". pre_false_helper H_Seq. apply IHc1. apply IHc2.
  Case "IFB".
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  Case "WHILE".
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

(** As a last step, we can show that the set of [hoare_proof] axioms is
    sufficient to prove any true fact about (partial) correctness.
    More precisely, any semantic Hoare triple that we can prove can
    also be proved from these axioms.  Such a set of axioms is said
    to be _relatively complete_. *)

(** This proof is inspired by the one at
http://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html
*)

(** To prove this fact, we'll need to invent some intermediate
    assertions using a technical device known as _weakest preconditions_.
    Given a command [c] and a desired postcondition assertion [Q],
    the weakest precondition [wp c Q] is an assertion [P] such that
    [{{P}} c {{Q}}] holds, and moreover, for any other assertion [P'],
    if [{{P'}} c {{Q}}] holds then [P' -> P].  We can more directly
    define this as follows: *)

(* 最弱前条件被定义为这样一个Assertion P，
   对于执行c之后，任意到达的终止状态s'，都能找到一个s，使得P s成立, 且Q s'成立。
   且不存在s，使得P s成立，但Q s'不成立。

   举例：
   {{P}} X ::= X + 1 {{X >= 1}}
   显然上面的hoare triple中，weakest P 应该是 X >= 0， 对于使得Q s'成立的任意状态s'，我们都能找到一个s，使得P s成立。

   我们不妨设想，如果 wp 是 X >= 1，那么对于终止状态s': X = 1，Q s'成立，但是该终止状态的初始状态s: X = 0，无法使得P s成立。
 *)
Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', c / s || s' -> Q s'.

(** **** Exercise: 1 star (wp_is_precondition)  *)
(* wp c Q 是 c {{Q}}的最弱前条件，那么{{wp c Q}} *)
Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
  (* FILL IN HERE *)
  intros c Q st st' H1 H2.
  apply H2.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star (wp_is_weakest)  *)
(* 任意一个合法的hoare triple，它的前条件P'都蕴含着最弱前条件（的性质）。 *)
Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
  (* FILL IN HERE *)
Proof.
  intros.
  unfold wp.
  intros.
  eapply H.
  apply H1.
  apply H0.
Qed.

(** The following utility lemma will also be useful. *)

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars (hoare_proof_complete)  *)
(** Complete the proof of the theorem. *)
(* 前面已经证明了<-，现在证明-> *)
Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  com_cases (induction c) Case; intros P Q HT.
  Case "SKIP".
    eapply H_Consequence.
     eapply H_Skip.
      intros.  eassumption.
      intro st. apply HT.  apply E_Skip.
  Case "::=".
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  Case ";;".
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
	 eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
     (* FILL IN HERE *)
  Case "IFB".
    apply H_If.
      apply IHc1.
      intros st st' H1 H2.
      eapply HT. apply E_IfTrue.
      apply H2. apply H1. apply H2.
      apply IHc2.
      intros st st' H1 H2.
      eapply HT. apply E_IfFalse.
      eapply bassn_eval_false.
      eapply H2. apply H1. apply H2.
  Case "WHILE".
    eapply H_Consequence.
    eapply H_While with (P:= wp (WHILE b DO c END) Q).
    apply IHc. unfold hoare_triple, wp.
    intros st st' Hc [Hw Hb] s' Hw'.
    apply Hw.
    eapply E_WhileLoop. unfold bassn in Hb. apply Hb.
    eapply Hc. apply Hw'.
    intros. eapply wp_is_weakest.
    eapply HT.
    apply H.
    intros st [H1 H2].
    unfold wp in H1.
    apply H1.
    eapply E_WhileEnd.
    apply bassn_eval_false.
    apply H2.
Qed.
  (** [] *)
                                                          
(** Finally, we might hope that our axiomatic Hoare logic is _decidable_;
    that is, that there is an (terminating) algorithm (a _decision procedure_)
    that can determine  whether or not a given Hoare triple is valid (derivable).
    But such a decision procedure cannot exist!

    Consider the triple [{{True}} c {{False}}]. This triple is valid
    if and only if [c] is non-terminating.  So any algorithm that could
    determine validity of arbitrary triples could solve the Halting Problem.

    Similarly, the triple [{{True} SKIP {{P}}] is valid if and only if
    [forall s, P s] is valid, where [P] is an arbitrary assertion of Coq's
    logic. But it is known that there can be no decision procedure for
    this logic.

*)

(** Overall, this axiomatic style of presentation gives a clearer picture of what it
    means to "give a proof in Hoare logic."  However, it is not
    entirely satisfactory from the point of view of writing down such
    proofs in practice: it is quite verbose.  The section of chapter
    [Hoare2] on formalizing decorated programs shows how we can do even
    better. *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

