(** * Prop: Propositions and Evidence *)

Require Export Logic.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** The first line declares that [ev] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    even" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  

    The last two lines declare the two ways to give evidence that a
    number [m] is even.  First, [0] is even, and [ev_0] is evidence
    for this.  Second, if [m = S (S n)] for some [n] and we can give
    evidence [e] that [n] is even, then [m] is also even, and [ev_SS n
    e] is the evidence.
*)


(** **** Exercise: 1 star (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    simpl. apply ev_0.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.
  (** [] *)



(* ##################################################### *)

(** For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty)  *)
(** How many different ways are there to show that [8] is [beautiful]? *)
(* 上面的说明已经介绍了两种方法，它们是按条件引用的先后顺序来说明8是beautiful number *)
(* 还可以从goal出发，逆向寻找可以支持goal成立的充分条件：
   goal： 8 是 beautiful number成立，根据规则b_sum，需要下面的命题成立：
   H1: 存在n和m，n + m = 8且n和m都是beautiful。显然H1是成立的，只要n = 3和m = 5。
   所以goal成立。
 *)
(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Constructing Evidence *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
(* FILL IN HERE *)
  intros.
  simpl.
  apply b_sum with (n:=n) (m:=n + 0).
  apply H.
  apply b_sum with (n:=n) (m:=0).
  apply H.
  apply b_0.
Qed.
(** [] *)

(** **** Exercise: 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  (* FILL IN HERE *)
  intros.
  induction m as [|m'].
  Case "m = 0".
    simpl. apply b_0.
  Case "m = S m'".
    simpl.
    apply b_sum with (n:=n) (m:=m' * n).
    apply H.
    apply IHm'.
Qed.
(** [] *)


(* ####################################################### *)
(** * Using Evidence in Proofs *)
(** ** Induction over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** *** *)
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree)  *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* FILL IN HERE *)
[]
*)

(** **** Exercise: 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  (* FILL IN HERE *)
  intros.
  apply g_plus3.
  do 2 apply g_plus5.
  apply H.
Qed.
(** [] *)

(** *** *)
(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Let's see what happens if we try to prove this by induction on the evidence [H]
   instead of on [n]. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* These exercises also require the use of induction on the evidence. *)

(** **** Exercise: 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  (* FILL IN HERE *)
  intros n m H1 H2.
  induction H1 as [|n'|n'].
  Case "g_0". simpl. apply H2.
  Case "g_plus3". apply g_plus3 with (n:=n'+m). apply IHgorgeous.
  Case "g_plus5". apply g_plus5 with (n:=n'+m). apply IHgorgeous.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  (* FILL IN HERE *)
  intros.
  induction H as [ | | |n'].
  Case "b_0". apply g_0.
  Case "b_3". apply g_plus3. apply g_0.
  Case "b_5". apply g_plus5. apply g_0.
  Case "b_sum". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
(** [] *)


(** **** Exercise: 3 stars, optional (g_times2)  *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
  (* FILL IN HERE *)
  intros.
  SearchAbout plus.
  rewrite plus_swap.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* FILL IN HERE *)
   Case "g_0". simpl. apply g_0.
   Case "g_plus3".
     apply g_plus3 with (n:=n + (3 + n + 0)).
     rewrite helper_g_times2.
     apply g_plus3 with (n:=n + n + 0).
     SearchAbout plus.
     rewrite plus_assoc with (p:=0) in IHgorgeous.
     apply IHgorgeous.
   Case "g_plus5".
     apply g_plus5 with (n:=n + (5 + n + 0)).
     rewrite helper_g_times2.
     apply g_plus5 with (n:=n + n + 0).
     rewrite plus_assoc with (p:=0) in IHgorgeous.
     apply IHgorgeous.
Qed.
(** [] *)



(** Here is a proof that the inductive definition of evenness implies
the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** **** Exercise: 1 star (ev__even)  *) 
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)
(* FILL IN HERE *)
(** [] *)

(** Intuitively, the induction principle [ev n] evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercise: 1 star (l_fails)  *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* FILL IN HERE *)
因为对全称命题采用归纳法证明，一切从定义出发。根据nat的定义，n要么等于0，要么等于(S n')。
对于n = 0的情况，我们很容易根据ev定义的规则来判定0是even number；
对于n = S n'的情况，我们从ev定义中，找不出一条规则（没有匹配的模式）来说明(S n')是even number。因此，证明失败。
*)
(** [] *)

(** Here's another exercise requiring induction on evidence. *)
(** **** Exercise: 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *)
  intros.
  induction H as [|n'].
  Case "n = 0". simpl. apply H0.
  Case "n = S (S n')".
    simpl.
    apply ev_SS.
    apply IHev.
Qed.
(** [] *)



(* ####################################################### *)
(** ** Inversion on Evidence *)


(** Having evidence for a proposition is useful while proving, because we 
   can _look_ at that evidence for more information. For example, consider 
    proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  Instead 
    the [inversion] tactic provides all of the information that we need.

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n)  *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)
Theorem ev_minus2_destruct_version: forall n,  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n as [|n'].
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n'". simpl. SearchAbout pred.
Abort.
(* 使用destruct对n进行分情况讨论时，会出现ev (S n') -> ev (pred n')，而这个蕴含式
   无法直接从ev的定义证明。
 *)

(* FILL IN HERE *)
(** [] *)

(** *** *)
(** Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** The Inversion Tactic Revisited *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate  between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    [inversion]把那些自相矛盾的subgoal丢弃，意思是无需证明，因为Fasle蕴含一切命题。
    而那些没有被丢掉的subgoal，就构成了original goal的完整充分条件。

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *)
  intros n H.
  inversion H as [|n' H'].
  inversion H' as [|n'' H''].
  apply H''.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *)
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *)
  intros n m Enplusm En.
  induction En as [| n' IHn'].
  Case "En = ev_0".
    simpl in Enplusm.
    apply Enplusm.
  Case "En = ev_SS".
    simpl in Enplusm.
    inversion Enplusm.
    apply IHIHn'.
    apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *)
  intros n m p Enm Enp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Enm.
  replace ((n+m) + (n+p)) with ((n + n) + (m + p)) in Enm.
  replace (n+n) with (double n) in Enm.
  apply ev_ev__ev with (m:=m+p) in Enm.
  apply Enm.
  replace (double n + (m + p) + (m + p)) with (double n + ((m + p) + (m + p))).
  replace  (m + p + (m + p)) with (double (m + p)).
  apply ev_sum.
  apply double_even.
  apply double_even.
  apply double_plus with (n:=m+p).
  apply plus_assoc with (n:=double n).
  apply double_plus.
  rewrite <- plus_assoc.
  replace (n+(m+p)) with (m+(n+ p)).
  rewrite plus_assoc.
  reflexivity.
  apply plus_swap.
  apply Enp.
Qed.
(** [] *)


(* ####################################################### *)
(** * Discussion and Variations *)
(** ** Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Parameterized Data Structures *)

(** So far, we have only looked at propositions about natural numbers. However, 
   we can define inductive predicates about any type of data. For example, 
   suppose we would like to characterize lists of _even_ length. We can 
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** Of course, this proposition is equivalent to just saying that the
length of the list is even. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** However, because evidence for [ev] contains less information than
evidence for [ev_list], the converse direction must be stated very
carefully. *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil. 
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l. 
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.


(** **** Exercise: 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

(* 我递归定义的回文列表 *)
Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil: pal []
  | pal_one: forall x, pal [x]
  | pal_cc: forall y l, pal l -> pal ( snoc ( cons y l ) y ).

Theorem pal_app_rev:
  forall X (l: list X), pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|h l'].
  Case "l = []".
    simpl. apply pal_nil.
  Case "l = h::l'".
    simpl. SearchAbout snoc.
    rewrite <- snoc_with_append.
    apply pal_cc.
    apply IHl'.
Qed.

Theorem pal_rev:
  forall X (l: list X), pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
  Case "H: pal_nil".
    simpl. reflexivity.
  Case "H: pal_one".
    simpl. reflexivity.
  Case "H: pal_cc".
    simpl.
    SearchAbout snoc.
    rewrite rev_snoc.
    simpl.
    rewrite <- IHpal.
    reflexivity.
Qed.
(* FILL IN HERE *)
(** [] *)

(* Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)
Theorem rev_pal:
  forall X (l: list X), l = rev l -> pal l.
Proof. Admitted.
(* FILL IN HERE *)
(** [] *)



(* ####################################################### *)
(** ** Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** *** *)
(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  do 3 apply le_S.
  (* apply le_S. apply le_S. apply le_S. *)
  apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
Inductive total_relation : nat -> nat -> Prop :=
  | total_rel: forall n m: nat, total_relation n m.
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat -> nat -> Prop :=
  | empty_rel: forall n m: nat, False -> empty_relation n m.
(* False -> P 的意思是不管从什么状态，都推不出P成立。
   换句话说，就是找不到一个可以使P成立的前提条件。
   套用在这里，我们就是说：找不到一个可以使得二元关系empty_relation(n, m)成立的前提条件
 *)
Eval compute in (empty_relation 1 3).
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *)
  intros m n o H1 H2.
  induction H2.
  Case "n = o". apply H1.
  Case "n = S m0". apply le_S in IHle. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *)
  intros.
  induction n as [|n'].
  Case "n = 0". apply le_n.
  Case "n = S". apply le_S in IHn'. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* FILL IN HERE *)
   intros n m H. induction H.
   Case "H: le_n". apply le_n.
   Case "H: le_S". apply le_S. apply IHle.
Qed.

Lemma Sn_le_m__n_le_m : forall n m,
  S n <= m -> n <= m.
Proof.
  intros n m H. induction H.
  Case "le_n". apply le_S. apply le_n.
  Case "le_S". apply le_S. apply IHle.  Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* FILL IN HERE *)
  intros n m H.
  inversion H.
  Case "H: le_n". apply le_n.
  Case "H: le_S". apply Sn_le_m__n_le_m in H1. apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* FILL IN HERE *)
  intros a b.
  induction b as [|b'].
  Case "b = 0".
    SearchAbout plus.
    rewrite plus_0_r.
    apply le_n.
  Case "b = S b'".
    SearchAbout plus.
    rewrite <- plus_n_Sm.
    apply le_S.
    apply IHb'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt. 
  (* FILL IN HERE *)
  intros.
  split.
  Case "subgoal: S n1 <= m".
    induction n2 as [|n2'].
    SCase "n2 = 0". rewrite plus_0_r in H. apply H.
    SCase "n2 = S n2'".
      apply IHn2'. rewrite <- plus_n_Sm with (n:=n1) (m:=n2') in H.
      apply Sn_le_m__n_le_m in H. apply H.
  Case "subgoal: S n2 <= m".
    induction n1 as [|n1'].
    SCase "n1 = 0". simpl in H. apply H.
    SCase "n1 = S n1'".
    apply IHn1'. simpl in H. apply Sn_le_m__n_le_m in H. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *)
  unfold lt.
  intros.
  apply le_S.
  apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *)
  intros n m. generalize dependent n.
  induction m as [|m']. (* 先对m做归纳，这是因为二元关系<=的定义就是以m为递归。 *)
  Case "m = 0".
    destruct n as [|n'].
    SCase "n = 0". intros. apply le_n.
    SCase "n = S n'". intros. inversion H.
  Case "m = S m'".
    destruct n as [|n'].
    SCase "n = 0". intros. apply O_le_n.
    SCase "n = S n'".
      intros.
      simpl in H.
      apply n_le_m__Sn_le_Sm.
      apply IHm'.
      apply H.
Qed.



Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on [m]. *)
  (* FILL IN HERE *)
  intros n m. generalize dependent n.
  induction m as [|m'].
  Case "m = 0".
    destruct n as [|n'].
    SCase "n = 0". intros. simpl. reflexivity.
    SCase "n = S n'". intros. inversion H.
  Case "m = S m'".
    destruct n as [|n'].
    SCase "n = 0".
      intros.
      unfold ble_nat. reflexivity.
    SCase "n = S n'".
      intros.
      simpl.
      apply IHm'.
      apply Sn_le_Sm__n_le_m in H.
      apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* Hint: This theorem can be easily proved without using [induction]. *)
  (* FILL IN HERE *)
  (* 想法：把ble_nat_true的性质证明，转化为证明le的性质，而le的性质我们已经证明了很多，
          这些都可以直接拿来引证。
   *)
  intros.
  apply le_ble_nat.
  apply ble_nat_true in H.
  apply ble_nat_true in H0.
  generalize dependent H0.
  generalize dependent H.
  apply le_trans.
Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *)
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m = 0".
    destruct n as [|n'].
    SCase "n = 0". intros. inversion H.
    SCase "n = S n'".
      intros.
      SearchAbout "~".
      unfold not.
      intros.
      inversion H0.
  Case "m = S m'".
    destruct n as [|n'].
    SCase "n = 0".
      unfold not.
      intros.
      inversion H.
    SCase "n = S n'".
      unfold not.
      intros.
      simpl in H.
      apply Sn_le_Sm__n_le_m in H0.
      apply le_ble_nat in H0.
      rewrite H in H0.
      inversion H0.
Qed.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
A1: [R 1 1 2] is provable.

A2: No, because for parameters m and n in rule(c1 ~ c4), symmetry is found.
    For example, if n = m + k1,b o = 2m + k2
        Via rule c5 => R m (m + k1) (2m + k2) -> R (m + k1) m (2m + k2).
    But actuall we can get the conclusion by rule(c2 c3 c4):
        Via rule c4 => R m (m + k1) (m + k2) -> R 0 k1 k2
        Via rule c2 => R 0 k1 k2 -> R m k1 (m + k2)
        Via rule c3 => R m k1 (m + k2) -> R m (m + k1) (2m + k2)

A3: No, because c1 c2 c3 can generalize total situation of R relation.
    why?
    Let's consider it as follows:
    if R (S m) (S n) (S (S o)) is true, it can be produced by rule c2:
        R m (S n) (S o) -> R (S m) (S n) (S (S o))
    while R m (S n) (S o) can be produced by rule c3:
        R m n o -> R m (S n) (S o)
    So R m n o is exactly true. It means we do not need rule c4.

[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)  
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
Theorem R_m_n_o__mplusn_o:
  forall m n o: nat, R m n o -> m + n = o.
Proof.
  intros.
  induction H.
  Case "H: c1". reflexivity.
  Case "H: c2".
    simpl.
    apply f_equal.
    apply IHR.
  Case "H: c3".
    SearchAbout plus.
    rewrite <- plus_n_Sm.
    apply f_equal.
    apply IHR.
  Case "H: c4".
    simpl in IHR.
    rewrite <- plus_n_Sm in IHR.
    inversion IHR.
    reflexivity.
  Case "H: c5".
    SearchAbout plus.
    rewrite plus_comm.
    apply IHR.
Qed.

Theorem mpulsn_o__R_m_n_o:
  forall m n o: nat, m + n = o -> R m n o.
Proof.
  intros.
  induction H.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    induction n as [|n'].
    SCase "n = 0".
      apply c1.
    SCase "n = S n'".
      apply c3.
      apply IHn'.
  Case "m = S m'".
    induction n as [|n'].
    SCase "n = 0".
      simpl.
      apply c2.
      apply IHm'.
    SCase "n = S n'".
      simpl.
      apply c2 in IHm'.
      apply IHm'.      
Qed.
(* FILL IN HERE *)
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is, 
      any list is a subsequence of itself.  

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3], 
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is 
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2] 
      is a subsequence of [l3], then [l1] is a subsequence of [l3].  
      Hint: choose your induction carefully!
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(** * Programming with Propositions *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)


