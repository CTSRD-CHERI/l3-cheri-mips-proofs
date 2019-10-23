(*<*)

(* Author: Kyndylan Nienhuis *)

theory CheriAltDefs

imports 
  "Preamble"
  "L3Lemmas"
  "CHERI-p256.CHERI_Monadic_p256"
begin

(*>*)
section \<open>Alternative definitions\<close>

text \<open>In this theory we give an alternative definition for all CHERI instructions and auxiliary
functions. Each alternative definition is equivalent to the original definition. The first
transformation is that we remove all occurrences of @{const extend_state}. We achieve this by
substituting the value of the extra state components in the places where they are used. To cover
for-loops, we define a new variant that carries a value to the next iteration. The second
transformation is that we merge accessing or updating sub-components of the state into one step.\<close>

section \<open>Preamble\<close>

text \<open>The following is conceptually part of the theory Preamble, but could not be inserted there
because Preamble.thy cannot have a reference to CHERI.\<close>

subsection \<open>Distributive laws\<close>

text \<open>We collect the distributive laws of the types of cases that are used in the model.\<close>

lemmas case_distrib = 
  Option.option.case_distrib
  List.list.case_distrib
  Product_Type.prod.case_distrib
  bool.case_distrib
  DataType.case_distrib
  ShadowMem.case_distrib
  ShadowTags.case_distrib
  RegSet.case_distrib
  CmpType.case_distrib
  Branch.case_distrib
  CP.case_distrib
  Store.case_distrib
  Load.case_distrib
  Trap.case_distrib
  Shift.case_distrib
  MultDiv.case_distrib
  ArithR.case_distrib
  ArithI.case_distrib
  CGet.case_distrib
  CSet.case_distrib
  CCheck.case_distrib
  CHERICOP2.case_distrib
  COP2.case_distrib
  CHERISWC2.case_distrib
  SWC2.case_distrib
  CHERILWC2.case_distrib
  LWC2.case_distrib
  CHERILDC2.case_distrib
  LDC2.case_distrib
  CHERISDC2.case_distrib
  SDC2.case_distrib
  instruction.case_distrib

lemmas case_distrib_cancel [simp] = 
  case_distrib[where h="\<lambda>_. _", THEN sym]

lemmas if_distrib_h = 
  if_distrib[where f=h] for h

lemma let_distrib:
  shows "h (let x = y in f x) = (let x = y in h (f x))"
by simp

lemmas all_distrib = 
  if_distrib_h
  let_distrib
  case_distrib

lemmas ValuePart_cases [ValueAndStatePart_simp] =
  all_distrib[where h="\<lambda>x. ValuePart x _"]

lemmas StatePart_cases [ValueAndStatePart_simp] =
  all_distrib[where h="\<lambda>x. StatePart x _"]

subsection \<open>Split laws\<close>

lemmas case_split = 
  Option.option.split
  List.list.split
  Product_Type.prod.split
  bool.split
  DataType.split
  ShadowMem.split
  ShadowTags.split
  RegSet.split
  CmpType.split
  Branch.split
  CP.split
  Store.split
  Load.split
  Trap.split
  Shift.split
  MultDiv.split
  ArithR.split
  ArithI.split
  CGet.split
  CSet.split
  CCheck.split
  CHERICOP2.split
  COP2.split
  CHERISWC2.split
  SWC2.split
  CHERILWC2.split
  LWC2.split
  CHERILDC2.split
  LDC2.split
  CHERISDC2.split
  SDC2.split
  instruction.split

lemma let_split:
  fixes P
  shows "P (let x = y in f x) = (\<forall>x. x = y \<longrightarrow> P (f x))"
by simp

lemmas all_split = 
  if_splits(1)
  let_split
  case_split
  
(*
(* I tried to get the above lemmas for free using one of the following existing lemmas. *)

thm instruction.case_distrib
thm instruction.induct
thm instruction.exhaust
thm instruction.split

(* However, xxx.split doesn't work, because I can't get rid of the conjunction. *)
lemmas foo_split = 
  instruction.split[where P="isInvariant _", THEN sym, THEN iffD1, OF conjI, OF allI, OF impI]

(* But I could use split, and also add conjI, allI and impI to the method *)
lemmas foo_split2  = 
  instruction.split[where P="isInvariant _", THEN sym, THEN iffD1]

(* xxx.exhaust doesn't work, because I can't bind P and y to something that shares a variable. *)
lemmas foo_exhaust = 
  instruction.exhaust[where P="isInvariant _ _" and y="_"]

(* xxx.induct does work, but takes much too long to process, and I still need to state the case. *)
lemmas foo_induct = 
  instruction.induct[where P="\<lambda>ins. isInvariant _ 
                         (case ins of ArithI x \<Rightarrow> _ x
                                   |  ArithR x \<Rightarrow> _ x
                                   |  BREAK \<Rightarrow> _
                                   |  Branch x \<Rightarrow> _ x
                                   |  CACHE x \<Rightarrow> _ x
                                   |  COP1 x \<Rightarrow> _ x
                                   |  COP2 x \<Rightarrow> _ x
                                   |  CP x \<Rightarrow> _ x
                                   |  ERET \<Rightarrow> _ 
                                   |  LDC2 x \<Rightarrow> _ x
                                   |  LWC2 x \<Rightarrow> _ x
                                   |  Load x \<Rightarrow> _ x
                                   |  MultDiv x \<Rightarrow> _ x
                                   |  RDHWR x \<Rightarrow> _ x
                                   |  ReservedInstruction \<Rightarrow> _
                                   |  SDC2 x \<Rightarrow> _ x
                                   |  SWC2 x \<Rightarrow> _ x
                                   |  SYNC x \<Rightarrow> _ x
                                   |  SYSCALL \<Rightarrow> _ 
                                   |  Shift x \<Rightarrow> _ x
                                   |  Store x \<Rightarrow> _ x
                                   |  TLBP \<Rightarrow> _
                                   |  TLBR \<Rightarrow> _ 
                                   |  TLBWI \<Rightarrow> _
                                   |  TLBWR \<Rightarrow> _
                                   |  Trap x \<Rightarrow> _ x
                                   |  Unpredictable \<Rightarrow> _
                                   |  WAIT \<Rightarrow> _)"]

(* xxx.case_distrib doesn't work, because it doesn't get rid of the case in the assumption. *)
lemmas foo_case_distrib =
  instruction.case_distrib[where h="isInvariant _", THEN sym, THEN iffD1]
*)

subsection \<open>Congruences\<close>

lemmas weak_cong = 
  if_weak_cong
  option.case_cong_weak
  list.case_cong_weak
  prod.case_cong_weak
  DataType.case_cong_weak
  ShadowMem.case_cong_weak
  ShadowTags.case_cong_weak
  RegSet.case_cong_weak
  CmpType.case_cong_weak
  Branch.case_cong_weak
  CP.case_cong_weak
  Store.case_cong_weak
  Load.case_cong_weak
  Trap.case_cong_weak
  Shift.case_cong_weak
  MultDiv.case_cong_weak
  ArithR.case_cong_weak
  ArithI.case_cong_weak
  CGet.case_cong_weak
  CSet.case_cong_weak
  CCheck.case_cong_weak
  CHERICOP2.case_cong_weak
  COP2.case_cong_weak
  CHERISWC2.case_cong_weak
  SWC2.case_cong_weak
  CHERILWC2.case_cong_weak
  LWC2.case_cong_weak
  CHERILDC2.case_cong_weak
  LDC2.case_cong_weak
  CHERISDC2.case_cong_weak
  SDC2.case_cong_weak
  instruction.case_cong_weak

lemmas cong =
  if_cong
  option.case_cong
  list.case_cong
  prod.case_cong
  DataType.case_cong
  ShadowMem.case_cong
  ShadowTags.case_cong
  RegSet.case_cong
  CmpType.case_cong
  Branch.case_cong
  CP.case_cong
  Store.case_cong
  Load.case_cong
  Trap.case_cong
  Shift.case_cong
  MultDiv.case_cong
  ArithR.case_cong
  ArithI.case_cong
  CGet.case_cong
  CSet.case_cong
  CCheck.case_cong
  CHERICOP2.case_cong
  COP2.case_cong
  CHERISWC2.case_cong
  SWC2.case_cong
  CHERILWC2.case_cong
  LWC2.case_cong
  CHERILDC2.case_cong
  LDC2.case_cong
  CHERISDC2.case_cong
  SDC2.case_cong
  instruction.case_cong    

subsection \<open>Strong congruence simplifier\<close>

text \<open>We remove \<open>if_splits\<close> from the split rules of the simplifier (to avoid an explosion of the
state). That means that some obvious simplifications are not done anymore, so we add these manually.
We do not like negations and disjunctions in our generated definitions, so we only add the following
lemmas to \<open>alt_def_simp\<close>.\<close>

lemma if_bool_simps2 [alt_def_simp]:
  shows "(if b then x else False) = (b \<and> x)"
    and "(if b then x else True) = (b \<longrightarrow> x)"
by simp_all

method strong_cong_simp uses add del = 
  (simp 
     add: add
     del: del
     split del: if_splits(1)
     cong del: weak_cong
     cong add: cong)

method strong_cong_simp_all uses add del = 
  (simp_all
     add: add
     del: del
     split del: if_splits(1)
     cong del: weak_cong
     cong add: cong)

subsection \<open>Simple version of @{method auto}\<close>

text \<open>In some rare cases @{method auto} gets stuck, but the proof is too difficult for @{method
simp}. The following method could help in that case: it invokes the simplifier and does some simple
elimination and introduction, but nothing fancy. Sometimes @{method auto} is quicker than this
method and sometimes the other way around. The proof method does not introduce any new
uninstantiated variables.\<close>

method simple_auto uses simp intro elim =
  (strong_cong_simp add: simp |
   elim conjE exE elim | 
   intro conjI impI allI intro);
  (simple_auto simp: simp intro: intro elim: elim)?

section \<open>Removing extend-state\<close>

subsection \<open>foreach-loop that returns a value\<close>

text \<open>The expression inside a @{term foreach_loop} cannot use the result of the previous
iteration. We define a new variant of the loop where this is possible.\<close>

fun foreach_loop_agg :: "'a list \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 's \<Rightarrow> 'b \<times> 's) \<Rightarrow>
                          's \<Rightarrow> 'b \<times> 's" where
  "foreach_loop_agg [] b _    = return b" |
  "foreach_loop_agg (h#t) b f = bind (f h b) (\<lambda>b. foreach_loop_agg t b f)"

lemma foreach_loop_agg_return [simp]:
  shows "foreach_loop_agg l b (\<lambda>a v. return (x a v)) = 
         return (fold x l b)"
by (induct l arbitrary: b) simp_all

lemma fold_id [simp]:
  shows "fold (\<lambda>_ v. v) l = (\<lambda>v. v)"
by (induct l) simp_all

lemma foreach_loop_agg_bind_return_constant [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>_. return b)) =
         bind (foreach_loop (l, (\<lambda>a. (f a b)))) (\<lambda>_. return b)"
by (induct l) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_bind_return_constant [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. bind (g a b c) (\<lambda>_. return b))) =
         bind (foreach_loop (l, (\<lambda>a. bind (f a b) (\<lambda>c. (g a b c) )))) (\<lambda>_. return b)"
by (induct l) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_bind_bind_return_constant [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. bind (g a b c) (\<lambda>d. bind (h a b c d) (\<lambda>_. return b)))) =
         bind (foreach_loop (l, (\<lambda>a. bind (f a b) (\<lambda>c. bind (g a b c) (\<lambda>d. h a b c d))))) (\<lambda>_. return b)"
by (induct l) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_return_left [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. return (fst b, x a b c))) =
         bind (foreach_loop_agg l (snd b) (\<lambda>a b2. 
                 bind (f a (fst b, b2)) (\<lambda>c. return (x a (fst b, b2) c))))
         (\<lambda>b2. return (fst b, b2))"
by (induct l arbitrary: b) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_return_right [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. return (x a b c, snd b))) =
         bind (foreach_loop_agg l (fst b) (\<lambda>a b2. 
                 bind (f a (b2, snd b)) (\<lambda>c. return (x a (b2, snd b) c))))
         (\<lambda>b2. return (b2, snd b))"
by (induct l arbitrary: b) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_bind_return_left [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. bind (g a b c) (\<lambda>d. return (fst b, x a b c d)))) =
         bind (foreach_loop_agg l (snd b) (\<lambda>a b2. 
                 bind (f a (fst b, b2)) (\<lambda>c. bind (g a (fst b, b2) c) (\<lambda>d. return (x a (fst b, b2) c d)))))
         (\<lambda>b2. return (fst b, b2))"
by (induct l arbitrary: b) (simp_all add: bind_associativity)

lemma foreach_loop_agg_bind_bind_return_right [simp]:
  shows "foreach_loop_agg l b (\<lambda>a b. bind (f a b) (\<lambda>c. bind (g a b c) (\<lambda>d. return (x a b c d, snd b)))) =
         bind (foreach_loop_agg l (fst b) (\<lambda>a b2. 
                 bind (f a (b2, snd b)) (\<lambda>c. bind (g a (b2, snd b) c) (\<lambda>d. return (x a (b2, snd b) c d)))))
         (\<lambda>b2. return (b2, snd b))"
by (induct l arbitrary: b) (simp_all add: bind_associativity)

lemma foreach_loop_agg_read_state [simp]:
  shows "foreach_loop_agg l b (\<lambda>a v. read_state (f a v)) = 
         read_state (\<lambda>s. fold (\<lambda>a v. f a v s) l b)"
proof (induct l arbitrary: b)
  case (Cons h t)
  hence "foreach_loop_agg (h # t) b (\<lambda>a v. read_state (f a v)) =
         bind (read_state (f h b)) (\<lambda>b. read_state (\<lambda>s. fold (\<lambda>a v. f a v s) t b))"
    by simp
  also have "... = read_state (\<lambda>s. fold (\<lambda>a v. f a v s) (h # t) b)"
    unfolding monad_def by simp
  finally show ?case .
qed simp

lemma foreach_loop_agg_bind_read_state_return [simp]:
  shows "foreach_loop_agg l b (\<lambda>a v. bind (read_state (f a v)) (\<lambda>b. return (x a v b))) = 
         read_state (\<lambda>s. fold (\<lambda>a v. x a v (f a v s)) l b)" (is "?l = ?r")
proof -
  have "bind (read_state (f a v)) (\<lambda>b. return (x a v b)) = read_state (\<lambda>s. x a v (f a v s))" for a v
    unfolding monad_def Let_def by simp
  hence "?l = foreach_loop_agg l b (\<lambda>a v. read_state (\<lambda>s. x a v (f a v s)))" by simp
  also have "... = read_state (\<lambda>s. fold (\<lambda>a v. x a v (f a v s)) l b)" by simp
  finally show ?thesis .
qed

lemma StatePart_foreach_loop_agg:
  assumes "\<And>a a' v v' s. ValuePart (m a v) (StatePart (m a' v') s) = ValuePart (m a v) s"
  shows "ValuePart (foreach_loop_agg l v m) = 
         (\<lambda>s. fold (\<lambda>a v. ValuePart (m a v) s) l v)"
using assms
by (induct l arbitrary: v)
   (auto simp add: ValuePart_bind)

subsection \<open>Extend state\<close>

text \<open>To simplify @{term extend_state} in the general case, we (temporarily) introduce two new
functions, namely @{term extend_before} and @{term extend_after}. Then we add rewrite rules that
eliminate those as well.\<close>

definition extend_before :: "'v \<Rightarrow> ('v \<times> 's \<Rightarrow> 'a \<times> 'v \<times> 's) \<Rightarrow> 's \<Rightarrow> ('a \<times> 'v) \<times> 's" where
  "extend_before v m = (\<lambda>s. let (a, s') = m (v, s) in ((a, fst s'), snd s'))"

definition extend_after :: "'v \<Rightarrow> ('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> 's \<Rightarrow> ('a \<times> 'v) \<times> 's" where
  "extend_after v m = bind m (\<lambda>a. return (a, v))" 

text \<open>We always expand the definition of @{term extend_after}; we only defined it to state the
simplifications of @{term extend_before} more elegantly. (In previous versions we did not always
expand the definition and ran into problems because the simplification rules were not confluent.\<close>

declare extend_after_def [alt_def_simp]

subsection \<open>Extend-state bind\<close>

lemma extend_state_bind [alt_def_simp]:
  shows "extend_state v (bind m n) = 
         bind (extend_before v m) (\<lambda>(a, v). extend_state v (n a))"    (is "?l = ?r")
proof (intro ext)
  fix s
  show "?l s = ?r s"
    unfolding extend_before_def monad_def
    by (cases "m (v, s)") auto
qed

lemma extend_before_bind [alt_def_simp]:
  shows "extend_before v (bind m n) = 
         bind (extend_before v m) (\<lambda>(a, v). extend_before v (n a))"    (is "?l = ?r")
proof (intro ext)
  fix s
  show "?l s = ?r s"
    unfolding extend_before_def monad_def
    by (cases "m (v, s)") auto
qed

subsection \<open>Extend-state return\<close>

text \<open>There already is a simplification in L3_Lib for @{term "extend_state v (return x)"}\<close>

lemma extend_before_return [alt_def_simp]:
  shows "extend_before v (return x) = extend_after v (return x)"
unfolding extend_before_def extend_after_def monad_def
by auto

subsection \<open>Extend-state read-state\<close>

lemma extend_state_read_state [alt_def_simp]:
  shows "extend_state v (read_state f) = read_state (\<lambda>s. f (v, s))"
unfolding monad_def
by simp

lemma extend_before_read_state [alt_def_simp]:
  shows "extend_before v (read_state f) = 
         extend_after v (read_state (\<lambda>s. f (v, s)))"
unfolding extend_before_def extend_after_def monad_def
by auto

subsection \<open>Extend-state update-state\<close>

lemma extend_state_update_state [alt_def_simp]:
  shows "extend_state v (update_state f) = update_state (\<lambda>s. snd (f (v, s)))"
unfolding monad_def
by simp

text \<open>The general case above for @{term "extend_before v (update_state f)"} is quite complicated,
and in the exported Isabelle/HOL only two variations appear, so we only add the specialised
lemmas to the simplification set.\<close>

lemma extend_before_update_state:
  shows "extend_before v (update_state f) = 
         bind (read_state (\<lambda>s. fst (f (v, s)))) 
              (\<lambda>v'. extend_after v' (update_state (\<lambda>s. snd (f (v, s))))) "
unfolding extend_before_def extend_after_def monad_def
by simp

lemma extend_before_update_state_1 [alt_def_simp]:
  shows "extend_before v (update_state (\<lambda>s. (fst s, f s))) = 
         extend_after v (update_state (\<lambda>s. f (v, s)))"
unfolding extend_before_update_state
by simp

lemma extend_before_update_state_2 [alt_def_simp]:
  shows "extend_before v (update_state (\<lambda>s. (x, snd s))) = 
         extend_after x (return ())"
unfolding extend_before_update_state
by simp

subsection \<open>Extend-state trim-state\<close>

text \<open>There already is a simplification in L3_Lib for @{term "extend_state v (trim_state m)"}.\<close>

lemma extend_before_trim_state [alt_def_simp]:
  shows "extend_before v (trim_state m) = extend_after v m"
        (is "?l = ?r")
proof
  fix s
  show "?l s = ?r s"
    unfolding extend_before_def extend_after_def monad_def
    by (cases "m s") auto
qed

subsection \<open>Extend-state foreach-loop\<close>

lemma extend_state_foreach_loop [alt_def_simp]:
  shows "extend_state v (foreach_loop (l, m)) = 
         bind (foreach_loop_agg l v (\<lambda>a v. bind (extend_before v (m a)) (\<lambda>(_, v). return v)))
              (\<lambda>_. return ())"
proof (induct l arbitrary: v)
  case Nil
  thus ?case 
    by simp
next
  case (Cons h t)
  thus ?case
    by (simp add: extend_state_bind case_prod_unfold bind_associativity)  
qed

lemma extend_before_foreach_loop [alt_def_simp]:
  shows "extend_before v (foreach_loop (l, m)) = 
         bind (foreach_loop_agg l v (\<lambda>a v. bind (extend_before v (m a)) (\<lambda>(_, v). return v)))
              (\<lambda>v. extend_after v (return ()))"
proof (induct l arbitrary: v)
  case Nil
  thus ?case 
    by (simp add: extend_before_return extend_after_def)
next
  case (Cons h t)
  thus ?case
    by (simp add: extend_before_bind case_prod_unfold bind_associativity)  
qed

subsection \<open>Extend-state foreach-loop-agg\<close>

lemma extend_state_foreach_loop_agg [alt_def_simp]:
  shows "extend_state v2 (foreach_loop_agg l v1 f) = 
         bind (foreach_loop_agg l (v1, v2) (\<lambda>a v. extend_before (snd v) (f a (fst v))))
              (\<lambda>v. return (fst v))"
proof (induct l arbitrary: v1 v2)
  case Nil
  thus ?case
    by simp
next
  case (Cons h t)
  thus ?case
    by (simp add: extend_state_bind case_prod_unfold bind_associativity)  
qed

lemma extend_before_foreach_loop_agg [alt_def_simp]:
  shows "extend_before v2 (foreach_loop_agg l v1 f) = 
         foreach_loop_agg l (v1, v2) (\<lambda>a v. extend_before (snd v) (f a (fst v)))"
proof (induct l arbitrary: v1 v2)
  case Nil
  thus ?case
    by (simp add: extend_before_return extend_after_def)
next
  case (Cons h t)
  thus ?case
    by (simp add: extend_before_bind case_prod_unfold)  
qed

subsection \<open>Extend-state distributive cases\<close>

lemmas extend_state_case [alt_def_simp] = 
  all_distrib[where h="extend_state _"]

lemmas extend_before_case [alt_def_simp] = 
  all_distrib[where h="extend_before _"]

section \<open>Contracting reads and updates\<close>

lemma bind_arg_cong:
  assumes "bind m n = k"
  shows "bind m (\<lambda>a. bind (n a) l) = bind k l"
using assms 
by (simp add: bind_associativity[THEN sym])

lemma contract_read:
  shows "bind (read_state getParent) (\<lambda>a. return (sub a)) = 
         read_state (\<lambda>s. sub (getParent s))" (is "?T1")
    and "bind (read_state getParent) (\<lambda>a. bind (return (sub a)) m) = 
         bind (read_state (\<lambda>s. sub (getParent s))) m" (is "?T2")
proof -
  show ?T1
    unfolding monad_def Let_def
    by simp
  from bind_arg_cong[OF this]
  show ?T2 .
qed

lemma contract_update:
  shows "bind (read_state getParent) 
              (\<lambda>v'. update_state (setParent (sub_update (\<lambda>_. f (sub v')) v'))) = 
         bind (read_state (\<lambda>s. sub (getParent s))) 
              (\<lambda>v. update_state (\<lambda>s. setParent (sub_update (\<lambda>_. f v) (getParent s)) s))" 
         (is "?T1")
    and "bind (read_state getParent) 
              (\<lambda>v'. bind (update_state (setParent (sub_update (\<lambda>_. f (sub v')) v'))) m) = 
         bind (read_state (\<lambda>s. sub (getParent s))) 
              (\<lambda>v. bind (update_state (\<lambda>s. setParent (sub_update (\<lambda>_. f v) (getParent s)) s)) m)" 
         (is "?T2")
proof -
  show ?T1
    unfolding monad_def Let_def
    by simp
  from bind_arg_cong[OF this]
  show ?T2 by (simp add: bind_associativity)
qed

lemma contract_update_constant:
  shows "bind (read_state getParent) 
              (\<lambda>v'. update_state (setParent (sub_update (\<lambda>_. x) v'))) = 
         update_state (\<lambda>s. setParent (sub_update (\<lambda>_. x) (getParent s)) s)" (is "?T1")
    and "bind (read_state getParent) 
              (\<lambda>v'. bind (update_state (setParent (sub_update (\<lambda>_. x) v'))) m) = 
         bind (update_state (\<lambda>s. setParent (sub_update (\<lambda>_. x) (getParent s)) s)) m" (is "?T2")
proof -
  show ?T1
    unfolding monad_def Let_def
    by simp
  from bind_arg_cong[OF this]
  show ?T2 .
qed

subsection \<open>Simplifying nested updates\<close>

(* Code generation - start - state component updates *)

lemma state_component_update_simps [simp]:
  shows "BranchDelayPCC_update (\<lambda>_. f_BranchDelayPCC (BranchDelayPCC s)) s = 
         BranchDelayPCC_update (f_BranchDelayPCC) s"
    and "BranchToPCC_update (\<lambda>_. f_BranchToPCC (BranchToPCC s)) s = 
         BranchToPCC_update (f_BranchToPCC) s"
    and "JTAG_UART_update (\<lambda>_. f_JTAG_UART (JTAG_UART s)) s = 
         JTAG_UART_update (f_JTAG_UART) s"
    and "PIC_base_address_update (\<lambda>_. f_PIC_base_address (PIC_base_address s)) s = 
         PIC_base_address_update (f_PIC_base_address) s"
    and "PIC_config_regs_update (\<lambda>_. f_PIC_config_regs (PIC_config_regs s)) s = 
         PIC_config_regs_update (f_PIC_config_regs) s"
    and "PIC_external_intrs_update (\<lambda>_. f_PIC_external_intrs (PIC_external_intrs s)) s = 
         PIC_external_intrs_update (f_PIC_external_intrs) s"
    and "PIC_ip_bits_update (\<lambda>_. f_PIC_ip_bits (PIC_ip_bits s)) s = 
         PIC_ip_bits_update (f_PIC_ip_bits) s"
    and "UNPREDICTABLE_HI_update (\<lambda>_. f_UNPREDICTABLE_HI (UNPREDICTABLE_HI s)) s = 
         UNPREDICTABLE_HI_update (f_UNPREDICTABLE_HI) s"
    and "UNPREDICTABLE_LO_update (\<lambda>_. f_UNPREDICTABLE_LO (UNPREDICTABLE_LO s)) s = 
         UNPREDICTABLE_LO_update (f_UNPREDICTABLE_LO) s"
    and "UNPREDICTABLE_TLB_update (\<lambda>_. f_UNPREDICTABLE_TLB (UNPREDICTABLE_TLB s)) s = 
         UNPREDICTABLE_TLB_update (f_UNPREDICTABLE_TLB) s"
    and "all_BranchDelayPCC_update (\<lambda>_. f_all_BranchDelayPCC (all_BranchDelayPCC s)) s = 
         all_BranchDelayPCC_update (f_all_BranchDelayPCC) s"
    and "all_BranchToPCC_update (\<lambda>_. f_all_BranchToPCC (all_BranchToPCC s)) s = 
         all_BranchToPCC_update (f_all_BranchToPCC) s"
    and "all_TLB_assoc_update (\<lambda>_. f_all_TLB_assoc (all_TLB_assoc s)) s = 
         all_TLB_assoc_update (f_all_TLB_assoc) s"
    and "all_TLB_direct_update (\<lambda>_. f_all_TLB_direct (all_TLB_direct s)) s = 
         all_TLB_direct_update (f_all_TLB_direct) s"
    and "all_capcause_update (\<lambda>_. f_all_capcause (all_capcause s)) s = 
         all_capcause_update (f_all_capcause) s"
    and "all_capr_update (\<lambda>_. f_all_capr (all_capr s)) s = 
         all_capr_update (f_all_capr) s"
    and "all_gpr_update (\<lambda>_. f_all_gpr (all_gpr s)) s = 
         all_gpr_update (f_all_gpr) s"
    and "all_pcc_update (\<lambda>_. f_all_pcc (all_pcc s)) s = 
         all_pcc_update (f_all_pcc) s"
    and "all_scapr_update (\<lambda>_. f_all_scapr (all_scapr s)) s = 
         all_scapr_update (f_all_scapr) s"
    and "all_state_update (\<lambda>_. f_all_state (all_state s)) s = 
         all_state_update (f_all_state) s"
    and "c_TLB_assoc_update (\<lambda>_. f_c_TLB_assoc (c_TLB_assoc s)) s = 
         c_TLB_assoc_update (f_c_TLB_assoc) s"
    and "c_TLB_direct_update (\<lambda>_. f_c_TLB_direct (c_TLB_direct s)) s = 
         c_TLB_direct_update (f_c_TLB_direct) s"
    and "c_capr_update (\<lambda>_. f_c_capr (c_capr s)) s = 
         c_capr_update (f_c_capr) s"
    and "c_gpr_update (\<lambda>_. f_c_gpr (c_gpr s)) s = 
         c_gpr_update (f_c_gpr) s"
    and "c_pcc_update (\<lambda>_. f_c_pcc (c_pcc s)) s = 
         c_pcc_update (f_c_pcc) s"
    and "c_scapr_update (\<lambda>_. f_c_scapr (c_scapr s)) s = 
         c_scapr_update (f_c_scapr) s"
    and "c_state_update (\<lambda>_. f_c_state (c_state s)) s = 
         c_state_update (f_c_state) s"
    and "c_state_update (c_BranchDelay_update (\<lambda>_. f_c_BranchDelay (c_BranchDelay (c_state s)))) s = 
         c_state_update (c_BranchDelay_update (f_c_BranchDelay)) s"
    and "c_state_update (c_BranchTo_update (\<lambda>_. f_c_BranchTo (c_BranchTo (c_state s)))) s = 
         c_state_update (c_BranchTo_update (f_c_BranchTo)) s"
    and "c_state_update (c_CP0_update (\<lambda>_. f_c_CP0 (c_CP0 (c_state s)))) s = 
         c_state_update (c_CP0_update (f_c_CP0)) s"
    and "c_state_update (c_CP0_update (BadInstr_update (\<lambda>_. f_BadInstr (BadInstr (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (BadInstr_update (f_BadInstr))) s"
    and "c_state_update (c_CP0_update (BadInstrP_update (\<lambda>_. f_BadInstrP (BadInstrP (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (BadInstrP_update (f_BadInstrP))) s"
    and "c_state_update (c_CP0_update (BadVAddr_update (\<lambda>_. f_BadVAddr (BadVAddr (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (BadVAddr_update (f_BadVAddr))) s"
    and "c_state_update (c_CP0_update (Cause_update (\<lambda>_. f_Cause (Cause (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Cause_update (f_Cause))) s"
    and "c_state_update (c_CP0_update (Cause_update (BD_update (\<lambda>_. f_BD (BD (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (BD_update (f_BD)))) s"
    and "c_state_update (c_CP0_update (Cause_update (CE_update (\<lambda>_. f_CE (CE (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (CE_update (f_CE)))) s"
    and "c_state_update (c_CP0_update (Cause_update (CauseRegister.ExcCode_update (\<lambda>_. f_CauseRegisterExcCode (CauseRegister.ExcCode (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (CauseRegister.ExcCode_update (f_CauseRegisterExcCode)))) s"
    and "c_state_update (c_CP0_update (Cause_update (IP_update (\<lambda>_. f_IP (IP (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (IP_update (f_IP)))) s"
    and "c_state_update (c_CP0_update (Cause_update (TI_update (\<lambda>_. f_TI (TI (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (TI_update (f_TI)))) s"
    and "c_state_update (c_CP0_update (Cause_update (causeregister'rst_update (\<lambda>_. f_causeregister'rst (causeregister'rst (Cause (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Cause_update (causeregister'rst_update (f_causeregister'rst)))) s"
    and "c_state_update (c_CP0_update (Compare_update (\<lambda>_. f_Compare (Compare (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Compare_update (f_Compare))) s"
    and "c_state_update (c_CP0_update (Config_update (\<lambda>_. f_Config (Config (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Config_update (f_Config))) s"
    and "c_state_update (c_CP0_update (Config_update (AR_update (\<lambda>_. f_AR (AR (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (AR_update (f_AR)))) s"
    and "c_state_update (c_CP0_update (Config_update (AT_update (\<lambda>_. f_AT (AT (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (AT_update (f_AT)))) s"
    and "c_state_update (c_CP0_update (Config_update (BE_update (\<lambda>_. f_BE (BE (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (BE_update (f_BE)))) s"
    and "c_state_update (c_CP0_update (Config_update (K0_update (\<lambda>_. f_K0 (K0 (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (K0_update (f_K0)))) s"
    and "c_state_update (c_CP0_update (Config_update (ConfigRegister.M_update (\<lambda>_. f_ConfigRegisterM (ConfigRegister.M (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (ConfigRegister.M_update (f_ConfigRegisterM)))) s"
    and "c_state_update (c_CP0_update (Config_update (ConfigRegister.MT_update (\<lambda>_. f_ConfigRegisterMT (ConfigRegister.MT (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (ConfigRegister.MT_update (f_ConfigRegisterMT)))) s"
    and "c_state_update (c_CP0_update (Config_update (configregister'rst_update (\<lambda>_. f_configregister'rst (configregister'rst (Config (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Config_update (configregister'rst_update (f_configregister'rst)))) s"
    and "c_state_update (c_CP0_update (Config1_update (\<lambda>_. f_Config1 (Config1 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Config1_update (f_Config1))) s"
    and "c_state_update (c_CP0_update (Config2_update (\<lambda>_. f_Config2 (Config2 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Config2_update (f_Config2))) s"
    and "c_state_update (c_CP0_update (Config3_update (\<lambda>_. f_Config3 (Config3 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Config3_update (f_Config3))) s"
    and "c_state_update (c_CP0_update (Config6_update (\<lambda>_. f_Config6 (Config6 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Config6_update (f_Config6))) s"
    and "c_state_update (c_CP0_update (Context_update (\<lambda>_. f_Context (Context (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Context_update (f_Context))) s"
    and "c_state_update (c_CP0_update (Context_update (Context.BadVPN2_update (\<lambda>_. f_ContextBadVPN2 (Context.BadVPN2 (Context (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Context_update (Context.BadVPN2_update (f_ContextBadVPN2)))) s"
    and "c_state_update (c_CP0_update (Context_update (Context.PTEBase_update (\<lambda>_. f_ContextPTEBase (Context.PTEBase (Context (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Context_update (Context.PTEBase_update (f_ContextPTEBase)))) s"
    and "c_state_update (c_CP0_update (Context_update (context'rst_update (\<lambda>_. f_context'rst (context'rst (Context (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Context_update (context'rst_update (f_context'rst)))) s"
    and "c_state_update (c_CP0_update (Count_update (\<lambda>_. f_Count (Count (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Count_update (f_Count))) s"
    and "c_state_update (c_CP0_update (Debug_update (\<lambda>_. f_Debug (Debug (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Debug_update (f_Debug))) s"
    and "c_state_update (c_CP0_update (EPC_update (\<lambda>_. f_EPC (EPC (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (EPC_update (f_EPC))) s"
    and "c_state_update (c_CP0_update (EntryHi_update (\<lambda>_. f_EntryHi (EntryHi (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (EntryHi_update (f_EntryHi))) s"
    and "c_state_update (c_CP0_update (EntryHi_update (EntryHi.ASID_update (\<lambda>_. f_EntryHiASID (EntryHi.ASID (EntryHi (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (EntryHi_update (EntryHi.ASID_update (f_EntryHiASID)))) s"
    and "c_state_update (c_CP0_update (EntryHi_update (EntryHi.R_update (\<lambda>_. f_EntryHiR (EntryHi.R (EntryHi (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (EntryHi_update (EntryHi.R_update (f_EntryHiR)))) s"
    and "c_state_update (c_CP0_update (EntryHi_update (EntryHi.VPN2_update (\<lambda>_. f_EntryHiVPN2 (EntryHi.VPN2 (EntryHi (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (EntryHi_update (EntryHi.VPN2_update (f_EntryHiVPN2)))) s"
    and "c_state_update (c_CP0_update (EntryHi_update (entryhi'rst_update (\<lambda>_. f_entryhi'rst (entryhi'rst (EntryHi (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (EntryHi_update (entryhi'rst_update (f_entryhi'rst)))) s"
    and "c_state_update (c_CP0_update (EntryLo0_update (\<lambda>_. f_EntryLo0 (EntryLo0 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (EntryLo0_update (f_EntryLo0))) s"
    and "c_state_update (c_CP0_update (EntryLo1_update (\<lambda>_. f_EntryLo1 (EntryLo1 (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (EntryLo1_update (f_EntryLo1))) s"
    and "c_state_update (c_CP0_update (ErrCtl_update (\<lambda>_. f_ErrCtl (ErrCtl (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (ErrCtl_update (f_ErrCtl))) s"
    and "c_state_update (c_CP0_update (ErrorEPC_update (\<lambda>_. f_ErrorEPC (ErrorEPC (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (ErrorEPC_update (f_ErrorEPC))) s"
    and "c_state_update (c_CP0_update (HWREna_update (\<lambda>_. f_HWREna (HWREna (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (HWREna_update (f_HWREna))) s"
    and "c_state_update (c_CP0_update (Index_update (\<lambda>_. f_Index (Index (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Index_update (f_Index))) s"
    and "c_state_update (c_CP0_update (LLAddr_update (\<lambda>_. f_LLAddr (LLAddr (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (LLAddr_update (f_LLAddr))) s"
    and "c_state_update (c_CP0_update (PRId_update (\<lambda>_. f_PRId (PRId (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (PRId_update (f_PRId))) s"
    and "c_state_update (c_CP0_update (PageMask_update (\<lambda>_. f_PageMask (PageMask (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (PageMask_update (f_PageMask))) s"
    and "c_state_update (c_CP0_update (Random_update (\<lambda>_. f_Random (Random (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Random_update (f_Random))) s"
    and "c_state_update (c_CP0_update (Random_update (Random.Random_update (\<lambda>_. f_RandomRandom (Random.Random (Random (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Random_update (Random.Random_update (f_RandomRandom)))) s"
    and "c_state_update (c_CP0_update (Random_update (random'rst_update (\<lambda>_. f_random'rst (random'rst (Random (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Random_update (random'rst_update (f_random'rst)))) s"
    and "c_state_update (c_CP0_update (Status_update (\<lambda>_. f_Status (Status (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Status_update (f_Status))) s"
    and "c_state_update (c_CP0_update (Status_update (BEV_update (\<lambda>_. f_BEV (BEV (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (BEV_update (f_BEV)))) s"
    and "c_state_update (c_CP0_update (Status_update (CU0_update (\<lambda>_. f_CU0 (CU0 (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (CU0_update (f_CU0)))) s"
    and "c_state_update (c_CP0_update (Status_update (CU1_update (\<lambda>_. f_CU1 (CU1 (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (CU1_update (f_CU1)))) s"
    and "c_state_update (c_CP0_update (Status_update (CU2_update (\<lambda>_. f_CU2 (CU2 (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (CU2_update (f_CU2)))) s"
    and "c_state_update (c_CP0_update (Status_update (CU3_update (\<lambda>_. f_CU3 (CU3 (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (CU3_update (f_CU3)))) s"
    and "c_state_update (c_CP0_update (Status_update (ERL_update (\<lambda>_. f_ERL (ERL (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (ERL_update (f_ERL)))) s"
    and "c_state_update (c_CP0_update (Status_update (EXL_update (\<lambda>_. f_EXL (EXL (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (EXL_update (f_EXL)))) s"
    and "c_state_update (c_CP0_update (Status_update (FR_update (\<lambda>_. f_FR (FR (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (FR_update (f_FR)))) s"
    and "c_state_update (c_CP0_update (Status_update (IE_update (\<lambda>_. f_IE (IE (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (IE_update (f_IE)))) s"
    and "c_state_update (c_CP0_update (Status_update (IM_update (\<lambda>_. f_IM (IM (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (IM_update (f_IM)))) s"
    and "c_state_update (c_CP0_update (Status_update (KSU_update (\<lambda>_. f_KSU (KSU (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (KSU_update (f_KSU)))) s"
    and "c_state_update (c_CP0_update (Status_update (KX_update (\<lambda>_. f_KX (KX (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (KX_update (f_KX)))) s"
    and "c_state_update (c_CP0_update (Status_update (StatusRegister.RE_update (\<lambda>_. f_StatusRegisterRE (StatusRegister.RE (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (StatusRegister.RE_update (f_StatusRegisterRE)))) s"
    and "c_state_update (c_CP0_update (Status_update (SX_update (\<lambda>_. f_SX (SX (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (SX_update (f_SX)))) s"
    and "c_state_update (c_CP0_update (Status_update (UX_update (\<lambda>_. f_UX (UX (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (UX_update (f_UX)))) s"
    and "c_state_update (c_CP0_update (Status_update (statusregister'rst_update (\<lambda>_. f_statusregister'rst (statusregister'rst (Status (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Status_update (statusregister'rst_update (f_statusregister'rst)))) s"
    and "c_state_update (c_CP0_update (UsrLocal_update (\<lambda>_. f_UsrLocal (UsrLocal (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (UsrLocal_update (f_UsrLocal))) s"
    and "c_state_update (c_CP0_update (Wired_update (\<lambda>_. f_Wired (Wired (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (Wired_update (f_Wired))) s"
    and "c_state_update (c_CP0_update (Wired_update (Wired.Wired_update (\<lambda>_. f_WiredWired (Wired.Wired (Wired (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Wired_update (Wired.Wired_update (f_WiredWired)))) s"
    and "c_state_update (c_CP0_update (Wired_update (wired'rst_update (\<lambda>_. f_wired'rst (wired'rst (Wired (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (Wired_update (wired'rst_update (f_wired'rst)))) s"
    and "c_state_update (c_CP0_update (XContext_update (\<lambda>_. f_XContext (XContext (c_CP0 (c_state s)))))) s = 
         c_state_update (c_CP0_update (XContext_update (f_XContext))) s"
    and "c_state_update (c_CP0_update (XContext_update (XContext.BadVPN2_update (\<lambda>_. f_XContextBadVPN2 (XContext.BadVPN2 (XContext (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (XContext_update (XContext.BadVPN2_update (f_XContextBadVPN2)))) s"
    and "c_state_update (c_CP0_update (XContext_update (XContext.PTEBase_update (\<lambda>_. f_XContextPTEBase (XContext.PTEBase (XContext (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (XContext_update (XContext.PTEBase_update (f_XContextPTEBase)))) s"
    and "c_state_update (c_CP0_update (XContext_update (XContext.R_update (\<lambda>_. f_XContextR (XContext.R (XContext (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (XContext_update (XContext.R_update (f_XContextR)))) s"
    and "c_state_update (c_CP0_update (XContext_update (xcontext'rst_update (\<lambda>_. f_xcontext'rst (xcontext'rst (XContext (c_CP0 (c_state s)))))))) s = 
         c_state_update (c_CP0_update (XContext_update (xcontext'rst_update (f_xcontext'rst)))) s"
    and "c_state_update (c_CoreStats_update (\<lambda>_. f_c_CoreStats (c_CoreStats (c_state s)))) s = 
         c_state_update (c_CoreStats_update (f_c_CoreStats)) s"
    and "c_state_update (c_CoreStats_update (branch_not_taken_update (\<lambda>_. f_branch_not_taken (branch_not_taken (c_CoreStats (c_state s)))))) s = 
         c_state_update (c_CoreStats_update (branch_not_taken_update (f_branch_not_taken))) s"
    and "c_state_update (c_CoreStats_update (branch_taken_update (\<lambda>_. f_branch_taken (branch_taken (c_CoreStats (c_state s)))))) s = 
         c_state_update (c_CoreStats_update (branch_taken_update (f_branch_taken))) s"
    and "c_state_update (c_LLbit_update (\<lambda>_. f_c_LLbit (c_LLbit (c_state s)))) s = 
         c_state_update (c_LLbit_update (f_c_LLbit)) s"
    and "c_state_update (c_PC_update (\<lambda>_. f_c_PC (c_PC (c_state s)))) s = 
         c_state_update (c_PC_update (f_c_PC)) s"
    and "c_state_update (c_exceptionSignalled_update (\<lambda>_. f_c_exceptionSignalled (c_exceptionSignalled (c_state s)))) s = 
         c_state_update (c_exceptionSignalled_update (f_c_exceptionSignalled)) s"
    and "c_state_update (c_hi_update (\<lambda>_. f_c_hi (c_hi (c_state s)))) s = 
         c_state_update (c_hi_update (f_c_hi)) s"
    and "c_state_update (c_lo_update (\<lambda>_. f_c_lo (c_lo (c_state s)))) s = 
         c_state_update (c_lo_update (f_c_lo)) s"
    and "capcause_update (\<lambda>_. f_capcause (capcause s)) s = 
         capcause_update (f_capcause) s"
    and "csv_stats_header_done_update (\<lambda>_. f_csv_stats_header_done (csv_stats_header_done s)) s = 
         csv_stats_header_done_update (f_csv_stats_header_done) s"
    and "currentInst_update (\<lambda>_. f_currentInst (currentInst s)) s = 
         currentInst_update (f_currentInst) s"
    and "done_update (\<lambda>_. f_done (done s)) s = 
         done_update (f_done) s"
    and "dynamicMemStats_update (\<lambda>_. f_dynamicMemStats (dynamicMemStats s)) s = 
         dynamicMemStats_update (f_dynamicMemStats) s"
    and "dynamic_shadow_16K_TAGS_update (\<lambda>_. f_dynamic_shadow_16K_TAGS (dynamic_shadow_16K_TAGS s)) s = 
         dynamic_shadow_16K_TAGS_update (f_dynamic_shadow_16K_TAGS) s"
    and "dynamic_shadow_4K_MEM_update (\<lambda>_. f_dynamic_shadow_4K_MEM (dynamic_shadow_4K_MEM s)) s = 
         dynamic_shadow_4K_MEM_update (f_dynamic_shadow_4K_MEM) s"
    and "dynamic_shadow_4K_TAGS_update (\<lambda>_. f_dynamic_shadow_4K_TAGS (dynamic_shadow_4K_TAGS s)) s = 
         dynamic_shadow_4K_TAGS_update (f_dynamic_shadow_4K_TAGS) s"
    and "dynamic_shadow_MEM_update (\<lambda>_. f_dynamic_shadow_MEM (dynamic_shadow_MEM s)) s = 
         dynamic_shadow_MEM_update (f_dynamic_shadow_MEM) s"
    and "dynamic_shadow_TAGS_update (\<lambda>_. f_dynamic_shadow_TAGS (dynamic_shadow_TAGS s)) s = 
         dynamic_shadow_TAGS_update (f_dynamic_shadow_TAGS) s"
    and "exception_update (\<lambda>_. f_exception (exception s)) s = 
         exception_update (f_exception) s"
    and "hasCP1_update (\<lambda>_. f_hasCP1 (hasCP1 s)) s = 
         hasCP1_update (f_hasCP1) s"
    and "hasCP2_update (\<lambda>_. f_hasCP2 (hasCP2 s)) s = 
         hasCP2_update (f_hasCP2) s"
    and "instCnt_update (\<lambda>_. f_instCnt (instCnt s)) s = 
         instCnt_update (f_instCnt) s"
    and "lastInst_update (\<lambda>_. f_lastInst (lastInst s)) s = 
         lastInst_update (f_lastInst) s"
    and "log_update (\<lambda>_. f_log (log s)) s = 
         log_update (f_log) s"
    and "memAccessStats_update (\<lambda>_. f_memAccessStats (memAccessStats s)) s = 
         memAccessStats_update (f_memAccessStats) s"
    and "print_update (\<lambda>_. f_print (print s)) s = 
         print_update (f_print) s"
    and "procID_update (\<lambda>_. f_procID (procID s)) s = 
         procID_update (f_procID) s"
    and "staticMemStats_update (\<lambda>_. f_staticMemStats (staticMemStats s)) s = 
         staticMemStats_update (f_staticMemStats) s"
    and "static_shadow_16K_TAGS_update (\<lambda>_. f_static_shadow_16K_TAGS (static_shadow_16K_TAGS s)) s = 
         static_shadow_16K_TAGS_update (f_static_shadow_16K_TAGS) s"
    and "static_shadow_4K_MEM_update (\<lambda>_. f_static_shadow_4K_MEM (static_shadow_4K_MEM s)) s = 
         static_shadow_4K_MEM_update (f_static_shadow_4K_MEM) s"
    and "static_shadow_4K_TAGS_update (\<lambda>_. f_static_shadow_4K_TAGS (static_shadow_4K_TAGS s)) s = 
         static_shadow_4K_TAGS_update (f_static_shadow_4K_TAGS) s"
    and "static_shadow_MEM_update (\<lambda>_. f_static_shadow_MEM (static_shadow_MEM s)) s = 
         static_shadow_MEM_update (f_static_shadow_MEM) s"
    and "static_shadow_TAGS_update (\<lambda>_. f_static_shadow_TAGS (static_shadow_TAGS s)) s = 
         static_shadow_TAGS_update (f_static_shadow_TAGS) s"
    and "the_MEM_update (\<lambda>_. f_the_MEM (the_MEM s)) s = 
         the_MEM_update (f_the_MEM) s"
    and "totalCore_update (\<lambda>_. f_totalCore (totalCore s)) s = 
         totalCore_update (f_totalCore) s"
    and "trace_level_update (\<lambda>_. f_trace_level (trace_level s)) s = 
         trace_level_update (f_trace_level) s"
    and "unknown_counters_update (\<lambda>_. f_unknown_counters (unknown_counters s)) s = 
         unknown_counters_update (f_unknown_counters) s"
    and "watchOOBCap_update (\<lambda>_. f_watchOOBCap (watchOOBCap s)) s = 
         watchOOBCap_update (f_watchOOBCap) s"
    and "watchPaddr_update (\<lambda>_. f_watchPaddr (watchPaddr s)) s = 
         watchPaddr_update (f_watchPaddr) s"
    and "watcher_update (\<lambda>_. f_watcher (watcher s)) s = 
         watcher_update (f_watcher) s"
by simp_all

(* Code generation - end *)

(* Code generation - start - contracting reads and updates *)

subsection \<open>@{const c_BranchDelay}\<close>

abbreviation getBranchDelay where
  "getBranchDelay \<equiv> (\<lambda>s. c_BranchDelay (c_state s))"

lemma BranchDelay_alt [alt_def_simp]:
  shows "BranchDelay = read_state getBranchDelay"
unfolding BranchDelay_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_BranchDelay [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_BranchDelay]

abbreviation setBranchDelay where
  "setBranchDelay v \<equiv> c_state_update (c_BranchDelay_update (\<lambda>_. v))"

lemma write'BranchDelay_alt [alt_def_simp]:
  shows "write'BranchDelay = (\<lambda>v. update_state (setBranchDelay v))"
unfolding write'BranchDelay_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_BranchDelay [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_BranchDelay_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_BranchDelay
                    and sub_update=c_BranchDelay_update]

subsection \<open>@{const c_BranchTo}\<close>

abbreviation getBranchTo where
  "getBranchTo \<equiv> (\<lambda>s. c_BranchTo (c_state s))"

lemma BranchTo_alt [alt_def_simp]:
  shows "BranchTo = read_state getBranchTo"
unfolding BranchTo_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_BranchTo [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_BranchTo]

abbreviation setBranchTo where
  "setBranchTo v \<equiv> c_state_update (c_BranchTo_update (\<lambda>_. v))"

lemma write'BranchTo_alt [alt_def_simp]:
  shows "write'BranchTo = (\<lambda>v. update_state (setBranchTo v))"
unfolding write'BranchTo_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_BranchTo [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_BranchTo_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_BranchTo
                    and sub_update=c_BranchTo_update]

subsection \<open>@{const c_CP0}\<close>

abbreviation getCP0 where
  "getCP0 \<equiv> (\<lambda>s. c_CP0 (c_state s))"

lemma CP0_alt [alt_def_simp]:
  shows "CP0 = read_state getCP0"
unfolding CP0_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_CP0 [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_CP0]

abbreviation setCP0 where
  "setCP0 v \<equiv> c_state_update (c_CP0_update (\<lambda>_. v))"

lemma write'CP0_alt [alt_def_simp]:
  shows "write'CP0 = (\<lambda>v. update_state (setCP0 v))"
unfolding write'CP0_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_CP0 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_CP0_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_CP0
                    and sub_update=c_CP0_update]

subsection \<open>@{const BadInstr}\<close>

abbreviation getCP0BadInstr where
  "getCP0BadInstr \<equiv> (\<lambda>s. BadInstr (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0BadInstr [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=BadInstr]

abbreviation setCP0BadInstr where
  "setCP0BadInstr v \<equiv> c_state_update (c_CP0_update (BadInstr_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0BadInstr [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=BadInstr_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=BadInstr
                    and sub_update=BadInstr_update]

subsection \<open>@{const BadInstrP}\<close>

abbreviation getCP0BadInstrP where
  "getCP0BadInstrP \<equiv> (\<lambda>s. BadInstrP (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0BadInstrP [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=BadInstrP]

abbreviation setCP0BadInstrP where
  "setCP0BadInstrP v \<equiv> c_state_update (c_CP0_update (BadInstrP_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0BadInstrP [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=BadInstrP_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=BadInstrP
                    and sub_update=BadInstrP_update]

subsection \<open>@{const BadVAddr}\<close>

abbreviation getCP0BadVAddr where
  "getCP0BadVAddr \<equiv> (\<lambda>s. BadVAddr (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0BadVAddr [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=BadVAddr]

abbreviation setCP0BadVAddr where
  "setCP0BadVAddr v \<equiv> c_state_update (c_CP0_update (BadVAddr_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0BadVAddr [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=BadVAddr_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=BadVAddr
                    and sub_update=BadVAddr_update]

subsection \<open>@{const Cause}\<close>

abbreviation getCP0Cause where
  "getCP0Cause \<equiv> (\<lambda>s. Cause (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Cause [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Cause]

abbreviation setCP0Cause where
  "setCP0Cause v \<equiv> c_state_update (c_CP0_update (Cause_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Cause [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Cause_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Cause
                    and sub_update=Cause_update]

subsection \<open>@{const BD}\<close>

abbreviation getCP0CauseBD where
  "getCP0CauseBD \<equiv> (\<lambda>s. BD (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseBD [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=BD]

abbreviation setCP0CauseBD where
  "setCP0CauseBD v \<equiv> c_state_update (c_CP0_update (Cause_update (BD_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseBD [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=BD_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=BD
                    and sub_update=BD_update]

subsection \<open>@{const CE}\<close>

abbreviation getCP0CauseCE where
  "getCP0CauseCE \<equiv> (\<lambda>s. CE (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseCE [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=CE]

abbreviation setCP0CauseCE where
  "setCP0CauseCE v \<equiv> c_state_update (c_CP0_update (Cause_update (CE_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseCE [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=CE_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=CE
                    and sub_update=CE_update]

subsection \<open>@{const CauseRegister.ExcCode}\<close>

abbreviation getCP0CauseExcCode where
  "getCP0CauseExcCode \<equiv> (\<lambda>s. CauseRegister.ExcCode (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseExcCode [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=CauseRegister.ExcCode]

abbreviation setCP0CauseExcCode where
  "setCP0CauseExcCode v \<equiv> c_state_update (c_CP0_update (Cause_update (CauseRegister.ExcCode_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseExcCode [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=CauseRegister.ExcCode_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=CauseRegister.ExcCode
                    and sub_update=CauseRegister.ExcCode_update]

subsection \<open>@{const IP}\<close>

abbreviation getCP0CauseIP where
  "getCP0CauseIP \<equiv> (\<lambda>s. IP (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseIP [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=IP]

abbreviation setCP0CauseIP where
  "setCP0CauseIP v \<equiv> c_state_update (c_CP0_update (Cause_update (IP_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseIP [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=IP_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=IP
                    and sub_update=IP_update]

subsection \<open>@{const TI}\<close>

abbreviation getCP0CauseTI where
  "getCP0CauseTI \<equiv> (\<lambda>s. TI (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseTI [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=TI]

abbreviation setCP0CauseTI where
  "setCP0CauseTI v \<equiv> c_state_update (c_CP0_update (Cause_update (TI_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseTI [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=TI_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=TI
                    and sub_update=TI_update]

subsection \<open>@{const causeregister'rst}\<close>

abbreviation getCP0CauseCauseregister'rst where
  "getCP0CauseCauseregister'rst \<equiv> (\<lambda>s. causeregister'rst (Cause (c_CP0 (c_state s))))"

lemmas contract_getCP0Cause_CP0CauseCauseregister'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Cause and sub=causeregister'rst]

abbreviation setCP0CauseCauseregister'rst where
  "setCP0CauseCauseregister'rst v \<equiv> c_state_update (c_CP0_update (Cause_update (causeregister'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0CauseCauseregister'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Cause
                           and setParent=setCP0Cause
                           and sub_update=causeregister'rst_update]
  contract_update[where getParent=getCP0Cause 
                    and setParent=setCP0Cause
                    and sub=causeregister'rst
                    and sub_update=causeregister'rst_update]

subsection \<open>@{const Compare}\<close>

abbreviation getCP0Compare where
  "getCP0Compare \<equiv> (\<lambda>s. Compare (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Compare [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Compare]

abbreviation setCP0Compare where
  "setCP0Compare v \<equiv> c_state_update (c_CP0_update (Compare_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Compare [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Compare_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Compare
                    and sub_update=Compare_update]

subsection \<open>@{const Config}\<close>

abbreviation getCP0Config where
  "getCP0Config \<equiv> (\<lambda>s. Config (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Config [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Config]

abbreviation setCP0Config where
  "setCP0Config v \<equiv> c_state_update (c_CP0_update (Config_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Config [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Config_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Config
                    and sub_update=Config_update]

subsection \<open>@{const AR}\<close>

abbreviation getCP0ConfigAR where
  "getCP0ConfigAR \<equiv> (\<lambda>s. AR (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigAR [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=AR]

abbreviation setCP0ConfigAR where
  "setCP0ConfigAR v \<equiv> c_state_update (c_CP0_update (Config_update (AR_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigAR [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=AR_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=AR
                    and sub_update=AR_update]

subsection \<open>@{const AT}\<close>

abbreviation getCP0ConfigAT where
  "getCP0ConfigAT \<equiv> (\<lambda>s. AT (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigAT [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=AT]

abbreviation setCP0ConfigAT where
  "setCP0ConfigAT v \<equiv> c_state_update (c_CP0_update (Config_update (AT_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigAT [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=AT_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=AT
                    and sub_update=AT_update]

subsection \<open>@{const BE}\<close>

abbreviation getCP0ConfigBE where
  "getCP0ConfigBE \<equiv> (\<lambda>s. BE (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigBE [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=BE]

abbreviation setCP0ConfigBE where
  "setCP0ConfigBE v \<equiv> c_state_update (c_CP0_update (Config_update (BE_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigBE [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=BE_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=BE
                    and sub_update=BE_update]

subsection \<open>@{const K0}\<close>

abbreviation getCP0ConfigK0 where
  "getCP0ConfigK0 \<equiv> (\<lambda>s. K0 (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigK0 [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=K0]

abbreviation setCP0ConfigK0 where
  "setCP0ConfigK0 v \<equiv> c_state_update (c_CP0_update (Config_update (K0_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigK0 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=K0_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=K0
                    and sub_update=K0_update]

subsection \<open>@{const ConfigRegister.M}\<close>

abbreviation getCP0ConfigM where
  "getCP0ConfigM \<equiv> (\<lambda>s. ConfigRegister.M (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigM [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=ConfigRegister.M]

abbreviation setCP0ConfigM where
  "setCP0ConfigM v \<equiv> c_state_update (c_CP0_update (Config_update (ConfigRegister.M_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigM [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=ConfigRegister.M_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=ConfigRegister.M
                    and sub_update=ConfigRegister.M_update]

subsection \<open>@{const ConfigRegister.MT}\<close>

abbreviation getCP0ConfigMT where
  "getCP0ConfigMT \<equiv> (\<lambda>s. ConfigRegister.MT (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigMT [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=ConfigRegister.MT]

abbreviation setCP0ConfigMT where
  "setCP0ConfigMT v \<equiv> c_state_update (c_CP0_update (Config_update (ConfigRegister.MT_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigMT [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=ConfigRegister.MT_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=ConfigRegister.MT
                    and sub_update=ConfigRegister.MT_update]

subsection \<open>@{const configregister'rst}\<close>

abbreviation getCP0ConfigConfigregister'rst where
  "getCP0ConfigConfigregister'rst \<equiv> (\<lambda>s. configregister'rst (Config (c_CP0 (c_state s))))"

lemmas contract_getCP0Config_CP0ConfigConfigregister'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Config and sub=configregister'rst]

abbreviation setCP0ConfigConfigregister'rst where
  "setCP0ConfigConfigregister'rst v \<equiv> c_state_update (c_CP0_update (Config_update (configregister'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ConfigConfigregister'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Config
                           and setParent=setCP0Config
                           and sub_update=configregister'rst_update]
  contract_update[where getParent=getCP0Config 
                    and setParent=setCP0Config
                    and sub=configregister'rst
                    and sub_update=configregister'rst_update]

subsection \<open>@{const Config1}\<close>

abbreviation getCP0Config1 where
  "getCP0Config1 \<equiv> (\<lambda>s. Config1 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Config1 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Config1]

abbreviation setCP0Config1 where
  "setCP0Config1 v \<equiv> c_state_update (c_CP0_update (Config1_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Config1 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Config1_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Config1
                    and sub_update=Config1_update]

subsection \<open>@{const Config2}\<close>

abbreviation getCP0Config2 where
  "getCP0Config2 \<equiv> (\<lambda>s. Config2 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Config2 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Config2]

abbreviation setCP0Config2 where
  "setCP0Config2 v \<equiv> c_state_update (c_CP0_update (Config2_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Config2 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Config2_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Config2
                    and sub_update=Config2_update]

subsection \<open>@{const Config3}\<close>

abbreviation getCP0Config3 where
  "getCP0Config3 \<equiv> (\<lambda>s. Config3 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Config3 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Config3]

abbreviation setCP0Config3 where
  "setCP0Config3 v \<equiv> c_state_update (c_CP0_update (Config3_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Config3 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Config3_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Config3
                    and sub_update=Config3_update]

subsection \<open>@{const Config6}\<close>

abbreviation getCP0Config6 where
  "getCP0Config6 \<equiv> (\<lambda>s. Config6 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Config6 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Config6]

abbreviation setCP0Config6 where
  "setCP0Config6 v \<equiv> c_state_update (c_CP0_update (Config6_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Config6 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Config6_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Config6
                    and sub_update=Config6_update]

subsection \<open>@{const Context}\<close>

abbreviation getCP0Context where
  "getCP0Context \<equiv> (\<lambda>s. Context (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Context [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Context]

abbreviation setCP0Context where
  "setCP0Context v \<equiv> c_state_update (c_CP0_update (Context_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Context [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Context_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Context
                    and sub_update=Context_update]

subsection \<open>@{const Context.BadVPN2}\<close>

abbreviation getCP0ContextBadVPN2 where
  "getCP0ContextBadVPN2 \<equiv> (\<lambda>s. Context.BadVPN2 (Context (c_CP0 (c_state s))))"

lemmas contract_getCP0Context_CP0ContextBadVPN2 [alt_def_simp] = 
  contract_read[where getParent=getCP0Context and sub=Context.BadVPN2]

abbreviation setCP0ContextBadVPN2 where
  "setCP0ContextBadVPN2 v \<equiv> c_state_update (c_CP0_update (Context_update (Context.BadVPN2_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ContextBadVPN2 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Context
                           and setParent=setCP0Context
                           and sub_update=Context.BadVPN2_update]
  contract_update[where getParent=getCP0Context 
                    and setParent=setCP0Context
                    and sub=Context.BadVPN2
                    and sub_update=Context.BadVPN2_update]

subsection \<open>@{const Context.PTEBase}\<close>

abbreviation getCP0ContextPTEBase where
  "getCP0ContextPTEBase \<equiv> (\<lambda>s. Context.PTEBase (Context (c_CP0 (c_state s))))"

lemmas contract_getCP0Context_CP0ContextPTEBase [alt_def_simp] = 
  contract_read[where getParent=getCP0Context and sub=Context.PTEBase]

abbreviation setCP0ContextPTEBase where
  "setCP0ContextPTEBase v \<equiv> c_state_update (c_CP0_update (Context_update (Context.PTEBase_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ContextPTEBase [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Context
                           and setParent=setCP0Context
                           and sub_update=Context.PTEBase_update]
  contract_update[where getParent=getCP0Context 
                    and setParent=setCP0Context
                    and sub=Context.PTEBase
                    and sub_update=Context.PTEBase_update]

subsection \<open>@{const context'rst}\<close>

abbreviation getCP0ContextContext'rst where
  "getCP0ContextContext'rst \<equiv> (\<lambda>s. context'rst (Context (c_CP0 (c_state s))))"

lemmas contract_getCP0Context_CP0ContextContext'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Context and sub=context'rst]

abbreviation setCP0ContextContext'rst where
  "setCP0ContextContext'rst v \<equiv> c_state_update (c_CP0_update (Context_update (context'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0ContextContext'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Context
                           and setParent=setCP0Context
                           and sub_update=context'rst_update]
  contract_update[where getParent=getCP0Context 
                    and setParent=setCP0Context
                    and sub=context'rst
                    and sub_update=context'rst_update]

subsection \<open>@{const Count}\<close>

abbreviation getCP0Count where
  "getCP0Count \<equiv> (\<lambda>s. Count (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Count [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Count]

abbreviation setCP0Count where
  "setCP0Count v \<equiv> c_state_update (c_CP0_update (Count_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Count [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Count_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Count
                    and sub_update=Count_update]

subsection \<open>@{const Debug}\<close>

abbreviation getCP0Debug where
  "getCP0Debug \<equiv> (\<lambda>s. Debug (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Debug [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Debug]

abbreviation setCP0Debug where
  "setCP0Debug v \<equiv> c_state_update (c_CP0_update (Debug_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Debug [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Debug_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Debug
                    and sub_update=Debug_update]

subsection \<open>@{const EPC}\<close>

abbreviation getCP0EPC where
  "getCP0EPC \<equiv> (\<lambda>s. EPC (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0EPC [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=EPC]

abbreviation setCP0EPC where
  "setCP0EPC v \<equiv> c_state_update (c_CP0_update (EPC_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0EPC [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=EPC_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=EPC
                    and sub_update=EPC_update]

subsection \<open>@{const EntryHi}\<close>

abbreviation getCP0EntryHi where
  "getCP0EntryHi \<equiv> (\<lambda>s. EntryHi (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0EntryHi [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=EntryHi]

abbreviation setCP0EntryHi where
  "setCP0EntryHi v \<equiv> c_state_update (c_CP0_update (EntryHi_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0EntryHi [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=EntryHi_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=EntryHi
                    and sub_update=EntryHi_update]

subsection \<open>@{const EntryHi.ASID}\<close>

abbreviation getCP0EntryHiASID where
  "getCP0EntryHiASID \<equiv> (\<lambda>s. EntryHi.ASID (EntryHi (c_CP0 (c_state s))))"

lemmas contract_getCP0EntryHi_CP0EntryHiASID [alt_def_simp] = 
  contract_read[where getParent=getCP0EntryHi and sub=EntryHi.ASID]

abbreviation setCP0EntryHiASID where
  "setCP0EntryHiASID v \<equiv> c_state_update (c_CP0_update (EntryHi_update (EntryHi.ASID_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0EntryHiASID [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0EntryHi
                           and setParent=setCP0EntryHi
                           and sub_update=EntryHi.ASID_update]
  contract_update[where getParent=getCP0EntryHi 
                    and setParent=setCP0EntryHi
                    and sub=EntryHi.ASID
                    and sub_update=EntryHi.ASID_update]

subsection \<open>@{const EntryHi.R}\<close>

abbreviation getCP0EntryHiR where
  "getCP0EntryHiR \<equiv> (\<lambda>s. EntryHi.R (EntryHi (c_CP0 (c_state s))))"

lemmas contract_getCP0EntryHi_CP0EntryHiR [alt_def_simp] = 
  contract_read[where getParent=getCP0EntryHi and sub=EntryHi.R]

abbreviation setCP0EntryHiR where
  "setCP0EntryHiR v \<equiv> c_state_update (c_CP0_update (EntryHi_update (EntryHi.R_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0EntryHiR [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0EntryHi
                           and setParent=setCP0EntryHi
                           and sub_update=EntryHi.R_update]
  contract_update[where getParent=getCP0EntryHi 
                    and setParent=setCP0EntryHi
                    and sub=EntryHi.R
                    and sub_update=EntryHi.R_update]

subsection \<open>@{const EntryHi.VPN2}\<close>

abbreviation getCP0EntryHiVPN2 where
  "getCP0EntryHiVPN2 \<equiv> (\<lambda>s. EntryHi.VPN2 (EntryHi (c_CP0 (c_state s))))"

lemmas contract_getCP0EntryHi_CP0EntryHiVPN2 [alt_def_simp] = 
  contract_read[where getParent=getCP0EntryHi and sub=EntryHi.VPN2]

abbreviation setCP0EntryHiVPN2 where
  "setCP0EntryHiVPN2 v \<equiv> c_state_update (c_CP0_update (EntryHi_update (EntryHi.VPN2_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0EntryHiVPN2 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0EntryHi
                           and setParent=setCP0EntryHi
                           and sub_update=EntryHi.VPN2_update]
  contract_update[where getParent=getCP0EntryHi 
                    and setParent=setCP0EntryHi
                    and sub=EntryHi.VPN2
                    and sub_update=EntryHi.VPN2_update]

subsection \<open>@{const entryhi'rst}\<close>

abbreviation getCP0EntryHiEntryhi'rst where
  "getCP0EntryHiEntryhi'rst \<equiv> (\<lambda>s. entryhi'rst (EntryHi (c_CP0 (c_state s))))"

lemmas contract_getCP0EntryHi_CP0EntryHiEntryhi'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0EntryHi and sub=entryhi'rst]

abbreviation setCP0EntryHiEntryhi'rst where
  "setCP0EntryHiEntryhi'rst v \<equiv> c_state_update (c_CP0_update (EntryHi_update (entryhi'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0EntryHiEntryhi'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0EntryHi
                           and setParent=setCP0EntryHi
                           and sub_update=entryhi'rst_update]
  contract_update[where getParent=getCP0EntryHi 
                    and setParent=setCP0EntryHi
                    and sub=entryhi'rst
                    and sub_update=entryhi'rst_update]

subsection \<open>@{const EntryLo0}\<close>

abbreviation getCP0EntryLo0 where
  "getCP0EntryLo0 \<equiv> (\<lambda>s. EntryLo0 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0EntryLo0 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=EntryLo0]

abbreviation setCP0EntryLo0 where
  "setCP0EntryLo0 v \<equiv> c_state_update (c_CP0_update (EntryLo0_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0EntryLo0 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=EntryLo0_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=EntryLo0
                    and sub_update=EntryLo0_update]

subsection \<open>@{const EntryLo1}\<close>

abbreviation getCP0EntryLo1 where
  "getCP0EntryLo1 \<equiv> (\<lambda>s. EntryLo1 (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0EntryLo1 [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=EntryLo1]

abbreviation setCP0EntryLo1 where
  "setCP0EntryLo1 v \<equiv> c_state_update (c_CP0_update (EntryLo1_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0EntryLo1 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=EntryLo1_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=EntryLo1
                    and sub_update=EntryLo1_update]

subsection \<open>@{const ErrCtl}\<close>

abbreviation getCP0ErrCtl where
  "getCP0ErrCtl \<equiv> (\<lambda>s. ErrCtl (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0ErrCtl [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=ErrCtl]

abbreviation setCP0ErrCtl where
  "setCP0ErrCtl v \<equiv> c_state_update (c_CP0_update (ErrCtl_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0ErrCtl [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=ErrCtl_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=ErrCtl
                    and sub_update=ErrCtl_update]

subsection \<open>@{const ErrorEPC}\<close>

abbreviation getCP0ErrorEPC where
  "getCP0ErrorEPC \<equiv> (\<lambda>s. ErrorEPC (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0ErrorEPC [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=ErrorEPC]

abbreviation setCP0ErrorEPC where
  "setCP0ErrorEPC v \<equiv> c_state_update (c_CP0_update (ErrorEPC_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0ErrorEPC [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=ErrorEPC_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=ErrorEPC
                    and sub_update=ErrorEPC_update]

subsection \<open>@{const HWREna}\<close>

abbreviation getCP0HWREna where
  "getCP0HWREna \<equiv> (\<lambda>s. HWREna (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0HWREna [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=HWREna]

abbreviation setCP0HWREna where
  "setCP0HWREna v \<equiv> c_state_update (c_CP0_update (HWREna_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0HWREna [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=HWREna_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=HWREna
                    and sub_update=HWREna_update]

subsection \<open>@{const Index}\<close>

abbreviation getCP0Index where
  "getCP0Index \<equiv> (\<lambda>s. Index (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Index [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Index]

abbreviation setCP0Index where
  "setCP0Index v \<equiv> c_state_update (c_CP0_update (Index_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Index [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Index_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Index
                    and sub_update=Index_update]

subsection \<open>@{const LLAddr}\<close>

abbreviation getCP0LLAddr where
  "getCP0LLAddr \<equiv> (\<lambda>s. LLAddr (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0LLAddr [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=LLAddr]

abbreviation setCP0LLAddr where
  "setCP0LLAddr v \<equiv> c_state_update (c_CP0_update (LLAddr_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0LLAddr [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=LLAddr_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=LLAddr
                    and sub_update=LLAddr_update]

subsection \<open>@{const PRId}\<close>

abbreviation getCP0PRId where
  "getCP0PRId \<equiv> (\<lambda>s. PRId (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0PRId [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=PRId]

abbreviation setCP0PRId where
  "setCP0PRId v \<equiv> c_state_update (c_CP0_update (PRId_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0PRId [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=PRId_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=PRId
                    and sub_update=PRId_update]

subsection \<open>@{const PageMask}\<close>

abbreviation getCP0PageMask where
  "getCP0PageMask \<equiv> (\<lambda>s. PageMask (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0PageMask [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=PageMask]

abbreviation setCP0PageMask where
  "setCP0PageMask v \<equiv> c_state_update (c_CP0_update (PageMask_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0PageMask [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=PageMask_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=PageMask
                    and sub_update=PageMask_update]

subsection \<open>@{const Random}\<close>

abbreviation getCP0Random where
  "getCP0Random \<equiv> (\<lambda>s. Random (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Random [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Random]

abbreviation setCP0Random where
  "setCP0Random v \<equiv> c_state_update (c_CP0_update (Random_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Random [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Random_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Random
                    and sub_update=Random_update]

subsection \<open>@{const Random.Random}\<close>

abbreviation getCP0RandomRandom where
  "getCP0RandomRandom \<equiv> (\<lambda>s. Random.Random (Random (c_CP0 (c_state s))))"

lemmas contract_getCP0Random_CP0RandomRandom [alt_def_simp] = 
  contract_read[where getParent=getCP0Random and sub=Random.Random]

abbreviation setCP0RandomRandom where
  "setCP0RandomRandom v \<equiv> c_state_update (c_CP0_update (Random_update (Random.Random_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0RandomRandom [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Random
                           and setParent=setCP0Random
                           and sub_update=Random.Random_update]
  contract_update[where getParent=getCP0Random 
                    and setParent=setCP0Random
                    and sub=Random.Random
                    and sub_update=Random.Random_update]

subsection \<open>@{const random'rst}\<close>

abbreviation getCP0RandomRandom'rst where
  "getCP0RandomRandom'rst \<equiv> (\<lambda>s. random'rst (Random (c_CP0 (c_state s))))"

lemmas contract_getCP0Random_CP0RandomRandom'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Random and sub=random'rst]

abbreviation setCP0RandomRandom'rst where
  "setCP0RandomRandom'rst v \<equiv> c_state_update (c_CP0_update (Random_update (random'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0RandomRandom'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Random
                           and setParent=setCP0Random
                           and sub_update=random'rst_update]
  contract_update[where getParent=getCP0Random 
                    and setParent=setCP0Random
                    and sub=random'rst
                    and sub_update=random'rst_update]

subsection \<open>@{const Status}\<close>

abbreviation getCP0Status where
  "getCP0Status \<equiv> (\<lambda>s. Status (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Status [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Status]

abbreviation setCP0Status where
  "setCP0Status v \<equiv> c_state_update (c_CP0_update (Status_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Status [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Status_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Status
                    and sub_update=Status_update]

subsection \<open>@{const BEV}\<close>

abbreviation getCP0StatusBEV where
  "getCP0StatusBEV \<equiv> (\<lambda>s. BEV (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusBEV [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=BEV]

abbreviation setCP0StatusBEV where
  "setCP0StatusBEV v \<equiv> c_state_update (c_CP0_update (Status_update (BEV_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusBEV [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=BEV_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=BEV
                    and sub_update=BEV_update]

subsection \<open>@{const CU0}\<close>

abbreviation getCP0StatusCU0 where
  "getCP0StatusCU0 \<equiv> (\<lambda>s. CU0 (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusCU0 [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=CU0]

abbreviation setCP0StatusCU0 where
  "setCP0StatusCU0 v \<equiv> c_state_update (c_CP0_update (Status_update (CU0_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusCU0 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=CU0_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=CU0
                    and sub_update=CU0_update]

subsection \<open>@{const CU1}\<close>

abbreviation getCP0StatusCU1 where
  "getCP0StatusCU1 \<equiv> (\<lambda>s. CU1 (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusCU1 [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=CU1]

abbreviation setCP0StatusCU1 where
  "setCP0StatusCU1 v \<equiv> c_state_update (c_CP0_update (Status_update (CU1_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusCU1 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=CU1_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=CU1
                    and sub_update=CU1_update]

subsection \<open>@{const CU2}\<close>

abbreviation getCP0StatusCU2 where
  "getCP0StatusCU2 \<equiv> (\<lambda>s. CU2 (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusCU2 [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=CU2]

abbreviation setCP0StatusCU2 where
  "setCP0StatusCU2 v \<equiv> c_state_update (c_CP0_update (Status_update (CU2_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusCU2 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=CU2_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=CU2
                    and sub_update=CU2_update]

subsection \<open>@{const CU3}\<close>

abbreviation getCP0StatusCU3 where
  "getCP0StatusCU3 \<equiv> (\<lambda>s. CU3 (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusCU3 [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=CU3]

abbreviation setCP0StatusCU3 where
  "setCP0StatusCU3 v \<equiv> c_state_update (c_CP0_update (Status_update (CU3_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusCU3 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=CU3_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=CU3
                    and sub_update=CU3_update]

subsection \<open>@{const ERL}\<close>

abbreviation getCP0StatusERL where
  "getCP0StatusERL \<equiv> (\<lambda>s. ERL (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusERL [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=ERL]

abbreviation setCP0StatusERL where
  "setCP0StatusERL v \<equiv> c_state_update (c_CP0_update (Status_update (ERL_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusERL [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=ERL_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=ERL
                    and sub_update=ERL_update]

subsection \<open>@{const EXL}\<close>

abbreviation getCP0StatusEXL where
  "getCP0StatusEXL \<equiv> (\<lambda>s. EXL (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusEXL [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=EXL]

abbreviation setCP0StatusEXL where
  "setCP0StatusEXL v \<equiv> c_state_update (c_CP0_update (Status_update (EXL_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusEXL [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=EXL_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=EXL
                    and sub_update=EXL_update]

subsection \<open>@{const FR}\<close>

abbreviation getCP0StatusFR where
  "getCP0StatusFR \<equiv> (\<lambda>s. FR (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusFR [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=FR]

abbreviation setCP0StatusFR where
  "setCP0StatusFR v \<equiv> c_state_update (c_CP0_update (Status_update (FR_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusFR [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=FR_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=FR
                    and sub_update=FR_update]

subsection \<open>@{const IE}\<close>

abbreviation getCP0StatusIE where
  "getCP0StatusIE \<equiv> (\<lambda>s. IE (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusIE [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=IE]

abbreviation setCP0StatusIE where
  "setCP0StatusIE v \<equiv> c_state_update (c_CP0_update (Status_update (IE_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusIE [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=IE_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=IE
                    and sub_update=IE_update]

subsection \<open>@{const IM}\<close>

abbreviation getCP0StatusIM where
  "getCP0StatusIM \<equiv> (\<lambda>s. IM (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusIM [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=IM]

abbreviation setCP0StatusIM where
  "setCP0StatusIM v \<equiv> c_state_update (c_CP0_update (Status_update (IM_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusIM [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=IM_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=IM
                    and sub_update=IM_update]

subsection \<open>@{const KSU}\<close>

abbreviation getCP0StatusKSU where
  "getCP0StatusKSU \<equiv> (\<lambda>s. KSU (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusKSU [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=KSU]

abbreviation setCP0StatusKSU where
  "setCP0StatusKSU v \<equiv> c_state_update (c_CP0_update (Status_update (KSU_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusKSU [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=KSU_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=KSU
                    and sub_update=KSU_update]

subsection \<open>@{const KX}\<close>

abbreviation getCP0StatusKX where
  "getCP0StatusKX \<equiv> (\<lambda>s. KX (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusKX [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=KX]

abbreviation setCP0StatusKX where
  "setCP0StatusKX v \<equiv> c_state_update (c_CP0_update (Status_update (KX_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusKX [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=KX_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=KX
                    and sub_update=KX_update]

subsection \<open>@{const StatusRegister.RE}\<close>

abbreviation getCP0StatusRE where
  "getCP0StatusRE \<equiv> (\<lambda>s. StatusRegister.RE (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusRE [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=StatusRegister.RE]

abbreviation setCP0StatusRE where
  "setCP0StatusRE v \<equiv> c_state_update (c_CP0_update (Status_update (StatusRegister.RE_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusRE [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=StatusRegister.RE_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=StatusRegister.RE
                    and sub_update=StatusRegister.RE_update]

subsection \<open>@{const SX}\<close>

abbreviation getCP0StatusSX where
  "getCP0StatusSX \<equiv> (\<lambda>s. SX (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusSX [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=SX]

abbreviation setCP0StatusSX where
  "setCP0StatusSX v \<equiv> c_state_update (c_CP0_update (Status_update (SX_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusSX [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=SX_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=SX
                    and sub_update=SX_update]

subsection \<open>@{const UX}\<close>

abbreviation getCP0StatusUX where
  "getCP0StatusUX \<equiv> (\<lambda>s. UX (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusUX [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=UX]

abbreviation setCP0StatusUX where
  "setCP0StatusUX v \<equiv> c_state_update (c_CP0_update (Status_update (UX_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusUX [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=UX_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=UX
                    and sub_update=UX_update]

subsection \<open>@{const statusregister'rst}\<close>

abbreviation getCP0StatusStatusregister'rst where
  "getCP0StatusStatusregister'rst \<equiv> (\<lambda>s. statusregister'rst (Status (c_CP0 (c_state s))))"

lemmas contract_getCP0Status_CP0StatusStatusregister'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Status and sub=statusregister'rst]

abbreviation setCP0StatusStatusregister'rst where
  "setCP0StatusStatusregister'rst v \<equiv> c_state_update (c_CP0_update (Status_update (statusregister'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0StatusStatusregister'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Status
                           and setParent=setCP0Status
                           and sub_update=statusregister'rst_update]
  contract_update[where getParent=getCP0Status 
                    and setParent=setCP0Status
                    and sub=statusregister'rst
                    and sub_update=statusregister'rst_update]

subsection \<open>@{const UsrLocal}\<close>

abbreviation getCP0UsrLocal where
  "getCP0UsrLocal \<equiv> (\<lambda>s. UsrLocal (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0UsrLocal [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=UsrLocal]

abbreviation setCP0UsrLocal where
  "setCP0UsrLocal v \<equiv> c_state_update (c_CP0_update (UsrLocal_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0UsrLocal [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=UsrLocal_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=UsrLocal
                    and sub_update=UsrLocal_update]

subsection \<open>@{const Wired}\<close>

abbreviation getCP0Wired where
  "getCP0Wired \<equiv> (\<lambda>s. Wired (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0Wired [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=Wired]

abbreviation setCP0Wired where
  "setCP0Wired v \<equiv> c_state_update (c_CP0_update (Wired_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0Wired [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=Wired_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=Wired
                    and sub_update=Wired_update]

subsection \<open>@{const Wired.Wired}\<close>

abbreviation getCP0WiredWired where
  "getCP0WiredWired \<equiv> (\<lambda>s. Wired.Wired (Wired (c_CP0 (c_state s))))"

lemmas contract_getCP0Wired_CP0WiredWired [alt_def_simp] = 
  contract_read[where getParent=getCP0Wired and sub=Wired.Wired]

abbreviation setCP0WiredWired where
  "setCP0WiredWired v \<equiv> c_state_update (c_CP0_update (Wired_update (Wired.Wired_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0WiredWired [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Wired
                           and setParent=setCP0Wired
                           and sub_update=Wired.Wired_update]
  contract_update[where getParent=getCP0Wired 
                    and setParent=setCP0Wired
                    and sub=Wired.Wired
                    and sub_update=Wired.Wired_update]

subsection \<open>@{const wired'rst}\<close>

abbreviation getCP0WiredWired'rst where
  "getCP0WiredWired'rst \<equiv> (\<lambda>s. wired'rst (Wired (c_CP0 (c_state s))))"

lemmas contract_getCP0Wired_CP0WiredWired'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0Wired and sub=wired'rst]

abbreviation setCP0WiredWired'rst where
  "setCP0WiredWired'rst v \<equiv> c_state_update (c_CP0_update (Wired_update (wired'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0WiredWired'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0Wired
                           and setParent=setCP0Wired
                           and sub_update=wired'rst_update]
  contract_update[where getParent=getCP0Wired 
                    and setParent=setCP0Wired
                    and sub=wired'rst
                    and sub_update=wired'rst_update]

subsection \<open>@{const XContext}\<close>

abbreviation getCP0XContext where
  "getCP0XContext \<equiv> (\<lambda>s. XContext (c_CP0 (c_state s)))"

lemmas contract_getCP0_CP0XContext [alt_def_simp] = 
  contract_read[where getParent=getCP0 and sub=XContext]

abbreviation setCP0XContext where
  "setCP0XContext v \<equiv> c_state_update (c_CP0_update (XContext_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CP0XContext [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0
                           and setParent=setCP0
                           and sub_update=XContext_update]
  contract_update[where getParent=getCP0 
                    and setParent=setCP0
                    and sub=XContext
                    and sub_update=XContext_update]

subsection \<open>@{const XContext.BadVPN2}\<close>

abbreviation getCP0XContextBadVPN2 where
  "getCP0XContextBadVPN2 \<equiv> (\<lambda>s. XContext.BadVPN2 (XContext (c_CP0 (c_state s))))"

lemmas contract_getCP0XContext_CP0XContextBadVPN2 [alt_def_simp] = 
  contract_read[where getParent=getCP0XContext and sub=XContext.BadVPN2]

abbreviation setCP0XContextBadVPN2 where
  "setCP0XContextBadVPN2 v \<equiv> c_state_update (c_CP0_update (XContext_update (XContext.BadVPN2_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0XContextBadVPN2 [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0XContext
                           and setParent=setCP0XContext
                           and sub_update=XContext.BadVPN2_update]
  contract_update[where getParent=getCP0XContext 
                    and setParent=setCP0XContext
                    and sub=XContext.BadVPN2
                    and sub_update=XContext.BadVPN2_update]

subsection \<open>@{const XContext.PTEBase}\<close>

abbreviation getCP0XContextPTEBase where
  "getCP0XContextPTEBase \<equiv> (\<lambda>s. XContext.PTEBase (XContext (c_CP0 (c_state s))))"

lemmas contract_getCP0XContext_CP0XContextPTEBase [alt_def_simp] = 
  contract_read[where getParent=getCP0XContext and sub=XContext.PTEBase]

abbreviation setCP0XContextPTEBase where
  "setCP0XContextPTEBase v \<equiv> c_state_update (c_CP0_update (XContext_update (XContext.PTEBase_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0XContextPTEBase [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0XContext
                           and setParent=setCP0XContext
                           and sub_update=XContext.PTEBase_update]
  contract_update[where getParent=getCP0XContext 
                    and setParent=setCP0XContext
                    and sub=XContext.PTEBase
                    and sub_update=XContext.PTEBase_update]

subsection \<open>@{const XContext.R}\<close>

abbreviation getCP0XContextR where
  "getCP0XContextR \<equiv> (\<lambda>s. XContext.R (XContext (c_CP0 (c_state s))))"

lemmas contract_getCP0XContext_CP0XContextR [alt_def_simp] = 
  contract_read[where getParent=getCP0XContext and sub=XContext.R]

abbreviation setCP0XContextR where
  "setCP0XContextR v \<equiv> c_state_update (c_CP0_update (XContext_update (XContext.R_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0XContextR [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0XContext
                           and setParent=setCP0XContext
                           and sub_update=XContext.R_update]
  contract_update[where getParent=getCP0XContext 
                    and setParent=setCP0XContext
                    and sub=XContext.R
                    and sub_update=XContext.R_update]

subsection \<open>@{const xcontext'rst}\<close>

abbreviation getCP0XContextXcontext'rst where
  "getCP0XContextXcontext'rst \<equiv> (\<lambda>s. xcontext'rst (XContext (c_CP0 (c_state s))))"

lemmas contract_getCP0XContext_CP0XContextXcontext'rst [alt_def_simp] = 
  contract_read[where getParent=getCP0XContext and sub=xcontext'rst]

abbreviation setCP0XContextXcontext'rst where
  "setCP0XContextXcontext'rst v \<equiv> c_state_update (c_CP0_update (XContext_update (xcontext'rst_update (\<lambda>_. v))))"

lemmas contract_c_state_update_CP0XContextXcontext'rst [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCP0XContext
                           and setParent=setCP0XContext
                           and sub_update=xcontext'rst_update]
  contract_update[where getParent=getCP0XContext 
                    and setParent=setCP0XContext
                    and sub=xcontext'rst
                    and sub_update=xcontext'rst_update]

subsection \<open>@{const c_CoreStats}\<close>

abbreviation getCoreStats where
  "getCoreStats \<equiv> (\<lambda>s. c_CoreStats (c_state s))"

lemma coreStats_alt [alt_def_simp]:
  shows "coreStats = read_state getCoreStats"
unfolding coreStats_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_CoreStats [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_CoreStats]

abbreviation setCoreStats where
  "setCoreStats v \<equiv> c_state_update (c_CoreStats_update (\<lambda>_. v))"

lemma write'coreStats_alt [alt_def_simp]:
  shows "write'coreStats = (\<lambda>v. update_state (setCoreStats v))"
unfolding write'coreStats_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_CoreStats [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_CoreStats_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_CoreStats
                    and sub_update=c_CoreStats_update]

subsection \<open>@{const branch_not_taken}\<close>

abbreviation getCoreStatsBranch_not_taken where
  "getCoreStatsBranch_not_taken \<equiv> (\<lambda>s. branch_not_taken (c_CoreStats (c_state s)))"

lemmas contract_getCoreStats_CoreStatsBranch_not_taken [alt_def_simp] = 
  contract_read[where getParent=getCoreStats and sub=branch_not_taken]

abbreviation setCoreStatsBranch_not_taken where
  "setCoreStatsBranch_not_taken v \<equiv> c_state_update (c_CoreStats_update (branch_not_taken_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CoreStatsBranch_not_taken [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCoreStats
                           and setParent=setCoreStats
                           and sub_update=branch_not_taken_update]
  contract_update[where getParent=getCoreStats 
                    and setParent=setCoreStats
                    and sub=branch_not_taken
                    and sub_update=branch_not_taken_update]

subsection \<open>@{const branch_taken}\<close>

abbreviation getCoreStatsBranch_taken where
  "getCoreStatsBranch_taken \<equiv> (\<lambda>s. branch_taken (c_CoreStats (c_state s)))"

lemmas contract_getCoreStats_CoreStatsBranch_taken [alt_def_simp] = 
  contract_read[where getParent=getCoreStats and sub=branch_taken]

abbreviation setCoreStatsBranch_taken where
  "setCoreStatsBranch_taken v \<equiv> c_state_update (c_CoreStats_update (branch_taken_update (\<lambda>_. v)))"

lemmas contract_c_state_update_CoreStatsBranch_taken [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=getCoreStats
                           and setParent=setCoreStats
                           and sub_update=branch_taken_update]
  contract_update[where getParent=getCoreStats 
                    and setParent=setCoreStats
                    and sub=branch_taken
                    and sub_update=branch_taken_update]

subsection \<open>@{const c_LLbit}\<close>

abbreviation getLLbit where
  "getLLbit \<equiv> (\<lambda>s. c_LLbit (c_state s))"

lemma LLbit_alt [alt_def_simp]:
  shows "LLbit = read_state getLLbit"
unfolding LLbit_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_LLbit [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_LLbit]

abbreviation setLLbit where
  "setLLbit v \<equiv> c_state_update (c_LLbit_update (\<lambda>_. v))"

lemma write'LLbit_alt [alt_def_simp]:
  shows "write'LLbit = (\<lambda>v. update_state (setLLbit v))"
unfolding write'LLbit_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_LLbit [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_LLbit_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_LLbit
                    and sub_update=c_LLbit_update]

subsection \<open>@{const c_PC}\<close>

abbreviation getPC where
  "getPC \<equiv> (\<lambda>s. c_PC (c_state s))"

lemma PC_alt [alt_def_simp]:
  shows "PC = read_state getPC"
unfolding PC_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_PC [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_PC]

abbreviation setPC where
  "setPC v \<equiv> c_state_update (c_PC_update (\<lambda>_. v))"

lemma write'PC_alt [alt_def_simp]:
  shows "write'PC = (\<lambda>v. update_state (setPC v))"
unfolding write'PC_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_PC [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_PC_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_PC
                    and sub_update=c_PC_update]

subsection \<open>@{const c_exceptionSignalled}\<close>

abbreviation getExceptionSignalled where
  "getExceptionSignalled \<equiv> (\<lambda>s. c_exceptionSignalled (c_state s))"

lemma exceptionSignalled_alt [alt_def_simp]:
  shows "exceptionSignalled = read_state getExceptionSignalled"
unfolding exceptionSignalled_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_ExceptionSignalled [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_exceptionSignalled]

abbreviation setExceptionSignalled where
  "setExceptionSignalled v \<equiv> c_state_update (c_exceptionSignalled_update (\<lambda>_. v))"

lemma write'exceptionSignalled_alt [alt_def_simp]:
  shows "write'exceptionSignalled = (\<lambda>v. update_state (setExceptionSignalled v))"
unfolding write'exceptionSignalled_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_ExceptionSignalled [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_exceptionSignalled_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_exceptionSignalled
                    and sub_update=c_exceptionSignalled_update]

subsection \<open>@{const c_hi}\<close>

abbreviation getHi where
  "getHi \<equiv> (\<lambda>s. c_hi (c_state s))"

lemma hi_alt [alt_def_simp]:
  shows "hi = read_state getHi"
unfolding hi_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_Hi [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_hi]

abbreviation setHi where
  "setHi v \<equiv> c_state_update (c_hi_update (\<lambda>_. v))"

lemma write'hi_alt [alt_def_simp]:
  shows "write'hi = (\<lambda>v. update_state (setHi v))"
unfolding write'hi_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_Hi [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_hi_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_hi
                    and sub_update=c_hi_update]

subsection \<open>@{const c_lo}\<close>

abbreviation getLo where
  "getLo \<equiv> (\<lambda>s. c_lo (c_state s))"

lemma lo_alt [alt_def_simp]:
  shows "lo = read_state getLo"
unfolding lo_def
unfolding monad_def Let_def
by simp

lemmas contract_c_state_Lo [alt_def_simp] = 
  contract_read[where getParent=c_state and sub=c_lo]

abbreviation setLo where
  "setLo v \<equiv> c_state_update (c_lo_update (\<lambda>_. v))"

lemma write'lo_alt [alt_def_simp]:
  shows "write'lo = (\<lambda>v. update_state (setLo v))"
unfolding write'lo_def
unfolding monad_def Let_def
by (intro ext) simp

lemmas contract_c_state_update_Lo [simplified, alt_def_simp] = 
  contract_update_constant[where getParent=c_state 
                           and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                           and sub_update=c_lo_update]
  contract_update[where getParent=c_state 
                    and setParent="\<lambda>v. c_state_update (\<lambda>_. v)"
                    and sub=c_lo
                    and sub_update=c_lo_update]

(* Code generation - end *)

section \<open>Rewriting the structure of functions\<close>

subsection \<open>Associativity\<close>

declare bind_associativity [alt_def_simp]

subsection \<open>Distributive lemmas\<close>

lemmas case_return_return [alt_def_simp] =
  all_distrib[where h="\<lambda>x. return x", THEN sym]

lemmas pair_cases_distrib [alt_def_simp] = 
  all_distrib[where h="\<lambda>x. (x, _)", THEN sym]
  all_distrib[where h="\<lambda>x. (_, x)", THEN sym]

lemma if_bind_return_return [alt_def_simp]:
  shows "(if b then bind m (\<lambda>_. return x) else return x) = 
         bind (if b then m else return ()) (\<lambda>_. return x)"
unfolding monad_def Let_def
by simp

lemma if_return_bind_return [alt_def_simp]:
  shows "(if b then return x else bind m (\<lambda>_. return x)) = 
         bind (if b then return () else m) (\<lambda>_. return x)"
unfolding monad_def Let_def
by simp

lemma if_bind_return_bind_return [alt_def_simp]:
  shows "(if b then bind m (\<lambda>v. return (x v)) else bind n (\<lambda>v. return (x v))) = 
         bind (if b then m else n) (\<lambda>v. return (x v))"
unfolding monad_def Let_def
by simp

lemma if_bind_bind_return_return [alt_def_simp]:
  shows "(if b then bind m (\<lambda>a. bind (n a) (\<lambda>_. return x)) else return x) = 
         bind (if b then bind m (\<lambda>a. n a) else return ()) (\<lambda>_. return x)"
unfolding monad_def Let_def
by simp

lemma if_return_bind_bind_return [alt_def_simp]:
  shows "(if b then return x else bind m (\<lambda>a. bind (n a) (\<lambda>_. return x))) = 
         bind (if b then return () else bind m (\<lambda>a. n a)) (\<lambda>_. return x)"
unfolding monad_def Let_def
by simp

lemma if_return_return_pair_left [alt_def_simp]:
  shows "(if b then return (x, y) else return (x, z)) = 
         bind (if b then return y else return z) (\<lambda>a. return (x, a))"
unfolding monad_def Let_def
by simp

lemma if_return_return_pair_right [alt_def_simp]:
  shows "(if b then return (x, z) else return (y, z)) = 
         bind (if b then return x else return y) (\<lambda>a. return (a, z))"
unfolding monad_def Let_def
by simp

lemma if_bind_return_return_pair_left [alt_def_simp]:
  shows "(if b then bind m (\<lambda>a. return (x, y a)) else return (x, z)) = 
         bind (if b then bind m (\<lambda>a. return (y a)) else return z) (\<lambda>a. return (x, a))"
unfolding monad_def Let_def
by simp

lemma if_bind_return_return_pair_right [alt_def_simp]:
  shows "(if b then bind m (\<lambda>a. return (x a, z)) else return (y, z)) = 
         bind (if b then bind m (\<lambda>a. return (x a)) else return y) (\<lambda>a. return (a, z))"
unfolding monad_def Let_def
by simp

lemma prod_bind_left [alt_def_simp]:
  shows "case x of (y, z) \<Rightarrow> bind (m y z) n = 
         bind (case x of (y, z) \<Rightarrow> m y z) n" 
by (cases x) auto 

lemma prod_bind_right [alt_def_simp]:
  shows "case x of (y, z) \<Rightarrow> bind m (n y z) = 
         bind m (\<lambda>a. case x of (y, z) \<Rightarrow> n y z a)" 
by (cases x) auto 

lemma let_bind_left [alt_def_simp]:
  shows "(let x = y in bind (m x) n) =
         bind (let x = y in m x) n"
by simp

lemma let_bind_right [alt_def_simp]:
  shows "(let x = y in bind m (n x)) =
         bind m (\<lambda>a. let x = y in n x a)"
by simp

subsection \<open>Changing the order\<close>

text \<open>The following lemmas are tailored to the generated CHERI definition and not of general
interest.\<close>

lemma swap_CP0_return [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (return x) (k a)) = 
         bind (return x) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

text \<open>The following lemma was included by mistake, and turned out crucial for generating the
alternative definition of @{const Fetch}. Together with \<open>swap_c_state_CP0\<close> it should loop, but for
some reason the simplifier does not loop when both these lemmas are used together.\<close>

lemma swap_CP0_read_state [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (read_state f) (k a)) = 
         bind (read_state f) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

lemma swap_CP0_PC [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (read_state getPC) (k a)) = 
         bind (read_state getPC) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

lemma swap_CP0_currentInst [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (read_state currentInst) (k a)) = 
         bind (read_state currentInst) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

lemma swap_CP0_if_return_read_state_return [alt_def_simp]:
  shows "bind (read_state getCP0) 
              (\<lambda>a. bind (if b then return x else bind (read_state f) (\<lambda>a. return (g a))) 
              (k a)) = 
         bind (if b then return x else bind (read_state f) (\<lambda>a. return (g a))) 
              (\<lambda>b. bind (read_state getCP0) 
              (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

lemma swap_CP0_PCC [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind PCC (k a)) = 
         bind PCC (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding PCC_def
unfolding monad_def Let_def
by simp

lemma swap_CP0_CAPR [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (CAPR cd) (k a)) = 
         bind (CAPR cd) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding CAPR_def
unfolding monad_def Let_def
by simp

lemma swap_CP0_next_unknown [alt_def_simp]:
  shows "bind (read_state getCP0) (\<lambda>a. bind (next_unknown v) (k a)) = 
         bind (next_unknown v) (\<lambda>b. bind (read_state getCP0) (\<lambda>a. k a b))"
unfolding next_unknown_def
unfolding monad_def Let_def
by simp

lemma swap_c_state_return [alt_def_simp]:
  shows "bind (read_state c_state) (\<lambda>a. bind (return x) (k a)) = 
         bind (return x) (\<lambda>b. bind (read_state c_state) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

lemma swap_c_state_CP0 [alt_def_simp]:
  shows "bind (read_state c_state) (\<lambda>a. bind (read_state getCP0) (k a)) = 
         bind (read_state getCP0) (\<lambda>b. bind (read_state c_state) (\<lambda>a. k a b))"
unfolding monad_def Let_def
by simp

subsection \<open>Manual contractions\<close>

lemmas contract_c_state_update_CP0CauseIP_2 [alt_def_simp] =
  contract_c_state_update_CP0Cause(3-4)
    [where f="\<lambda>cause. cause\<lparr>IP := _ (IP cause)\<rparr>"]

lemmas contract_c_state_update_CP0EntryLo0_2 [alt_def_simp] =
  contract_c_state_update_CP0EntryLo0(3-4)
    [where f="\<lambda>x. _ (x, _)"]

lemmas contract_c_state_update_CP0EntryLo1_2 [alt_def_simp] =
  contract_c_state_update_CP0EntryLo1(3-4)
    [where f="\<lambda>x. _ (x, _)"]

lemmas contract_c_state_update_CP0EntryHi_2 [alt_def_simp] =
  contract_c_state_update_CP0EntryHi(3-4)
    [where f="\<lambda>x. _ (x, _)"]

lemmas contract_c_state_update_CP0Status_2 [alt_def_simp] =
  contract_c_state_update_CP0Status(3-4)
    [where f="\<lambda>x. _ (x, _)"]

subsection \<open>Removing @{const return}\<close>

text \<open>We later remove the lemma \<open>bind_left_identity\<close> from the proof method, to avoid the proof
method to simplify away \<open>return (X a)\<close> where \<open>X\<close> is a state component. In the following cases it is
still fine to simplify away \<open>return\<close>. \<close>

named_theorems bind_left_identity_specific

thm bind_left_identity

lemmas bind_left_identity_unit [bind_left_identity_specific] =
  bind_left_identity[where a="()"]

lemmas bind_left_identity_fst [bind_left_identity_specific] =
  bind_left_identity[where a="fst _"]

lemmas bind_left_identity_snd [bind_left_identity_specific] =
  bind_left_identity[where a="snd _"]

lemmas bind_left_identity_pair [bind_left_identity_specific] =
  bind_left_identity[where a="(_,_)"]

lemmas bind_left_identity_not [bind_left_identity_specific] =
  bind_left_identity[where a="\<not> _"]

lemmas bind_left_identity_eq [bind_left_identity_specific] =
  bind_left_identity[where a="_ = _"]

lemmas bind_left_identity_plus [bind_left_identity_specific] =
  bind_left_identity[where a="_ + _"]

lemmas bind_left_identity_minus [bind_left_identity_specific] =
  bind_left_identity[where a="_ - _"]

lemmas bind_left_identity_BadInstr [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>BadInstr := _\<rparr>"]

lemmas bind_left_identity_BadInstrP [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>BadInstrP := _\<rparr>"]

lemmas bind_left_identity_BadVAddr [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>BadVAddr := _\<rparr>"]

lemmas bind_left_identity_EPC [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>EPC := _\<rparr>"]

lemmas bind_left_identity_c_CP0 [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>c_CP0 := _\<rparr>"]

lemmas bind_left_identity_Count [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>Count := _\<rparr>"]

lemmas bind_left_identity_Cause [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>Cause := _\<rparr>"]

lemmas bind_left_identity_CauseIP [bind_left_identity_specific] =
  bind_left_identity[where a="Cause _\<lparr>IP := _\<rparr>"]

lemmas bind_left_identity_Random [bind_left_identity_specific] =
  bind_left_identity[where a="_\<lparr>CP0.Random := _\<rparr>"]

lemmas bind_left_identity_RandomRandom [bind_left_identity_specific] =
  bind_left_identity[where a="CP0.Random _\<lparr>Random.Random := _\<rparr>"]

lemmas bind_left_identity_word_bit_field_insert [bind_left_identity_specific] =
  bind_left_identity[where a="word_bit_field_insert _ _ _ _"]

section \<open>Alternative definitions\<close>

method compute_alt_def_pass_1 uses simp del =
  -- \<open>In the first pass we only simplify some occurrences of @{const return}.\<close>
  (strong_cong_simp 
     add: bind_left_identity_specific alt_def_simp simp
     del: bind_left_identity alt_def_simp_del del)

method compute_alt_def_pass_2 uses simp del =
  -- \<open>In the second pass we simplify all occurrences of @{const return}.\<close>
  (strong_cong_simp 
     add: alt_def_simp simp
     del: alt_def_simp_del del)

method compute_alt_def uses simp del =
  -- \<open>Applying \<open>trans\<close> allows us to simplify schematic goals twice.\<close>
  (rule trans),
  (compute_alt_def_pass_1 simp: simp del: del),
  (compute_alt_def_pass_2 simp: simp del: del)

(* Code generation - start - alternative definitions *)

(* Code generation - prefix - raise'exception *)

text \<open>The function @{const raise'exception} can have any type @{typ "state \<Rightarrow> 'a \<times> state"}. When
@{const raise'exception} is used in other functions, we do not know which type they use, which makes
it hard to state assumptions about that use of @{const raise'exception}.

To circumvent that, we replace @{const raise'exception} with another version that only updates the
state, and a @{term "return undefined"}. We give this other version the same name, which means that
in the rest of the development it seems that @{const raise'exception} has always been of type @{typ
"state \<Rightarrow> unit \<times> state"}.\<close>

definition raise'exception :: "exception \<Rightarrow> state \<Rightarrow> unit \<times> state" where
  "raise'exception \<equiv> \<lambda>e. bind (read_state exception) 
                               (\<lambda>v. if v = NoException 
                                    then update_state (exception_update (\<lambda>_. e)) 
                                    else return ())"

lemma raise'exception_simp [alt_def_simp]:
  shows "CHERI_Monadic_p256.raise'exception = 
         (\<lambda>ex. bind (raise'exception ex)
                    (\<lambda>_. return undefined))"
unfolding CHERI_Monadic_p256.raise'exception_def
          raise'exception_def
by (simp add: bind_associativity)

(* Code generation - end prefix *)

schematic_goal raise'exception_alt_def:
  shows "raise'exception = ?x"
unfolding raise'exception_def
unfolding Let_def
by compute_alt_def

schematic_goal println_alt_def [simp]:
  shows "println = ?x"
unfolding println_def
unfolding Let_def
by compute_alt_def

schematic_goal clear_watcher_alt_def [simp]:
  shows "clear_watcher = ?x"
unfolding clear_watcher_def
unfolding Let_def
by compute_alt_def

schematic_goal clear_logs_alt_def [simp]:
  shows "clear_logs = ?x"
unfolding clear_logs_def
unfolding Let_def
by compute_alt_def

schematic_goal PIC_update_alt_def:
  shows "PIC_update = ?x"
unfolding PIC_update_def
unfolding Let_def
by compute_alt_def

schematic_goal PIC_initialise_alt_def:
  shows "PIC_initialise = ?x"
unfolding PIC_initialise_def
unfolding Let_def
by compute_alt_def

schematic_goal PIC_load_alt_def:
  shows "PIC_load = ?x"
unfolding PIC_load_def
unfolding Let_def
by compute_alt_def

schematic_goal PIC_store_alt_def:
  shows "PIC_store = ?x"
unfolding PIC_store_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_update_interrupt_bit_alt_def:
  shows "JTAG_UART_update_interrupt_bit = ?x"
unfolding JTAG_UART_update_interrupt_bit_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_load_alt_def:
  shows "JTAG_UART_load = ?x"
unfolding JTAG_UART_load_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_input_alt_def:
  shows "JTAG_UART_input = ?x"
unfolding JTAG_UART_input_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_store_alt_def:
  shows "JTAG_UART_store = ?x"
unfolding JTAG_UART_store_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_output_alt_def:
  shows "JTAG_UART_output = ?x"
unfolding JTAG_UART_output_def
unfolding Let_def
by compute_alt_def

schematic_goal JTAG_UART_initialise_alt_def:
  shows "JTAG_UART_initialise = ?x"
unfolding JTAG_UART_initialise_def
unfolding Let_def
by compute_alt_def

schematic_goal gpr_alt_def:
  shows "gpr = ?x"
unfolding gpr_def
unfolding Let_def
by compute_alt_def

schematic_goal write'gpr_alt_def:
  shows "write'gpr = ?x"
unfolding write'gpr_def
unfolding Let_def
by compute_alt_def

schematic_goal GPR_alt_def:
  shows "GPR = ?x"
unfolding GPR_def
unfolding Let_def
by compute_alt_def

schematic_goal write'GPR_alt_def:
  shows "write'GPR = ?x"
unfolding write'GPR_def
unfolding Let_def
by compute_alt_def

schematic_goal UserMode_alt_def:
  shows "UserMode = ?x"
unfolding UserMode_def
unfolding Let_def
by compute_alt_def

schematic_goal SupervisorMode_alt_def:
  shows "SupervisorMode = ?x"
unfolding SupervisorMode_def
unfolding Let_def
by compute_alt_def

schematic_goal KernelMode_alt_def:
  shows "KernelMode = ?x"
unfolding KernelMode_def
unfolding Let_def
by compute_alt_def

schematic_goal BigEndianMem_alt_def:
  shows "BigEndianMem = ?x"
unfolding BigEndianMem_def
unfolding Let_def
by compute_alt_def

schematic_goal ReverseEndian_alt_def:
  shows "ReverseEndian = ?x"
unfolding ReverseEndian_def
unfolding Let_def
by compute_alt_def

schematic_goal BigEndianCPU_alt_def:
  shows "BigEndianCPU = ?x"
unfolding BigEndianCPU_def
unfolding Let_def
by compute_alt_def

schematic_goal CheckBranch_alt_def:
  shows "CheckBranch = ?x"
unfolding CheckBranch_def
unfolding Let_def
by compute_alt_def

schematic_goal BranchNotTaken_alt_def:
  shows "BranchNotTaken = ?x"
unfolding BranchNotTaken_def
unfolding Let_def
by compute_alt_def

schematic_goal BranchLikelyNotTaken_alt_def:
  shows "BranchLikelyNotTaken = ?x"
unfolding BranchLikelyNotTaken_def
unfolding Let_def
by compute_alt_def

schematic_goal dumpRegs_alt_def [simp]:
  shows "dumpRegs = ?x"
unfolding dumpRegs_def
unfolding Let_def
by compute_alt_def

schematic_goal initCoreStats_alt_def:
  shows "initCoreStats = ?x"
unfolding initCoreStats_def
unfolding Let_def
by compute_alt_def

schematic_goal printCoreStats_alt_def:
  shows "printCoreStats = ?x"
unfolding printCoreStats_def
unfolding Let_def
by compute_alt_def

schematic_goal next_unknown_alt_def:
  shows "next_unknown = ?x"
unfolding next_unknown_def
unfolding Let_def
by compute_alt_def

schematic_goal dumpCRegs_alt_def [simp]:
  shows "dumpCRegs = ?x"
unfolding dumpCRegs_def
unfolding Let_def
by compute_alt_def

schematic_goal PCC_alt_def:
  shows "PCC = ?x"
unfolding PCC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'PCC_alt_def:
  shows "write'PCC = ?x"
unfolding write'PCC_def
unfolding Let_def
by compute_alt_def

schematic_goal CAPR_alt_def:
  shows "CAPR = ?x"
unfolding CAPR_def
unfolding Let_def
by compute_alt_def

schematic_goal write'CAPR_alt_def:
  shows "write'CAPR = ?x"
unfolding write'CAPR_def
unfolding Let_def
by compute_alt_def

schematic_goal SCAPR_alt_def:
  shows "SCAPR = ?x"
unfolding SCAPR_def
unfolding Let_def
by compute_alt_def

schematic_goal write'SCAPR_alt_def:
  shows "write'SCAPR = ?x"
unfolding write'SCAPR_def
unfolding Let_def
by compute_alt_def

schematic_goal RCC_alt_def [simp]:
  shows "RCC = ?x"
unfolding RCC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'RCC_alt_def [simp]:
  shows "write'RCC = ?x"
unfolding write'RCC_def
unfolding Let_def
by compute_alt_def

schematic_goal IDC_alt_def [simp]:
  shows "IDC = ?x"
unfolding IDC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'IDC_alt_def [simp]:
  shows "write'IDC = ?x"
unfolding write'IDC_def
unfolding Let_def
by compute_alt_def

schematic_goal DDC_alt_def [simp]:
  shows "DDC = ?x"
unfolding DDC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'DDC_alt_def [simp]:
  shows "write'DDC = ?x"
unfolding write'DDC_def
unfolding Let_def
by compute_alt_def

schematic_goal TLSC_alt_def [simp]:
  shows "TLSC = ?x"
unfolding TLSC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'TLSC_alt_def [simp]:
  shows "write'TLSC = ?x"
unfolding write'TLSC_def
unfolding Let_def
by compute_alt_def

schematic_goal PTLSC_alt_def [simp]:
  shows "PTLSC = ?x"
unfolding PTLSC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'PTLSC_alt_def [simp]:
  shows "write'PTLSC = ?x"
unfolding write'PTLSC_def
unfolding Let_def
by compute_alt_def

schematic_goal KR1C_alt_def [simp]:
  shows "KR1C = ?x"
unfolding KR1C_def
unfolding Let_def
by compute_alt_def

schematic_goal write'KR1C_alt_def [simp]:
  shows "write'KR1C = ?x"
unfolding write'KR1C_def
unfolding Let_def
by compute_alt_def

schematic_goal KR2C_alt_def [simp]:
  shows "KR2C = ?x"
unfolding KR2C_def
unfolding Let_def
by compute_alt_def

schematic_goal write'KR2C_alt_def [simp]:
  shows "write'KR2C = ?x"
unfolding write'KR2C_def
unfolding Let_def
by compute_alt_def

schematic_goal KCC_alt_def [simp]:
  shows "KCC = ?x"
unfolding KCC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'KCC_alt_def [simp]:
  shows "write'KCC = ?x"
unfolding write'KCC_def
unfolding Let_def
by compute_alt_def

schematic_goal KDC_alt_def [simp]:
  shows "KDC = ?x"
unfolding KDC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'KDC_alt_def [simp]:
  shows "write'KDC = ?x"
unfolding write'KDC_def
unfolding Let_def
by compute_alt_def

schematic_goal EPCC_alt_def [simp]:
  shows "EPCC = ?x"
unfolding EPCC_def
unfolding Let_def
by compute_alt_def

schematic_goal write'EPCC_alt_def [simp]:
  shows "write'EPCC = ?x"
unfolding write'EPCC_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalException_alt_def:
  shows "SignalException = ?x"
unfolding SignalException_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalCP2UnusableException_alt_def:
  shows "SignalCP2UnusableException = ?x"
unfolding SignalCP2UnusableException_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalCapException_internal_alt_def:
  shows "SignalCapException_internal = ?x"
unfolding SignalCapException_internal_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalCapException_alt_def:
  shows "SignalCapException = ?x"
unfolding SignalCapException_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalCapException_noReg_alt_def:
  shows "SignalCapException_noReg = ?x"
unfolding SignalCapException_noReg_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ERET_alt_def:
  shows "dfn'ERET = ?x"
unfolding dfn'ERET_def
unfolding Let_def
by compute_alt_def

schematic_goal TLB_direct_alt_def:
  shows "TLB_direct = ?x"
unfolding TLB_direct_def
unfolding Let_def
by compute_alt_def

schematic_goal write'TLB_direct_alt_def:
  shows "write'TLB_direct = ?x"
unfolding write'TLB_direct_def
unfolding Let_def
by compute_alt_def

schematic_goal TLB_assoc_alt_def:
  shows "TLB_assoc = ?x"
unfolding TLB_assoc_def
unfolding Let_def
by compute_alt_def

schematic_goal write'TLB_assoc_alt_def:
  shows "write'TLB_assoc = ?x"
unfolding write'TLB_assoc_def
unfolding Let_def
by compute_alt_def

schematic_goal LookupTLB_alt_def:
  shows "LookupTLB = ?x"
unfolding LookupTLB_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalTLBException_internal_alt_def:
  shows "SignalTLBException_internal = ?x"
unfolding SignalTLBException_internal_def
unfolding Let_def
by compute_alt_def

(* Code generation - override - SignalTLBException *)

text \<open>Like @{const raise'exception}, @{const SignalTLBException}

 can have any type @{typ "state \<Rightarrow> 'a \<times> state"}. For the same reason as for @{const raise'exception}
 we provide a different definition of @{const SignalTLBException} that always returns @{typ unit}.\<close>

definition SignalTLBException where
  "SignalTLBException \<equiv> 
   \<lambda>v. case v of (v1, v2) \<Rightarrow> 
       bind (SignalTLBException_internal v2) (\<lambda>_. SignalException v1)"

lemma bind_bind_return:
  shows "bind (bind m (\<lambda>v. return (x v))) n =
         bind m (\<lambda>v. n (x v))" 
unfolding bind_associativity
by simp

lemma SignalTLBException_simp [alt_def_simp]:
  shows "CHERI_Monadic_p256.SignalTLBException = 
         (\<lambda>ex. bind (SignalTLBException ex) 
                    (\<lambda>_. bind (next_unknown ''tlb-translation'')
                    (\<lambda>v. return (undefined v))))"
unfolding Let_def
  SignalTLBException_def
  CHERI_Monadic_p256.SignalTLBException_def
by (auto simp: bind_associativity)

schematic_goal SignalTLBException_alt_def:
  shows "SignalTLBException = ?x"
unfolding SignalTLBException_def
unfolding CHERI_Monadic_p256.SignalTLBException_def Let_def
by compute_alt_def

(* Code generation - end override *)

schematic_goal CheckSegment_alt_def:
  shows "CheckSegment = ?x"
unfolding CheckSegment_def
unfolding Let_def
by compute_alt_def

schematic_goal check_cca_alt_def:
  shows "check_cca = ?x"
unfolding check_cca_def
unfolding Let_def
by compute_alt_def

schematic_goal TLB_next_random_alt_def:
  shows "TLB_next_random = ?x"
unfolding TLB_next_random_def
unfolding Let_def
by compute_alt_def

schematic_goal AddressTranslation_alt_def:
  shows "AddressTranslation = ?x"
unfolding AddressTranslation_def
unfolding Let_def
by compute_alt_def

schematic_goal CP0TLBEntry_alt_def:
  shows "CP0TLBEntry = ?x"
unfolding CP0TLBEntry_def
unfolding Let_def
by compute_alt_def

schematic_goal SignalTLBCapException_alt_def:
  shows "SignalTLBCapException = ?x"
unfolding SignalTLBCapException_def
unfolding Let_def
by compute_alt_def

schematic_goal printMemStats_alt_def:
  shows "printMemStats = ?x"
unfolding printMemStats_def
unfolding Let_def
by compute_alt_def

schematic_goal initMemStats_alt_def:
  shows "initMemStats = ?x"
unfolding initMemStats_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_data_reads_updt_alt_def:
  shows "stats_data_reads_updt = ?x"
unfolding stats_data_reads_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_data_writes_updt_alt_def:
  shows "stats_data_writes_updt = ?x"
unfolding stats_data_writes_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_inst_reads_updt_alt_def:
  shows "stats_inst_reads_updt = ?x"
unfolding stats_inst_reads_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_valid_cap_reads_updt_alt_def:
  shows "stats_valid_cap_reads_updt = ?x"
unfolding stats_valid_cap_reads_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_valid_cap_writes_updt_alt_def:
  shows "stats_valid_cap_writes_updt = ?x"
unfolding stats_valid_cap_writes_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_invalid_cap_reads_updt_alt_def:
  shows "stats_invalid_cap_reads_updt = ?x"
unfolding stats_invalid_cap_reads_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal stats_invalid_cap_writes_updt_alt_def:
  shows "stats_invalid_cap_writes_updt = ?x"
unfolding stats_invalid_cap_writes_updt_def
unfolding Let_def
by compute_alt_def

schematic_goal MEM_alt_def:
  shows "MEM = ?x"
unfolding MEM_def
unfolding Let_def
by compute_alt_def

schematic_goal write'MEM_alt_def:
  shows "write'MEM = ?x"
unfolding write'MEM_def
unfolding Let_def
by compute_alt_def

schematic_goal InitMEM_alt_def:
  shows "InitMEM = ?x"
unfolding InitMEM_def
unfolding Let_def
by compute_alt_def

schematic_goal ReadData_alt_def:
  shows "ReadData = ?x"
unfolding ReadData_def
unfolding Let_def
by compute_alt_def

schematic_goal WriteData_alt_def:
  shows "WriteData = ?x"
unfolding WriteData_def
unfolding Let_def
by compute_alt_def

schematic_goal ReadInst_alt_def:
  shows "ReadInst = ?x"
unfolding ReadInst_def
unfolding Let_def
by compute_alt_def

schematic_goal ReadCap_alt_def:
  shows "ReadCap = ?x"
unfolding ReadCap_def
unfolding Let_def
by compute_alt_def

schematic_goal WriteCap_alt_def:
  shows "WriteCap = ?x"
unfolding WriteCap_def
unfolding Let_def
by compute_alt_def

schematic_goal AdjustEndian_alt_def:
  shows "AdjustEndian = ?x"
unfolding AdjustEndian_def
unfolding Let_def
by compute_alt_def

schematic_goal initMemAccessStats_alt_def:
  shows "initMemAccessStats = ?x"
unfolding initMemAccessStats_def
unfolding Let_def
by compute_alt_def

schematic_goal printMemAccessStats_alt_def:
  shows "printMemAccessStats = ?x"
unfolding printMemAccessStats_def
unfolding Let_def
by compute_alt_def

schematic_goal watchForLoad_alt_def [simp]:
  shows "watchForLoad = ?x"
unfolding watchForLoad_def
unfolding Let_def
by compute_alt_def

schematic_goal watchForCapLoad_alt_def [simp]:
  shows "watchForCapLoad = ?x"
unfolding watchForCapLoad_def
unfolding Let_def
by compute_alt_def

schematic_goal watchForStore_alt_def [simp]:
  shows "watchForStore = ?x"
unfolding watchForStore_def
unfolding Let_def
by compute_alt_def

schematic_goal watchForCapStore_alt_def [simp]:
  shows "watchForCapStore = ?x"
unfolding watchForCapStore_def
unfolding Let_def
by compute_alt_def

schematic_goal getVirtualAddress_alt_def:
  shows "getVirtualAddress = ?x"
unfolding getVirtualAddress_def
unfolding Let_def
by compute_alt_def

schematic_goal LoadMemoryCap_alt_def:
  shows "LoadMemoryCap = ?x"
unfolding LoadMemoryCap_def
unfolding Let_def
by compute_alt_def

schematic_goal LoadMemory_alt_def:
  shows "LoadMemory = ?x"
unfolding LoadMemory_def
unfolding Let_def
by compute_alt_def

schematic_goal LoadCap_alt_def:
  shows "LoadCap = ?x"
unfolding LoadCap_def
unfolding Let_def
by compute_alt_def

schematic_goal StoreMemoryCap_alt_def:
  shows "StoreMemoryCap = ?x"
unfolding StoreMemoryCap_def
unfolding Let_def
by compute_alt_def

schematic_goal StoreMemory_alt_def:
  shows "StoreMemory = ?x"
unfolding StoreMemory_def
unfolding Let_def
by compute_alt_def

schematic_goal StoreCap_alt_def:
  shows "StoreCap = ?x"
unfolding StoreCap_def
unfolding Let_def
by compute_alt_def

schematic_goal Fetch_alt_def:
  shows "Fetch = ?x"
unfolding Fetch_def
unfolding Let_def
by compute_alt_def

schematic_goal CP0R_alt_def:
  shows "CP0R = ?x"
unfolding CP0R_def
unfolding Let_def
by compute_alt_def

schematic_goal write'CP0R_alt_def:
  shows "write'CP0R = ?x"
unfolding write'CP0R_def
unfolding Let_def
by compute_alt_def

schematic_goal resetStats_alt_def:
  shows "resetStats = ?x"
unfolding resetStats_def
unfolding Let_def
by compute_alt_def

schematic_goal dumpStats_alt_def [simp]:
  shows "dumpStats = ?x"
unfolding dumpStats_def
unfolding Let_def
by compute_alt_def

schematic_goal HI_alt_def:
  shows "HI = ?x"
unfolding HI_def
unfolding Let_def
by compute_alt_def

schematic_goal write'HI_alt_def:
  shows "write'HI = ?x"
unfolding write'HI_def
unfolding Let_def
by compute_alt_def

schematic_goal LO_alt_def:
  shows "LO = ?x"
unfolding LO_def
unfolding Let_def
by compute_alt_def

schematic_goal write'LO_alt_def:
  shows "write'LO = ?x"
unfolding write'LO_def
unfolding Let_def
by compute_alt_def

schematic_goal mtc_alt_def:
  shows "mtc = ?x"
unfolding mtc_def
unfolding Let_def
by compute_alt_def

schematic_goal dmtc_alt_def:
  shows "dmtc = ?x"
unfolding dmtc_def
unfolding Let_def
by compute_alt_def

schematic_goal mfc_alt_def:
  shows "mfc = ?x"
unfolding mfc_def
unfolding Let_def
by compute_alt_def

schematic_goal dmfc_alt_def:
  shows "dmfc = ?x"
unfolding dmfc_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ADDI_alt_def:
  shows "dfn'ADDI = ?x"
unfolding dfn'ADDI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ADDIU_alt_def:
  shows "dfn'ADDIU = ?x"
unfolding dfn'ADDIU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DADDI_alt_def:
  shows "dfn'DADDI = ?x"
unfolding dfn'DADDI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DADDIU_alt_def:
  shows "dfn'DADDIU = ?x"
unfolding dfn'DADDIU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLTI_alt_def:
  shows "dfn'SLTI = ?x"
unfolding dfn'SLTI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLTIU_alt_def:
  shows "dfn'SLTIU = ?x"
unfolding dfn'SLTIU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ANDI_alt_def:
  shows "dfn'ANDI = ?x"
unfolding dfn'ANDI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ORI_alt_def:
  shows "dfn'ORI = ?x"
unfolding dfn'ORI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'XORI_alt_def:
  shows "dfn'XORI = ?x"
unfolding dfn'XORI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LUI_alt_def:
  shows "dfn'LUI = ?x"
unfolding dfn'LUI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ADD_alt_def:
  shows "dfn'ADD = ?x"
unfolding dfn'ADD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ADDU_alt_def:
  shows "dfn'ADDU = ?x"
unfolding dfn'ADDU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SUB_alt_def:
  shows "dfn'SUB = ?x"
unfolding dfn'SUB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SUBU_alt_def:
  shows "dfn'SUBU = ?x"
unfolding dfn'SUBU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DADD_alt_def:
  shows "dfn'DADD = ?x"
unfolding dfn'DADD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DADDU_alt_def:
  shows "dfn'DADDU = ?x"
unfolding dfn'DADDU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSUB_alt_def:
  shows "dfn'DSUB = ?x"
unfolding dfn'DSUB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSUBU_alt_def:
  shows "dfn'DSUBU = ?x"
unfolding dfn'DSUBU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLT_alt_def:
  shows "dfn'SLT = ?x"
unfolding dfn'SLT_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLTU_alt_def:
  shows "dfn'SLTU = ?x"
unfolding dfn'SLTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'AND_alt_def:
  shows "dfn'AND = ?x"
unfolding dfn'AND_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'OR_alt_def:
  shows "dfn'OR = ?x"
unfolding dfn'OR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'XOR_alt_def:
  shows "dfn'XOR = ?x"
unfolding dfn'XOR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'NOR_alt_def:
  shows "dfn'NOR = ?x"
unfolding dfn'NOR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MOVN_alt_def:
  shows "dfn'MOVN = ?x"
unfolding dfn'MOVN_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MOVZ_alt_def:
  shows "dfn'MOVZ = ?x"
unfolding dfn'MOVZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MADD_alt_def:
  shows "dfn'MADD = ?x"
unfolding dfn'MADD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MADDU_alt_def:
  shows "dfn'MADDU = ?x"
unfolding dfn'MADDU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MSUB_alt_def:
  shows "dfn'MSUB = ?x"
unfolding dfn'MSUB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MSUBU_alt_def:
  shows "dfn'MSUBU = ?x"
unfolding dfn'MSUBU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MUL_alt_def:
  shows "dfn'MUL = ?x"
unfolding dfn'MUL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MULT_alt_def:
  shows "dfn'MULT = ?x"
unfolding dfn'MULT_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MULTU_alt_def:
  shows "dfn'MULTU = ?x"
unfolding dfn'MULTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DMULT_alt_def:
  shows "dfn'DMULT = ?x"
unfolding dfn'DMULT_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DMULTU_alt_def:
  shows "dfn'DMULTU = ?x"
unfolding dfn'DMULTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DIV_alt_def:
  shows "dfn'DIV = ?x"
unfolding dfn'DIV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DIVU_alt_def:
  shows "dfn'DIVU = ?x"
unfolding dfn'DIVU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DDIV_alt_def:
  shows "dfn'DDIV = ?x"
unfolding dfn'DDIV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DDIVU_alt_def:
  shows "dfn'DDIVU = ?x"
unfolding dfn'DDIVU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MFHI_alt_def:
  shows "dfn'MFHI = ?x"
unfolding dfn'MFHI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MFLO_alt_def:
  shows "dfn'MFLO = ?x"
unfolding dfn'MFLO_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MTHI_alt_def:
  shows "dfn'MTHI = ?x"
unfolding dfn'MTHI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MTLO_alt_def:
  shows "dfn'MTLO = ?x"
unfolding dfn'MTLO_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLL_alt_def:
  shows "dfn'SLL = ?x"
unfolding dfn'SLL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SRL_alt_def:
  shows "dfn'SRL = ?x"
unfolding dfn'SRL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SRA_alt_def:
  shows "dfn'SRA = ?x"
unfolding dfn'SRA_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SLLV_alt_def:
  shows "dfn'SLLV = ?x"
unfolding dfn'SLLV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SRLV_alt_def:
  shows "dfn'SRLV = ?x"
unfolding dfn'SRLV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SRAV_alt_def:
  shows "dfn'SRAV = ?x"
unfolding dfn'SRAV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSLL_alt_def:
  shows "dfn'DSLL = ?x"
unfolding dfn'DSLL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRL_alt_def:
  shows "dfn'DSRL = ?x"
unfolding dfn'DSRL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRA_alt_def:
  shows "dfn'DSRA = ?x"
unfolding dfn'DSRA_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSLLV_alt_def:
  shows "dfn'DSLLV = ?x"
unfolding dfn'DSLLV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRLV_alt_def:
  shows "dfn'DSRLV = ?x"
unfolding dfn'DSRLV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRAV_alt_def:
  shows "dfn'DSRAV = ?x"
unfolding dfn'DSRAV_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSLL32_alt_def:
  shows "dfn'DSLL32 = ?x"
unfolding dfn'DSLL32_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRL32_alt_def:
  shows "dfn'DSRL32 = ?x"
unfolding dfn'DSRL32_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DSRA32_alt_def:
  shows "dfn'DSRA32 = ?x"
unfolding dfn'DSRA32_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TGE_alt_def:
  shows "dfn'TGE = ?x"
unfolding dfn'TGE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TGEU_alt_def:
  shows "dfn'TGEU = ?x"
unfolding dfn'TGEU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLT_alt_def:
  shows "dfn'TLT = ?x"
unfolding dfn'TLT_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLTU_alt_def:
  shows "dfn'TLTU = ?x"
unfolding dfn'TLTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TEQ_alt_def:
  shows "dfn'TEQ = ?x"
unfolding dfn'TEQ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TNE_alt_def:
  shows "dfn'TNE = ?x"
unfolding dfn'TNE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TGEI_alt_def:
  shows "dfn'TGEI = ?x"
unfolding dfn'TGEI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TGEIU_alt_def:
  shows "dfn'TGEIU = ?x"
unfolding dfn'TGEIU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLTI_alt_def:
  shows "dfn'TLTI = ?x"
unfolding dfn'TLTI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLTIU_alt_def:
  shows "dfn'TLTIU = ?x"
unfolding dfn'TLTIU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TEQI_alt_def:
  shows "dfn'TEQI = ?x"
unfolding dfn'TEQI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TNEI_alt_def:
  shows "dfn'TNEI = ?x"
unfolding dfn'TNEI_def
unfolding Let_def
by compute_alt_def

schematic_goal loadByte_alt_def:
  shows "loadByte = ?x"
unfolding loadByte_def
unfolding Let_def
by compute_alt_def

schematic_goal loadHalf_alt_def:
  shows "loadHalf = ?x"
unfolding loadHalf_def
unfolding Let_def
by compute_alt_def

schematic_goal loadWord_alt_def:
  shows "loadWord = ?x"
unfolding loadWord_def
unfolding Let_def
by compute_alt_def

schematic_goal loadDoubleword_alt_def:
  shows "loadDoubleword = ?x"
unfolding loadDoubleword_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LB_alt_def:
  shows "dfn'LB = ?x"
unfolding dfn'LB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LBU_alt_def:
  shows "dfn'LBU = ?x"
unfolding dfn'LBU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LH_alt_def:
  shows "dfn'LH = ?x"
unfolding dfn'LH_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LHU_alt_def:
  shows "dfn'LHU = ?x"
unfolding dfn'LHU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LW_alt_def:
  shows "dfn'LW = ?x"
unfolding dfn'LW_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LWU_alt_def:
  shows "dfn'LWU = ?x"
unfolding dfn'LWU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LL_alt_def:
  shows "dfn'LL = ?x"
unfolding dfn'LL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LD_alt_def:
  shows "dfn'LD = ?x"
unfolding dfn'LD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LLD_alt_def:
  shows "dfn'LLD = ?x"
unfolding dfn'LLD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LWL_alt_def:
  shows "dfn'LWL = ?x"
unfolding dfn'LWL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LWR_alt_def:
  shows "dfn'LWR = ?x"
unfolding dfn'LWR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LDL_alt_def:
  shows "dfn'LDL = ?x"
unfolding dfn'LDL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'LDR_alt_def:
  shows "dfn'LDR = ?x"
unfolding dfn'LDR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SB_alt_def:
  shows "dfn'SB = ?x"
unfolding dfn'SB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SH_alt_def:
  shows "dfn'SH = ?x"
unfolding dfn'SH_def
unfolding Let_def
by compute_alt_def

schematic_goal storeWord_alt_def:
  shows "storeWord = ?x"
unfolding storeWord_def
unfolding Let_def
by compute_alt_def

schematic_goal storeDoubleword_alt_def:
  shows "storeDoubleword = ?x"
unfolding storeDoubleword_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SW_alt_def:
  shows "dfn'SW = ?x"
unfolding dfn'SW_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SD_alt_def:
  shows "dfn'SD = ?x"
unfolding dfn'SD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SC_alt_def:
  shows "dfn'SC = ?x"
unfolding dfn'SC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SCD_alt_def:
  shows "dfn'SCD = ?x"
unfolding dfn'SCD_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SWL_alt_def:
  shows "dfn'SWL = ?x"
unfolding dfn'SWL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SWR_alt_def:
  shows "dfn'SWR = ?x"
unfolding dfn'SWR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SDL_alt_def:
  shows "dfn'SDL = ?x"
unfolding dfn'SDL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SDR_alt_def:
  shows "dfn'SDR = ?x"
unfolding dfn'SDR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BREAK_alt_def:
  shows "dfn'BREAK = ?x"
unfolding dfn'BREAK_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'SYSCALL_alt_def:
  shows "dfn'SYSCALL = ?x"
unfolding dfn'SYSCALL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MTC0_alt_def:
  shows "dfn'MTC0 = ?x"
unfolding dfn'MTC0_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DMTC0_alt_def:
  shows "dfn'DMTC0 = ?x"
unfolding dfn'DMTC0_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'MFC0_alt_def:
  shows "dfn'MFC0 = ?x"
unfolding dfn'MFC0_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DMFC0_alt_def:
  shows "dfn'DMFC0 = ?x"
unfolding dfn'DMFC0_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'J_alt_def:
  shows "dfn'J = ?x"
unfolding dfn'J_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'JAL_alt_def:
  shows "dfn'JAL = ?x"
unfolding dfn'JAL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'JALR_alt_def:
  shows "dfn'JALR = ?x"
unfolding dfn'JALR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'JR_alt_def:
  shows "dfn'JR = ?x"
unfolding dfn'JR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BEQ_alt_def:
  shows "dfn'BEQ = ?x"
unfolding dfn'BEQ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BNE_alt_def:
  shows "dfn'BNE = ?x"
unfolding dfn'BNE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLEZ_alt_def:
  shows "dfn'BLEZ = ?x"
unfolding dfn'BLEZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGTZ_alt_def:
  shows "dfn'BGTZ = ?x"
unfolding dfn'BGTZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLTZ_alt_def:
  shows "dfn'BLTZ = ?x"
unfolding dfn'BLTZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGEZ_alt_def:
  shows "dfn'BGEZ = ?x"
unfolding dfn'BGEZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLTZAL_alt_def:
  shows "dfn'BLTZAL = ?x"
unfolding dfn'BLTZAL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGEZAL_alt_def:
  shows "dfn'BGEZAL = ?x"
unfolding dfn'BGEZAL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BEQL_alt_def:
  shows "dfn'BEQL = ?x"
unfolding dfn'BEQL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BNEL_alt_def:
  shows "dfn'BNEL = ?x"
unfolding dfn'BNEL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLEZL_alt_def:
  shows "dfn'BLEZL = ?x"
unfolding dfn'BLEZL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGTZL_alt_def:
  shows "dfn'BGTZL = ?x"
unfolding dfn'BGTZL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLTZL_alt_def:
  shows "dfn'BLTZL = ?x"
unfolding dfn'BLTZL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGEZL_alt_def:
  shows "dfn'BGEZL = ?x"
unfolding dfn'BGEZL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BLTZALL_alt_def:
  shows "dfn'BLTZALL = ?x"
unfolding dfn'BLTZALL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'BGEZALL_alt_def:
  shows "dfn'BGEZALL = ?x"
unfolding dfn'BGEZALL_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'RDHWR_alt_def:
  shows "dfn'RDHWR = ?x"
unfolding dfn'RDHWR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CACHE_alt_def:
  shows "dfn'CACHE = ?x"
unfolding dfn'CACHE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ReservedInstruction_alt_def:
  shows "dfn'ReservedInstruction = ?x"
unfolding dfn'ReservedInstruction_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'Unpredictable_alt_def:
  shows "dfn'Unpredictable = ?x"
unfolding dfn'Unpredictable_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLBP_alt_def:
  shows "dfn'TLBP = ?x"
unfolding dfn'TLBP_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLBR_alt_def:
  shows "dfn'TLBR = ?x"
unfolding dfn'TLBR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLBWI_alt_def:
  shows "dfn'TLBWI = ?x"
unfolding dfn'TLBWI_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'TLBWR_alt_def:
  shows "dfn'TLBWR = ?x"
unfolding dfn'TLBWR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'COP1_alt_def:
  shows "dfn'COP1 = ?x"
unfolding dfn'COP1_def
unfolding Let_def
by compute_alt_def

schematic_goal watchOOB_alt_def [simp]:
  shows "watchOOB = ?x"
unfolding watchOOB_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'DumpCapReg_alt_def [simp]:
  shows "dfn'DumpCapReg = ?x"
unfolding dfn'DumpCapReg_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetBase_alt_def:
  shows "dfn'CGetBase = ?x"
unfolding dfn'CGetBase_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetOffset_alt_def:
  shows "dfn'CGetOffset = ?x"
unfolding dfn'CGetOffset_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetLen_alt_def:
  shows "dfn'CGetLen = ?x"
unfolding dfn'CGetLen_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetTag_alt_def:
  shows "dfn'CGetTag = ?x"
unfolding dfn'CGetTag_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetSealed_alt_def:
  shows "dfn'CGetSealed = ?x"
unfolding dfn'CGetSealed_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetPerm_alt_def:
  shows "dfn'CGetPerm = ?x"
unfolding dfn'CGetPerm_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetType_alt_def:
  shows "dfn'CGetType = ?x"
unfolding dfn'CGetType_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetAddr_alt_def:
  shows "dfn'CGetAddr = ?x"
unfolding dfn'CGetAddr_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetPCC_alt_def:
  shows "dfn'CGetPCC = ?x"
unfolding dfn'CGetPCC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetPCCSetOffset_alt_def:
  shows "dfn'CGetPCCSetOffset = ?x"
unfolding dfn'CGetPCCSetOffset_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CGetCause_alt_def:
  shows "dfn'CGetCause = ?x"
unfolding dfn'CGetCause_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSetCause_alt_def:
  shows "dfn'CSetCause = ?x"
unfolding dfn'CSetCause_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CIncOffset_alt_def:
  shows "dfn'CIncOffset = ?x"
unfolding dfn'CIncOffset_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CIncOffsetImmediate_alt_def:
  shows "dfn'CIncOffsetImmediate = ?x"
unfolding dfn'CIncOffsetImmediate_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSetBounds_alt_def:
  shows "dfn'CSetBounds = ?x"
unfolding dfn'CSetBounds_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSetBoundsExact_alt_def:
  shows "dfn'CSetBoundsExact = ?x"
unfolding dfn'CSetBoundsExact_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSetBoundsImmediate_alt_def:
  shows "dfn'CSetBoundsImmediate = ?x"
unfolding dfn'CSetBoundsImmediate_def
unfolding Let_def
by compute_alt_def

schematic_goal ClearRegs_alt_def:
  shows "ClearRegs = ?x"
unfolding ClearRegs_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ClearLo_alt_def:
  shows "dfn'ClearLo = ?x"
unfolding dfn'ClearLo_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'ClearHi_alt_def:
  shows "dfn'ClearHi = ?x"
unfolding dfn'ClearHi_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CClearLo_alt_def:
  shows "dfn'CClearLo = ?x"
unfolding dfn'CClearLo_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CClearHi_alt_def:
  shows "dfn'CClearHi = ?x"
unfolding dfn'CClearHi_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CClearTag_alt_def:
  shows "dfn'CClearTag = ?x"
unfolding dfn'CClearTag_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CAndPerm_alt_def:
  shows "dfn'CAndPerm = ?x"
unfolding dfn'CAndPerm_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSetOffset_alt_def:
  shows "dfn'CSetOffset = ?x"
unfolding dfn'CSetOffset_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSub_alt_def:
  shows "dfn'CSub = ?x"
unfolding dfn'CSub_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CCheckPerm_alt_def:
  shows "dfn'CCheckPerm = ?x"
unfolding dfn'CCheckPerm_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CCheckType_alt_def:
  shows "dfn'CCheckType = ?x"
unfolding dfn'CCheckType_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CFromPtr_alt_def:
  shows "dfn'CFromPtr = ?x"
unfolding dfn'CFromPtr_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CToPtr_alt_def:
  shows "dfn'CToPtr = ?x"
unfolding dfn'CToPtr_def
unfolding Let_def
by compute_alt_def

schematic_goal CPtrCmp_alt_def:
  shows "CPtrCmp = ?x"
unfolding CPtrCmp_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CEQ_alt_def:
  shows "dfn'CEQ = ?x"
unfolding dfn'CEQ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CNE_alt_def:
  shows "dfn'CNE = ?x"
unfolding dfn'CNE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLT_alt_def:
  shows "dfn'CLT = ?x"
unfolding dfn'CLT_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLE_alt_def:
  shows "dfn'CLE = ?x"
unfolding dfn'CLE_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLTU_alt_def:
  shows "dfn'CLTU = ?x"
unfolding dfn'CLTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLEU_alt_def:
  shows "dfn'CLEU = ?x"
unfolding dfn'CLEU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CEXEQ_alt_def:
  shows "dfn'CEXEQ = ?x"
unfolding dfn'CEXEQ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CNEXEQ_alt_def:
  shows "dfn'CNEXEQ = ?x"
unfolding dfn'CNEXEQ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CBTU_alt_def:
  shows "dfn'CBTU = ?x"
unfolding dfn'CBTU_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CBTS_alt_def:
  shows "dfn'CBTS = ?x"
unfolding dfn'CBTS_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CBEZ_alt_def:
  shows "dfn'CBEZ = ?x"
unfolding dfn'CBEZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CBNZ_alt_def:
  shows "dfn'CBNZ = ?x"
unfolding dfn'CBNZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSC_alt_def:
  shows "dfn'CSC = ?x"
unfolding dfn'CSC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLC_alt_def:
  shows "dfn'CLC = ?x"
unfolding dfn'CLC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLoad_alt_def:
  shows "dfn'CLoad = ?x"
unfolding dfn'CLoad_def
unfolding Let_def
by compute_alt_def

schematic_goal store_alt_def:
  shows "store = ?x"
unfolding store_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CStore_alt_def:
  shows "dfn'CStore = ?x"
unfolding dfn'CStore_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLLC_alt_def:
  shows "dfn'CLLC = ?x"
unfolding dfn'CLLC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CLLx_alt_def:
  shows "dfn'CLLx = ?x"
unfolding dfn'CLLx_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSCC_alt_def:
  shows "dfn'CSCC = ?x"
unfolding dfn'CSCC_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSCx_alt_def:
  shows "dfn'CSCx = ?x"
unfolding dfn'CSCx_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CMOVN_alt_def:
  shows "dfn'CMOVN = ?x"
unfolding dfn'CMOVN_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CMOVZ_alt_def:
  shows "dfn'CMOVZ = ?x"
unfolding dfn'CMOVZ_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CMove_alt_def:
  shows "dfn'CMove = ?x"
unfolding dfn'CMove_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CTestSubset_alt_def:
  shows "dfn'CTestSubset = ?x"
unfolding dfn'CTestSubset_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CBuildCap_alt_def:
  shows "dfn'CBuildCap = ?x"
unfolding dfn'CBuildCap_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CCopyType_alt_def:
  shows "dfn'CCopyType = ?x"
unfolding dfn'CCopyType_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CJR_alt_def:
  shows "dfn'CJR = ?x"
unfolding dfn'CJR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CJALR_alt_def:
  shows "dfn'CJALR = ?x"
unfolding dfn'CJALR_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CSeal_alt_def:
  shows "dfn'CSeal = ?x"
unfolding dfn'CSeal_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CUnseal_alt_def:
  shows "dfn'CUnseal = ?x"
unfolding dfn'CUnseal_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CCall_alt_def:
  shows "dfn'CCall = ?x"
unfolding dfn'CCall_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CCallFast_alt_def:
  shows "dfn'CCallFast = ?x"
unfolding dfn'CCallFast_def
unfolding Let_def
by compute_alt_def

schematic_goal special_register_accessible_alt_def:
  shows "special_register_accessible = ?x"
unfolding special_register_accessible_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CReadHwr_alt_def:
  shows "dfn'CReadHwr = ?x"
unfolding dfn'CReadHwr_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CWriteHwr_alt_def:
  shows "dfn'CWriteHwr = ?x"
unfolding dfn'CWriteHwr_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'CReturn_alt_def:
  shows "dfn'CReturn = ?x"
unfolding dfn'CReturn_def
unfolding Let_def
by compute_alt_def

schematic_goal dfn'UnknownCapInstruction_alt_def:
  shows "dfn'UnknownCapInstruction = ?x"
unfolding dfn'UnknownCapInstruction_def
unfolding Let_def
by compute_alt_def

schematic_goal log_instruction_alt_def:
  shows "log_instruction = ?x"
unfolding log_instruction_def
unfolding Let_def
by compute_alt_def

schematic_goal Run_alt_def:
  shows "Run = ?x"
unfolding Run_def
unfolding Let_def
by compute_alt_def

(* Code generation - override - Next *)

schematic_goal Next_alt_def_aux:
  shows "Next = ?x"
unfolding Next_def
unfolding Let_def
by compute_alt_def

definition TakeBranch :: "state \<Rightarrow> unit \<times> state" where
  "TakeBranch \<equiv>
   bind (read_state getBranchDelay)
        (\<lambda>v. bind (read_state getBranchTo)
        (\<lambda>a. bind (read_state BranchDelayPCC)
        (\<lambda>aa. bind (read_state BranchToPCC)
        (\<lambda>aaa. (case v of None \<Rightarrow> 
                 (case a of None \<Rightarrow> 
                   (case aa of None \<Rightarrow> 
                     (case aaa of None \<Rightarrow> 
                       bind (read_state getExceptionSignalled)
                            (\<lambda>v. if \<not> v 
                                 then bind (read_state getPC)
                                           (\<lambda>v. update_state (setPC (v + 4)))
                                 else return ())
                     | Some a \<Rightarrow> 
                       bind (update_state (BranchDelayPCC_update (\<lambda>_. Some a)))
                            (\<lambda>_. bind (update_state (BranchToPCC_update Map.empty))
                            (\<lambda>_. bind (read_state getPC) 
                            (\<lambda>v. update_state (setPC (v + 4))))))
                   | Some (addr, cap) \<Rightarrow> 
                     (case aaa of None \<Rightarrow>
                       bind (update_state (BranchDelayPCC_update Map.empty)) 
                            (\<lambda>_. bind (update_state (setPC addr)) 
                            (\<lambda>_. write'PCC cap))
                     | Some aa \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch'')))
                 | Some addr \<Rightarrow> 
                   (case aa of None \<Rightarrow> 
                     (case aaa of None \<Rightarrow> 
                       bind (update_state (setBranchDelay (Some addr)))
                            (\<lambda>_. bind (update_state (setBranchTo None)) 
                            (\<lambda>_. bind (read_state getPC) 
                            (\<lambda>v. update_state (setPC (v + 4)))))
                     | Some a \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch''))
                   | Some ab \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch'')))
               | Some addr \<Rightarrow> 
                 (case a of None \<Rightarrow> 
                   (case aa of None \<Rightarrow> 
                     (case aaa of None \<Rightarrow> 
                       bind (update_state (setBranchDelay None)) 
                            (\<lambda>_. update_state (setPC addr))
                     | Some a \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch''))
                   | Some ab \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch''))
                 | Some ab \<Rightarrow> 
                       raise'exception (UNPREDICTABLE ''Branch follows branch'')))))))" 

lemma Next_alt_def:
  shows "Next =
         bind (update_state (currentInst_update Map.empty))
              (\<lambda>_. bind Fetch 
              (\<lambda>v. bind (update_state (currentInst_update (\<lambda>_. v)))
              (\<lambda>_. bind (read_state currentInst)
              (\<lambda>v. bind (case v of None \<Rightarrow> return () | Some w \<Rightarrow> Run (Decode w))
              (\<lambda>_. bind TakeBranch
              (\<lambda>_. bind (update_state (setExceptionSignalled False))
              (\<lambda>_. bind (read_state getCP0Count) 
              (\<lambda>b. bind (update_state (setCP0Count (b + 1)))
              (\<lambda>_. bind (read_state currentInst) 
              (\<lambda>v. update_state (lastInst_update (\<lambda>_. v))))))))))))"
unfolding Next_alt_def_aux TakeBranch_def
by (simp add: bind_associativity)

(* Code generation - end override *)

(* Code generation - end *)

(*<*)
end
(*>*)