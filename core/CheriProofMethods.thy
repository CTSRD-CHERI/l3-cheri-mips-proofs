(*<*)

(* Author: Kyndylan Nienhuis *)

theory CheriProofMethods

imports 
  "CHERI-alt.CheriAltDefs"
begin

(*>*)
section \<open>Commutativity\<close>

subsection \<open>Definition of commutativity\<close>

definition Commute where
  "Commute m n \<equiv>
   \<forall>s. StatePart m (StatePart n s) = StatePart n (StatePart m s) \<and>
       ValuePart m (StatePart n s) = ValuePart m s \<and>
       ValuePart n (StatePart m s) = ValuePart n s"

lemma CommuteI [intro]:
  assumes "\<And>s. StatePart m (StatePart n s) = StatePart n (StatePart m s)"
      and "\<And>s. ValuePart m (StatePart n s) = ValuePart m s"
      and "\<And>s. ValuePart n (StatePart m s) = ValuePart n s"
  shows "Commute m n"
using assms
unfolding Commute_def
by simp

lemma CommuteE [elim!]:
  assumes "Commute m n"
  shows "StatePart m (StatePart n s) = StatePart n (StatePart m s)"
    and "ValuePart m (StatePart n s) = ValuePart m s"
    and "ValuePart n (StatePart m s) = ValuePart n s"
using assms
unfolding Commute_def
by simp_all

text \<open>Lemmas with the attribute \<open>Commute_compositeI\<close> that we define below are lemmas that reduce
@{term "Commute m n"} to @{term "Commute m\<^sub>i n"} where \<open>m\<^sub>i\<close> are components of \<open>m\<close>. Examples are
lemmas that decompose @{const bind} and @{const foreach_loop} into their arguments, or CHERI
definitions into their dependencies.\<close>

named_theorems Commute_compositeI

lemma Commute_is_symmetric:
  shows "Commute m n = Commute n m"
unfolding Commute_def 
by auto

lemma Commute_returnI [intro!, Commute_compositeI, simp]:
  shows "Commute (return x) m"
unfolding Commute_def
by auto

lemma Commute_read_stateI [intro]:
  assumes "\<And>s. f (StatePart m s) = f s"
  shows "Commute (read_state f) m"
using assms
unfolding Commute_def
by auto

lemma Commute_read_stateE [elim!]:
  assumes "Commute (read_state f) m"
  shows "f (StatePart m s) = f s"
using assms
unfolding Commute_def
by auto

lemma Commute_read_state_read_stateI [intro!, simp]:
  shows "Commute (read_state f) (read_state g)"
unfolding Commute_def
by auto

lemma Commute_read_state_update_stateI [intro]:
  assumes "\<And>s. f (g s) = f s"
  shows "Commute (read_state f) (update_state g)"
using assms
unfolding Commute_def
by auto

lemma Commute_read_state_update_stateE [elim!]:
  assumes "Commute (read_state f) (update_state g)"
  shows "f (g s) = f s"
using assms
unfolding Commute_def
by simp

lemma Commute_update_state_read_stateI [intro]:
  assumes "\<And>s. g (f s) = g s"
  shows "Commute (update_state f) (read_state g)"
using assms
unfolding Commute_def
by auto

lemma Commute_update_state_read_stateE [elim!]:
  assumes "Commute (update_state f) (read_state g)"
  shows "g (f s) = g s"
using assms
unfolding Commute_def
by simp

lemma Commute_update_state_update_stateI [intro]:
  assumes "\<And>s. f (g s) = g (f s)"
  shows "Commute (update_state f) (update_state g)"
using assms
unfolding Commute_def
by auto

lemma Commute_update_state_update_stateE [elim!]:
  assumes "Commute (update_state f) (update_state g)"
  shows "f (g s) = g (f s)"
using assms
unfolding Commute_def
by simp

lemma Commute_read_state_ValuePart [elim!]:
  assumes "Commute m n"
  shows "Commute (read_state (ValuePart m)) n"
using assms
unfolding Commute_def
by auto

lemma Commute_update_state_StatePart [elim!]:
  assumes "Commute m n"
  shows "Commute (update_state (StatePart m)) n"
using assms
unfolding Commute_def
by auto

lemma Commute_bindI [intro, Commute_compositeI]:
  assumes "\<And>a. Commute (n a) k"
      and "Commute m k"
  shows "Commute (bind m n) k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_foreach_loopI [intro, Commute_compositeI]:
  assumes "\<And>a. Commute (m a) n"
  shows "Commute (foreach_loop (l, m)) n"
using assms
by (induct l) auto

lemma Commute_foreach_loop_aggI [intro, Commute_compositeI]:
  assumes "\<And>a v. Commute (m a v) n"
  shows "Commute (foreach_loop_agg l v m) n"
using assms
by (induct l arbitrary: v) auto

lemmas common_split = 
  if_splits(1)
  let_split
  Option.option.split
  List.list.split
  Product_Type.prod.split
  bool.split
  DataType.split

lemmas Commute_casesI [intro, Commute_compositeI] =
  all_split[where P="\<lambda>x. Commute x n", THEN iffD2] for n

lemma Commute_equals [intro, Commute_compositeI]:
  assumes "Commute m k"
      and "Commute m' k"
  shows "Commute (m =\<^sub>b m') k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_not [intro, Commute_compositeI]:
  assumes "Commute m k"
  shows "Commute (\<not>\<^sub>b m) k"
using assms
unfolding Commute_def
by simp

lemma Commute_conj [intro, Commute_compositeI]:
  assumes "Commute m k"
      and "Commute m' k"
  shows "Commute (m \<and>\<^sub>b m') k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_disj [intro, Commute_compositeI]:
  assumes "Commute m k"
      and "Commute m' k"
  shows "Commute (m \<or>\<^sub>b m') k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_All [intro, Commute_compositeI]:
  assumes "\<And>x. Commute (m x) k"
  shows "Commute (\<forall>\<^sub>bx. m x) k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_Ex [intro, Commute_compositeI]:
  assumes "\<And>x. Commute (m x) k"
  shows "Commute (\<exists>\<^sub>bx. m x) k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_read_state_func [intro, Commute_compositeI]:
  assumes "\<And>x. Commute (read_state (f x)) k"
  shows "Commute (read_state (\<lambda>s x. f x s)) k"
using assms
unfolding Commute_def
by (simp add: ValueAndStatePart_simp)

subsection \<open>Proving commutativity\<close>

lemmas Commute_swap = 
  Commute_is_symmetric[THEN iffD1]

method Commute uses intro = 
  assumption |
  solves \<open>simp\<close> |
  (rule Commute_compositeI intro; 
      (intro conjI impI allI)?; 
      Commute intro: intro) |
  (rule Commute_swap, 
      rule Commute_compositeI intro; 
      (intro conjI impI allI)?; 
      Commute intro: intro) |
  (rule Commute_read_state_ValuePart; 
      Commute intro: intro) |
  (rule Commute_swap, 
      rule Commute_read_state_ValuePart; 
      Commute intro: intro) |
  (rule Commute_update_state_StatePart; 
      Commute intro: intro) |
  (rule Commute_swap, 
      rule Commute_update_state_StatePart; 
      Commute intro: intro) |
  (rule Commute_read_state_read_stateI) |
  (rule Commute_read_state_update_stateI; 
      solves \<open>assumption | simp\<close>) |
  (rule Commute_update_state_read_stateI; 
      solves \<open>assumption | simp\<close>) |
  (rule Commute_update_state_update_stateI; 
      solves \<open>assumption | simp\<close>)

text \<open>Consider a lemma of the form @{term "Commute (update_state f) (update_state g)"} where \<open>f\<close> and
\<open>g\<close> update different fields of the state record. The @{method Commute} method proves this lemma by
invoking the simplifier on the goal @{term "f (g s) = g (f s)"}. The simplifier in turn proves that
statement by replacing it with @{term "h\<^sub>i (f (g s)) = h\<^sub>i (g (f s))"} where \<open>h\<^sub>i\<close> ranges over all
the ~50 record fields, which take a non-neglectable amount of time to simplify.

To speed up the @{method Commute} method we `cache' some of these lemmas by adding them to
\<open>Commute_compositeI\<close>. We chose the most used occurrences of \<open>f\<close> and \<open>g\<close>.\<close>

lemma Commute_BranchDelayPCC_update [Commute_compositeI]:
  shows "Commute (update_state (BranchDelayPCC_update v)) (update_state (BranchToPCC_update v1))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (c_capr_update v2))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (c_gpr_update v3))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (c_pcc_update v4))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (c_state_update v5))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (BranchDelayPCC_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_BranchToPCC_update [Commute_compositeI]:
  shows "Commute (update_state (BranchToPCC_update v)) (update_state (c_capr_update v2))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (c_gpr_update v3))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (c_pcc_update v4))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (c_state_update v5))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (BranchToPCC_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_c_capr_update [Commute_compositeI]:
  shows "Commute (update_state (c_capr_update v)) (update_state (c_gpr_update v3))"
    and "Commute (update_state (c_capr_update v)) (update_state (c_pcc_update v4))"
    and "Commute (update_state (c_capr_update v)) (update_state (c_state_update v5))"
    and "Commute (update_state (c_capr_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (c_capr_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (c_capr_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_c_gpr_update [Commute_compositeI]:
  shows "Commute (update_state (c_gpr_update v)) (update_state (c_pcc_update v4))"
    and "Commute (update_state (c_gpr_update v)) (update_state (c_state_update v5))"
    and "Commute (update_state (c_gpr_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (c_gpr_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (c_gpr_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_c_pcc_update [Commute_compositeI]:
  shows "Commute (update_state (c_pcc_update v)) (update_state (c_state_update v5))"
    and "Commute (update_state (c_pcc_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (c_pcc_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (c_pcc_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_c_state_update [Commute_compositeI]:
  shows "Commute (update_state (c_state_update v)) (update_state (exception_update v6))"
    and "Commute (update_state (c_state_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (c_state_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_exception_update [Commute_compositeI]:
  shows "Commute (update_state (exception_update v)) (update_state (the_MEM_update v7))"
    and "Commute (update_state (exception_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_the_MEM_update [Commute_compositeI]:
  shows "Commute (update_state (the_MEM_update v)) (update_state (unknown_counters_update v8))"
by Commute+

lemma Commute_c_BranchDelay_update [Commute_compositeI]:
  shows "Commute (update_state (c_state_update (c_BranchDelay_update v))) (update_state (c_state_update (c_BranchTo_update v1)))"
    and "Commute (update_state (c_state_update (c_BranchDelay_update v))) (update_state (c_state_update (c_CP0_update v2)))"
    and "Commute (update_state (c_state_update (c_BranchDelay_update v))) (update_state (c_state_update (c_PC_update v3)))"
    and "Commute (update_state (c_state_update (c_BranchDelay_update v))) (update_state (c_state_update (c_exceptionSignalled_update v4)))"
by Commute+

lemma Commute_c_BranchTo_update [Commute_compositeI]:
  shows "Commute (update_state (c_state_update (c_BranchTo_update v))) (update_state (c_state_update (c_CP0_update v2)))"
    and "Commute (update_state (c_state_update (c_BranchTo_update v))) (update_state (c_state_update (c_PC_update v3)))"
    and "Commute (update_state (c_state_update (c_BranchTo_update v))) (update_state (c_state_update (c_exceptionSignalled_update v4)))"
by Commute+

lemma Commute_c_CP0_update [Commute_compositeI]:
  shows "Commute (update_state (c_state_update (c_CP0_update v))) (update_state (c_state_update (c_PC_update v3)))"
    and "Commute (update_state (c_state_update (c_CP0_update v))) (update_state (c_state_update (c_exceptionSignalled_update v4)))"
by Commute+

lemma Commute_c_PC_update [Commute_compositeI]:
  shows "Commute (update_state (c_state_update (c_PC_update v))) (update_state (c_state_update (c_exceptionSignalled_update v4)))"
by Commute+

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemmas below is testing the proof method.\<close>

lemma
  assumes "\<And>a. Commute p (m a)"
      and "Commute p n"
      and "\<And>a. Commute p (n' a)"
  shows "Commute (if b then foreach_loop (l, m) else bind n n') p"
by (Commute intro: assms)

lemma
  assumes "\<And>a. Commute p (m a)"
      and "\<And>a. Commute p (n a)"
  shows "Commute (\<forall>\<^sub>bx. \<exists>\<^sub>by. m x =\<^sub>b n y) p"
by (Commute intro: assms)

subsection \<open>Finding dependencies\<close>

text \<open>Nested state components do not work very well with @{const read_state}. The following lemma
fixes that.\<close>

lemma Commute_read_state_nested [elim!]:
  assumes "Commute (read_state f) m"
  shows "Commute (read_state (\<lambda>s. g (f s))) m"
proof -
  have "Commute (bind (read_state f) (\<lambda>a. return (g a))) m"
    using assms by auto
  thus ?thesis
    unfolding monad_def Let_def
    by simp
qed

method Commute_find_dependencies_step uses intro elim =
  assumption |
  rule intro
       Commute_returnI
       impI
       conjI
       allI |
  rule Commute_bindI
       Commute_foreach_loopI
       Commute_foreach_loop_aggI
       Commute_casesI |
  erule elim
        Commute_read_state_nested

method Commute_find_dependencies uses intro elim = 
  (Commute_find_dependencies_step intro: intro elim: elim)+

subsection \<open>Commutativity lemmas\<close>

(* Code generation - start - commutativity *)

subsubsection \<open>@{const raise'exception}\<close>

lemma Commute_raise'exception [Commute_compositeI]:
  assumes "Commute (read_state exception) m"
      and "\<And>x. Commute (update_state (exception_update x)) m"
  shows "Commute (raise'exception v) m"
unfolding raise'exception_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const PIC_update}\<close>

lemma Commute_PIC_update [Commute_compositeI]:
  assumes "Commute (read_state PIC_config_regs) m"
      and "Commute (read_state PIC_ip_bits) m"
      and "Commute (read_state PIC_external_intrs) m"
      and "Commute (read_state (\<lambda>s. IP (Cause (c_CP0 (c_state s))))) m"
      and "Commute (read_state all_state) m"
      and "Commute (read_state procID) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Cause_update (IP_update x))))) m"
      and "\<And>x. Commute (update_state (all_state_update x)) m"
  shows "Commute (PIC_update v) m"
unfolding PIC_update_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const PIC_initialise}\<close>

lemma Commute_PIC_initialise [Commute_compositeI]:
  assumes "Commute (read_state PIC_base_address) m"
      and "Commute (read_state PIC_config_regs) m"
      and "Commute (read_state PIC_ip_bits) m"
      and "Commute (read_state PIC_external_intrs) m"
      and "Commute (read_state procID) m"
      and "\<And>x. Commute (update_state (PIC_base_address_update x)) m"
      and "\<And>x. Commute (update_state (PIC_config_regs_update x)) m"
      and "\<And>x. Commute (update_state (PIC_ip_bits_update x)) m"
      and "\<And>x. Commute (update_state (PIC_external_intrs_update x)) m"
      and "\<And>x. Commute (PIC_update x) m"
  shows "Commute (PIC_initialise v) m"
unfolding PIC_initialise_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const PIC_load}\<close>

lemma Commute_PIC_load [Commute_compositeI]:
  assumes "Commute (read_state PIC_base_address) m"
      and "Commute (read_state PIC_config_regs) m"
      and "Commute (read_state PIC_ip_bits) m"
      and "Commute (read_state PIC_external_intrs) m"
      and "Commute (next_unknown ''pic-data'') m"
  shows "Commute (PIC_load v) m"
unfolding PIC_load_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const PIC_store}\<close>

lemma Commute_PIC_store [Commute_compositeI]:
  assumes "Commute (read_state PIC_config_regs) m"
      and "Commute (read_state PIC_ip_bits) m"
      and "Commute (read_state PIC_base_address) m"
      and "\<And>x. Commute (update_state (PIC_config_regs_update x)) m"
      and "\<And>x. Commute (update_state (PIC_ip_bits_update x)) m"
      and "\<And>x. Commute (PIC_update x) m"
  shows "Commute (PIC_store v) m"
unfolding PIC_store_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_update_interrupt_bit}\<close>

lemma Commute_JTAG_UART_update_interrupt_bit [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "Commute (read_state PIC_external_intrs) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
      and "\<And>x. Commute (update_state (PIC_external_intrs_update x)) m"
      and "\<And>x. Commute (PIC_update x) m"
  shows "Commute (JTAG_UART_update_interrupt_bit v) m"
unfolding JTAG_UART_update_interrupt_bit_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_load}\<close>

lemma Commute_JTAG_UART_load [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
      and "\<And>x. Commute (JTAG_UART_update_interrupt_bit x) m"
  shows "Commute JTAG_UART_load m"
unfolding JTAG_UART_load_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_input}\<close>

lemma Commute_JTAG_UART_input [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
      and "\<And>x. Commute (JTAG_UART_update_interrupt_bit x) m"
      and "Commute JTAG_UART_load m"
  shows "Commute (JTAG_UART_input v) m"
unfolding JTAG_UART_input_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_store}\<close>

lemma Commute_JTAG_UART_store [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
      and "\<And>x. Commute (JTAG_UART_update_interrupt_bit x) m"
  shows "Commute (JTAG_UART_store v) m"
unfolding JTAG_UART_store_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_output}\<close>

lemma Commute_JTAG_UART_output [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
      and "\<And>x. Commute (JTAG_UART_update_interrupt_bit x) m"
  shows "Commute JTAG_UART_output m"
unfolding JTAG_UART_output_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const JTAG_UART_initialise}\<close>

lemma Commute_JTAG_UART_initialise [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "\<And>x. Commute (update_state (JTAG_UART_update x)) m"
  shows "Commute (JTAG_UART_initialise v) m"
unfolding JTAG_UART_initialise_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const gpr}\<close>

lemma Commute_gpr [Commute_compositeI]:
  assumes "Commute (read_state c_gpr) m"
  shows "Commute (gpr v) m"
unfolding gpr_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'gpr}\<close>

lemma Commute_write'gpr [Commute_compositeI]:
  assumes "Commute (read_state c_gpr) m"
      and "\<And>x. Commute (update_state (c_gpr_update x)) m"
  shows "Commute (write'gpr v) m"
unfolding write'gpr_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const GPR}\<close>

lemma Commute_GPR [Commute_compositeI]:
  assumes "\<And>x. Commute (gpr x) m"
  shows "Commute (GPR v) m"
unfolding GPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'GPR}\<close>

lemma Commute_write'GPR [Commute_compositeI]:
  assumes "\<And>x. Commute (write'gpr x) m"
  shows "Commute (write'GPR v) m"
unfolding write'GPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const UserMode}\<close>

lemma Commute_UserMode [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. KSU (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. EXL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. ERL (Status (c_CP0 (c_state s))))) m"
  shows "Commute UserMode m"
unfolding UserMode_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SupervisorMode}\<close>

lemma Commute_SupervisorMode [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. KSU (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. EXL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. ERL (Status (c_CP0 (c_state s))))) m"
  shows "Commute SupervisorMode m"
unfolding SupervisorMode_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const KernelMode}\<close>

lemma Commute_KernelMode [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. KSU (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. EXL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. ERL (Status (c_CP0 (c_state s))))) m"
  shows "Commute KernelMode m"
unfolding KernelMode_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const BigEndianMem}\<close>

lemma Commute_BigEndianMem [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. BE (Config (c_CP0 (c_state s))))) m"
  shows "Commute BigEndianMem m"
unfolding BigEndianMem_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const ReverseEndian}\<close>

lemma Commute_ReverseEndian [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. StatusRegister.RE (Status (c_CP0 (c_state s))))) m"
      and "Commute UserMode m"
  shows "Commute ReverseEndian m"
unfolding ReverseEndian_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const BigEndianCPU}\<close>

lemma Commute_BigEndianCPU [Commute_compositeI]:
  assumes "Commute BigEndianMem m"
      and "Commute ReverseEndian m"
  shows "Commute BigEndianCPU m"
unfolding BigEndianCPU_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CheckBranch}\<close>

lemma Commute_CheckBranch [Commute_compositeI]:
  assumes "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state (\<lambda>s. c_BranchDelay (c_state s))) m"
      and "\<And>x. Commute (raise'exception x) m"
  shows "Commute CheckBranch m"
unfolding CheckBranch_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const BranchNotTaken}\<close>

lemma Commute_BranchNotTaken [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_PC (c_state s))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_BranchTo_update x))) m"
      and "Commute CheckBranch m"
  shows "Commute BranchNotTaken m"
unfolding BranchNotTaken_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const BranchLikelyNotTaken}\<close>

lemma Commute_BranchLikelyNotTaken [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_PC (c_state s))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_PC_update x))) m"
      and "Commute CheckBranch m"
  shows "Commute BranchLikelyNotTaken m"
unfolding BranchLikelyNotTaken_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const initCoreStats}\<close>

lemma Commute_initCoreStats [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_state_update (c_CoreStats_update x))) m"
  shows "Commute initCoreStats m"
unfolding initCoreStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const printCoreStats}\<close>

lemma Commute_printCoreStats [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_CoreStats (c_state s))) m"
  shows "Commute printCoreStats m"
unfolding printCoreStats_alt_def
using assms
by - Commute_find_dependencies

(* Code generation - override - next_unknown *)

subsubsection \<open>@{const next_unknown}\<close>

lemma unknown_counter_update_Commutes [simp]:
  shows "(\<lambda>c. c(x := Suc (c x))) \<circ> (\<lambda>c. c(y := Suc (c y))) =
         (\<lambda>c. c(y := Suc (c y))) \<circ> (\<lambda>c. c(x := Suc (c x)))"
by force

lemma Commute_next_unknown [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. unknown_counters s v)) m"
      and "Commute (update_state (unknown_counters_update (\<lambda>c. c(v := Suc (c v))))) m"
  shows "Commute (next_unknown v) m"
proof -
  have "next_unknown v = 
        bind (read_state (\<lambda>s. (unknown_counters s v, v)))
             (\<lambda>a. bind (update_state (unknown_counters_update (\<lambda>c. c(v := Suc (c v))))) 
             (\<lambda>_. return a))"
    unfolding next_unknown_alt_def monad_def
    by auto
  thus ?thesis
    using assms
    by auto
qed

text \<open>The lemma below tests the proof method @{method Commute}.\<close>

lemma "Commute (next_unknown ''a'') (next_unknown ''b'')"
by Commute

(* Code generation - end override *)

subsubsection \<open>@{const PCC}\<close>

lemma Commute_PCC [Commute_compositeI]:
  assumes "Commute (read_state c_pcc) m"
      and "Commute (read_state procID) m"
  shows "Commute PCC m"
unfolding PCC_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'PCC}\<close>

lemma Commute_write'PCC [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_pcc_update x)) m"
  shows "Commute (write'PCC v) m"
unfolding write'PCC_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CAPR}\<close>

lemma Commute_CAPR [Commute_compositeI]:
  assumes "Commute (read_state c_capr) m"
      and "Commute (read_state procID) m"
  shows "Commute (CAPR v) m"
unfolding CAPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'CAPR}\<close>

lemma Commute_write'CAPR [Commute_compositeI]:
  assumes "Commute (read_state c_capr) m"
      and "\<And>x. Commute (update_state (c_capr_update x)) m"
  shows "Commute (write'CAPR v) m"
unfolding write'CAPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SCAPR}\<close>

lemma Commute_SCAPR [Commute_compositeI]:
  assumes "Commute (read_state c_scapr) m"
      and "Commute (read_state procID) m"
  shows "Commute (SCAPR v) m"
unfolding SCAPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'SCAPR}\<close>

lemma Commute_write'SCAPR [Commute_compositeI]:
  assumes "Commute (read_state c_scapr) m"
      and "\<And>x. Commute (update_state (c_scapr_update x)) m"
  shows "Commute (write'SCAPR v) m"
unfolding write'SCAPR_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalException}\<close>

lemma Commute_SignalException [Commute_compositeI]:
  assumes "Commute (read_state currentInst) m"
      and "Commute (read_state lastInst) m"
      and "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state capcause) m"
      and "Commute (read_state (\<lambda>s. c_BranchDelay (c_state s))) m"
      and "Commute (read_state (\<lambda>s. c_PC (c_state s))) m"
      and "Commute (read_state (\<lambda>s. EXL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. BEV (Status (c_CP0 (c_state s))))) m"
      and "\<And>x. Commute (update_state (BranchDelayPCC_update x)) m"
      and "\<And>x. Commute (update_state (BranchToPCC_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_BranchDelay_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_BranchTo_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_PC_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_exceptionSignalled_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Status_update (EXL_update x))))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (EPC_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadInstr_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadInstrP_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Cause_update (BD_update x))))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Cause_update (CauseRegister.ExcCode_update x))))) m"
      and "Commute PCC m"
      and "\<And>x. Commute (write'PCC x) m"
      and "\<And>x. Commute (SCAPR x) m"
      and "\<And>x. Commute (write'SCAPR x) m"
      and "Commute (next_unknown ''BadInstrP'') m"
  shows "Commute (SignalException v) m"
unfolding SignalException_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalCP2UnusableException}\<close>

lemma Commute_SignalCP2UnusableException [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Cause_update (CE_update x))))) m"
      and "\<And>x. Commute (SignalException x) m"
  shows "Commute SignalCP2UnusableException m"
unfolding SignalCP2UnusableException_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalCapException_internal}\<close>

lemma Commute_SignalCapException_internal [Commute_compositeI]:
  assumes "Commute (read_state capcause) m"
      and "\<And>x. Commute (update_state (capcause_update x)) m"
      and "\<And>x. Commute (SignalException x) m"
  shows "Commute (SignalCapException_internal v) m"
unfolding SignalCapException_internal_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalCapException}\<close>

lemma Commute_SignalCapException [Commute_compositeI]:
  assumes "\<And>x. Commute (SignalCapException_internal x) m"
  shows "Commute (SignalCapException v) m"
unfolding SignalCapException_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalCapException_noReg}\<close>

lemma Commute_SignalCapException_noReg [Commute_compositeI]:
  assumes "\<And>x. Commute (SignalCapException_internal x) m"
  shows "Commute (SignalCapException_noReg v) m"
unfolding SignalCapException_noReg_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const TLB_direct}\<close>

lemma Commute_TLB_direct [Commute_compositeI]:
  assumes "Commute (read_state c_TLB_direct) m"
      and "Commute (read_state procID) m"
  shows "Commute (TLB_direct v) m"
unfolding TLB_direct_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'TLB_direct}\<close>

lemma Commute_write'TLB_direct [Commute_compositeI]:
  assumes "Commute (read_state c_TLB_direct) m"
      and "\<And>x. Commute (update_state (c_TLB_direct_update x)) m"
  shows "Commute (write'TLB_direct v) m"
unfolding write'TLB_direct_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const TLB_assoc}\<close>

lemma Commute_TLB_assoc [Commute_compositeI]:
  assumes "Commute (read_state c_TLB_assoc) m"
      and "Commute (read_state procID) m"
  shows "Commute (TLB_assoc v) m"
unfolding TLB_assoc_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'TLB_assoc}\<close>

lemma Commute_write'TLB_assoc [Commute_compositeI]:
  assumes "Commute (read_state c_TLB_assoc) m"
      and "\<And>x. Commute (update_state (c_TLB_assoc_update x)) m"
  shows "Commute (write'TLB_assoc v) m"
unfolding write'TLB_assoc_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const LookupTLB}\<close>

lemma Commute_LookupTLB [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. Config6 (c_CP0 (c_state s)))) m"
      and "Commute (read_state (\<lambda>s. EntryHi (c_CP0 (c_state s)))) m"
      and "\<And>x. Commute (TLB_assoc x) m"
      and "\<And>x. Commute (TLB_direct x) m"
  shows "Commute (LookupTLB v) m"
unfolding LookupTLB_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalTLBException_internal}\<close>

lemma Commute_SignalTLBException_internal [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadVAddr_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (EntryHi_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Context_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (XContext_update x)))) m"
  shows "Commute (SignalTLBException_internal v) m"
unfolding SignalTLBException_internal_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalTLBException}\<close>

lemma Commute_SignalTLBException [Commute_compositeI]:
  assumes "\<And>x. Commute (SignalException x) m"
      and "\<And>x. Commute (SignalTLBException_internal x) m"
  shows "Commute (SignalTLBException v) m"
unfolding SignalTLBException_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CheckSegment}\<close>

lemma Commute_CheckSegment [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. K0 (Config (c_CP0 (c_state s))))) m"
      and "Commute UserMode m"
      and "Commute SupervisorMode m"
  shows "Commute (CheckSegment v) m"
unfolding CheckSegment_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const check_cca}\<close>

lemma Commute_check_cca [Commute_compositeI]:
  assumes "\<And>x. Commute (raise'exception x) m"
  shows "Commute (check_cca v) m"
unfolding check_cca_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const TLB_next_random}\<close>

lemma Commute_TLB_next_random [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. Random.Random (Random (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. Wired.Wired (Wired (c_CP0 (c_state s))))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Random_update (Random.Random_update x))))) m"
  shows "Commute (TLB_next_random v) m"
unfolding TLB_next_random_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const AddressTranslation}\<close>

lemma Commute_AddressTranslation [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. EntryHi (c_CP0 (c_state s)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadVAddr_update x)))) m"
      and "\<And>x. Commute (CheckSegment x) m"
      and "\<And>x. Commute (LookupTLB x) m"
      and "Commute PCC m"
      and "\<And>x. Commute (SignalTLBException x) m"
      and "\<And>x. Commute (raise'exception x) m"
      and "\<And>x. Commute (check_cca x) m"
      and "\<And>x. Commute (SignalException x) m"
      and "Commute (next_unknown ''tlb-translation'') m"
  shows "Commute (AddressTranslation v) m"
unfolding AddressTranslation_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CP0TLBEntry}\<close>

lemma Commute_CP0TLBEntry [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_CP0 (c_state s))) m"
  shows "Commute (CP0TLBEntry v) m"
unfolding CP0TLBEntry_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const SignalTLBCapException}\<close>

lemma Commute_SignalTLBCapException [Commute_compositeI]:
  assumes "\<And>x. Commute (SignalTLBException_internal x) m"
      and "\<And>x. Commute (SignalCapException_noReg x) m"
      and "Commute (next_unknown ''tlb-cap-exception'') m"
  shows "Commute (SignalTLBCapException v) m"
unfolding SignalTLBCapException_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const printMemStats}\<close>

lemma Commute_printMemStats [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
  shows "Commute printMemStats m"
unfolding printMemStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const initMemStats}\<close>

lemma Commute_initMemStats [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute initMemStats m"
unfolding initMemStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_data_reads_updt}\<close>

lemma Commute_stats_data_reads_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_data_reads_updt v) m"
unfolding stats_data_reads_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_data_writes_updt}\<close>

lemma Commute_stats_data_writes_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_data_writes_updt v) m"
unfolding stats_data_writes_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_inst_reads_updt}\<close>

lemma Commute_stats_inst_reads_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_inst_reads_updt v) m"
unfolding stats_inst_reads_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_valid_cap_reads_updt}\<close>

lemma Commute_stats_valid_cap_reads_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_valid_cap_reads_updt v) m"
unfolding stats_valid_cap_reads_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_valid_cap_writes_updt}\<close>

lemma Commute_stats_valid_cap_writes_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_valid_cap_writes_updt v) m"
unfolding stats_valid_cap_writes_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_invalid_cap_reads_updt}\<close>

lemma Commute_stats_invalid_cap_reads_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_invalid_cap_reads_updt v) m"
unfolding stats_invalid_cap_reads_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const stats_invalid_cap_writes_updt}\<close>

lemma Commute_stats_invalid_cap_writes_updt [Commute_compositeI]:
  assumes "Commute (read_state staticMemStats) m"
      and "Commute (read_state dynamicMemStats) m"
      and "\<And>x. Commute (update_state (staticMemStats_update x)) m"
      and "\<And>x. Commute (update_state (dynamicMemStats_update x)) m"
  shows "Commute (stats_invalid_cap_writes_updt v) m"
unfolding stats_invalid_cap_writes_updt_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const MEM}\<close>

lemma Commute_MEM [Commute_compositeI]:
  assumes "Commute (read_state the_MEM) m"
  shows "Commute (MEM v) m"
unfolding MEM_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'MEM}\<close>

lemma Commute_write'MEM [Commute_compositeI]:
  assumes "Commute (read_state the_MEM) m"
      and "\<And>x. Commute (update_state (the_MEM_update x)) m"
  shows "Commute (write'MEM v) m"
unfolding write'MEM_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const InitMEM}\<close>

lemma Commute_InitMEM [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (static_shadow_MEM_update x)) m"
      and "\<And>x. Commute (update_state (static_shadow_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (static_shadow_4K_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (static_shadow_16K_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (dynamic_shadow_MEM_update x)) m"
      and "\<And>x. Commute (update_state (dynamic_shadow_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (dynamic_shadow_4K_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (dynamic_shadow_16K_TAGS_update x)) m"
      and "\<And>x. Commute (update_state (the_MEM_update x)) m"
      and "Commute (next_unknown ''mem-data'') m"
  shows "Commute InitMEM m"
unfolding InitMEM_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const ReadData}\<close>

lemma Commute_ReadData [Commute_compositeI]:
  assumes "\<And>x. Commute (MEM x) m"
      and "\<And>x. Commute (stats_data_reads_updt x) m"
  shows "Commute (ReadData v) m"
unfolding ReadData_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const WriteData}\<close>

lemma Commute_WriteData [Commute_compositeI]:
  assumes "Commute (read_state the_MEM) m"
      and "\<And>x. Commute (write'MEM x) m"
      and "\<And>x. Commute (stats_data_writes_updt x) m"
  shows "Commute (WriteData v) m"
unfolding WriteData_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const ReadInst}\<close>

lemma Commute_ReadInst [Commute_compositeI]:
  assumes "\<And>x. Commute (MEM x) m"
      and "\<And>x. Commute (stats_inst_reads_updt x) m"
  shows "Commute (ReadInst v) m"
unfolding ReadInst_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const ReadCap}\<close>

lemma Commute_ReadCap [Commute_compositeI]:
  assumes "\<And>x. Commute (MEM x) m"
      and "\<And>x. Commute (stats_valid_cap_reads_updt x) m"
      and "\<And>x. Commute (stats_invalid_cap_reads_updt x) m"
  shows "Commute (ReadCap v) m"
unfolding ReadCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const WriteCap}\<close>

lemma Commute_WriteCap [Commute_compositeI]:
  assumes "\<And>x. Commute (write'MEM x) m"
      and "\<And>x. Commute (stats_valid_cap_writes_updt x) m"
      and "\<And>x. Commute (stats_invalid_cap_writes_updt x) m"
  shows "Commute (WriteCap v) m"
unfolding WriteCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const AdjustEndian}\<close>

lemma Commute_AdjustEndian [Commute_compositeI]:
  assumes "Commute ReverseEndian m"
      and "\<And>x. Commute (raise'exception x) m"
  shows "Commute (AdjustEndian v) m"
unfolding AdjustEndian_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const initMemAccessStats}\<close>

lemma Commute_initMemAccessStats [Commute_compositeI]:
  assumes "Commute (read_state memAccessStats) m"
      and "\<And>x. Commute (update_state (memAccessStats_update x)) m"
  shows "Commute initMemAccessStats m"
unfolding initMemAccessStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const printMemAccessStats}\<close>

lemma Commute_printMemAccessStats [Commute_compositeI]:
  assumes "Commute (read_state memAccessStats) m"
  shows "Commute printMemAccessStats m"
unfolding printMemAccessStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const getVirtualAddress}\<close>

lemma Commute_getVirtualAddress [Commute_compositeI]:
  assumes "\<And>x. Commute (SCAPR x) m"
  shows "Commute (getVirtualAddress v) m"
unfolding getVirtualAddress_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const LoadMemoryCap}\<close>

lemma Commute_LoadMemoryCap [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "Commute (read_state totalCore) m"
      and "Commute (read_state PIC_base_address) m"
      and "Commute (read_state memAccessStats) m"
      and "Commute (read_state (\<lambda>s. c_exceptionSignalled (c_state s))) m"
      and "\<And>x. Commute (update_state (memAccessStats_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_LLbit_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadVAddr_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (LLAddr_update x)))) m"
      and "\<And>x. Commute (AdjustEndian x) m"
      and "\<And>x. Commute (ReadData x) m"
      and "\<And>x. Commute (PIC_load x) m"
      and "\<And>x. Commute (SignalException x) m"
      and "\<And>x. Commute (AddressTranslation x) m"
      and "\<And>x. Commute (raise'exception x) m"
      and "Commute JTAG_UART_load m"
      and "\<And>x. Commute (stats_data_reads_updt x) m"
      and "Commute (next_unknown ''mem-data'') m"
  shows "Commute (LoadMemoryCap v) m"
unfolding LoadMemoryCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const LoadMemory}\<close>

lemma Commute_LoadMemory [Commute_compositeI]:
  assumes "\<And>x. Commute (SCAPR x) m"
      and "\<And>x. Commute (SignalCapException x) m"
      and "\<And>x. Commute (LoadMemoryCap x) m"
      and "Commute (next_unknown ''mem-data'') m"
  shows "Commute (LoadMemory v) m"
unfolding LoadMemory_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const LoadCap}\<close>

lemma Commute_LoadCap [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "Commute (read_state totalCore) m"
      and "Commute (read_state PIC_base_address) m"
      and "Commute (read_state memAccessStats) m"
      and "Commute (read_state (\<lambda>s. c_exceptionSignalled (c_state s))) m"
      and "\<And>x. Commute (update_state (memAccessStats_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_LLbit_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (LLAddr_update x)))) m"
      and "\<And>x. Commute (AddressTranslation x) m"
      and "\<And>x. Commute (raise'exception x) m"
      and "\<And>x. Commute (ReadCap x) m"
      and "Commute (next_unknown ''capability'') m"
  shows "Commute (LoadCap v) m"
unfolding LoadCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const StoreMemoryCap}\<close>

lemma Commute_StoreMemoryCap [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "Commute (read_state totalCore) m"
      and "Commute (read_state PIC_base_address) m"
      and "Commute (read_state memAccessStats) m"
      and "Commute (read_state (\<lambda>s. c_LLbit (c_state s))) m"
      and "Commute (read_state (\<lambda>s. c_exceptionSignalled (c_state s))) m"
      and "Commute (read_state (\<lambda>s. LLAddr (c_CP0 (c_state s)))) m"
      and "Commute (read_state all_state) m"
      and "Commute (read_state procID) m"
      and "\<And>x. Commute (update_state (all_state_update x)) m"
      and "\<And>x. Commute (update_state (memAccessStats_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_LLbit_update x))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadVAddr_update x)))) m"
      and "\<And>x. Commute (AdjustEndian x) m"
      and "\<And>x. Commute (SignalException x) m"
      and "\<And>x. Commute (AddressTranslation x) m"
      and "\<And>x. Commute (raise'exception x) m"
      and "\<And>x. Commute (JTAG_UART_store x) m"
      and "\<And>x. Commute (PIC_store x) m"
      and "\<And>x. Commute (WriteData x) m"
      and "Commute (next_unknown ''sc-success'') m"
  shows "Commute (StoreMemoryCap v) m"
unfolding StoreMemoryCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const StoreMemory}\<close>

lemma Commute_StoreMemory [Commute_compositeI]:
  assumes "\<And>x. Commute (SCAPR x) m"
      and "\<And>x. Commute (SignalCapException x) m"
      and "\<And>x. Commute (StoreMemoryCap x) m"
      and "Commute (next_unknown ''sc-success'') m"
  shows "Commute (StoreMemory v) m"
unfolding StoreMemory_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const StoreCap}\<close>

lemma Commute_StoreCap [Commute_compositeI]:
  assumes "Commute (read_state JTAG_UART) m"
      and "Commute (read_state totalCore) m"
      and "Commute (read_state PIC_base_address) m"
      and "Commute (read_state memAccessStats) m"
      and "Commute (read_state (\<lambda>s. c_LLbit (c_state s))) m"
      and "Commute (read_state (\<lambda>s. c_exceptionSignalled (c_state s))) m"
      and "Commute (read_state (\<lambda>s. LLAddr (c_CP0 (c_state s)))) m"
      and "Commute (read_state (\<lambda>s. ASID (EntryHi (c_CP0 (c_state s))))) m"
      and "Commute (read_state all_state) m"
      and "Commute (read_state procID) m"
      and "\<And>x. Commute (update_state (all_state_update x)) m"
      and "\<And>x. Commute (update_state (memAccessStats_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_LLbit_update x))) m"
      and "\<And>x. Commute (AddressTranslation x) m"
      and "\<And>x. Commute (raise'exception x) m"
      and "\<And>x. Commute (SignalTLBCapException x) m"
      and "\<And>x. Commute (WriteCap x) m"
  shows "Commute (StoreCap v) m"
unfolding StoreCap_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const Fetch}\<close>

lemma Commute_Fetch [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_exceptionSignalled (c_state s))) m"
      and "Commute (read_state (\<lambda>s. c_PC (c_state s))) m"
      and "Commute (read_state (\<lambda>s. Compare (c_CP0 (c_state s)))) m"
      and "Commute (read_state (\<lambda>s. Count (c_CP0 (c_state s)))) m"
      and "Commute (read_state (\<lambda>s. IE (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. EXL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. ERL (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. IM (Status (c_CP0 (c_state s))))) m"
      and "Commute (read_state (\<lambda>s. IP (Cause (c_CP0 (c_state s))))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (Cause_update x)))) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update (BadVAddr_update x)))) m"
      and "\<And>x. Commute (SignalException x) m"
      and "\<And>x. Commute (SignalCapException_noReg x) m"
      and "Commute PCC m"
      and "\<And>x. Commute (ReadInst x) m"
      and "\<And>x. Commute (AddressTranslation x) m"
  shows "Commute Fetch m"
unfolding Fetch_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CP0R}\<close>

lemma Commute_CP0R [Commute_compositeI]:
  assumes "Commute (read_state procID) m"
      and "Commute (read_state totalCore) m"
      and "Commute (read_state (\<lambda>s. c_CP0 (c_state s))) m"
      and "Commute (next_unknown ''cop-reg'') m"
  shows "Commute (CP0R v) m"
unfolding CP0R_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'CP0R}\<close>

lemma Commute_write'CP0R [Commute_compositeI]:
  assumes "Commute (read_state hasCP1) m"
      and "Commute (read_state hasCP2) m"
      and "Commute (read_state (\<lambda>s. c_CP0 (c_state s))) m"
      and "\<And>x. Commute (update_state (done_update x)) m"
      and "\<And>x. Commute (update_state (c_state_update (c_CP0_update x))) m"
      and "\<And>x. Commute (raise'exception x) m"
  shows "Commute (write'CP0R v) m"
unfolding write'CP0R_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const resetStats}\<close>

lemma Commute_resetStats [Commute_compositeI]:
  assumes "Commute initMemStats m"
      and "Commute initMemAccessStats m"
      and "Commute initCoreStats m"
  shows "Commute resetStats m"
unfolding resetStats_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const HI}\<close>

lemma Commute_HI [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_hi (c_state s))) m"
      and "Commute (next_unknown ''hi-reg'') m"
  shows "Commute HI m"
unfolding HI_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'HI}\<close>

lemma Commute_write'HI [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_state_update (c_hi_update x))) m"
  shows "Commute (write'HI v) m"
unfolding write'HI_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const LO}\<close>

lemma Commute_LO [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. c_lo (c_state s))) m"
      and "Commute (next_unknown ''lo-reg'') m"
  shows "Commute LO m"
unfolding LO_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const write'LO}\<close>

lemma Commute_write'LO [Commute_compositeI]:
  assumes "\<And>x. Commute (update_state (c_state_update (c_lo_update x))) m"
  shows "Commute (write'LO v) m"
unfolding write'LO_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const special_register_accessible}\<close>

lemma Commute_special_register_accessible [Commute_compositeI]:
  assumes "Commute (read_state (\<lambda>s. CU0 (Status (c_CP0 (c_state s))))) m"
      and "Commute PCC m"
      and "Commute KernelMode m"
  shows "Commute (special_register_accessible v) m"
unfolding special_register_accessible_alt_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const log_instruction}\<close>

lemma Commute_log_instruction [Commute_compositeI]:
  assumes "Commute (read_state procID) m"
      and "Commute (read_state instCnt) m"
      and "Commute (read_state (\<lambda>s. c_PC (c_state s))) m"
      and "Commute PCC m"
  shows "Commute (log_instruction v) m"
unfolding log_instruction_alt_def
using assms
by - Commute_find_dependencies

(* Code generation - override - Next *)

lemma Commute_TakeBranch [Commute_compositeI]:
  assumes "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state BranchToPCC) m"
      and "Commute (read_state getBranchDelay) m"
      and "Commute (read_state getBranchTo) m"
      and "Commute (read_state getExceptionSignalled) m"
      and "Commute (read_state getPC) m"
      and "Commute (read_state CCallBranch) m"
      and "\<And>v. Commute (update_state (BranchDelayPCC_update v)) m"
      and "\<And>v. Commute (update_state (BranchToPCC_update v)) m"
      and "\<And>v. Commute (update_state (setBranchDelay v)) m"
      and "\<And>v. Commute (update_state (setBranchTo v)) m"
      and "\<And>v. Commute (update_state (setPC v)) m"
      and "\<And>v. Commute (update_state (CCallBranch_update v)) m"
      and "\<And>v. Commute (update_state (CCallBranchDelay_update v)) m"
      and "\<And>v. Commute (write'PCC v) m"
      and "\<And>ex. Commute (raise'exception (UNPREDICTABLE ex)) m"
  shows "Commute TakeBranch m"
unfolding TakeBranch_def
using assms
by - Commute_find_dependencies

(* Code generation - end override *)

(* Code generation - end *)

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemma below is testing the proof method.\<close>

lemma
  "Commute (bind UserMode (\<lambda>a. update_state (setPC (f a))))
           (bind (write'GPR v) (\<lambda>_. foreach_loop (l, \<lambda>x. update_state (setExceptionSignalled x))))"
by Commute

subsection \<open>Changing the order of steps\<close>

definition SwappingGives :: 
  "(state \<Rightarrow> 'a \<times> state) \<Rightarrow> 
   (state \<Rightarrow> 'b \<times> state) \<Rightarrow> 
   (state \<Rightarrow> 'a \<times> state) \<Rightarrow> 
   (state \<Rightarrow> 'b \<times> state) \<Rightarrow> 
   bool" 
where
  "SwappingGives m n m' n' \<equiv>
   bind m (\<lambda>_. n) = bind n' (\<lambda>a. bind m' (\<lambda>_. return a))"

lemma SwappingGivesE_ValuePart [elim!]:
  assumes "SwappingGives m n m' n'"
  shows "ValuePart n (StatePart m s) = ValuePart n' s"
proof -
  have "bind m (\<lambda>_. n) = bind n' (\<lambda>a. bind m' (\<lambda>_. return a))"
    using assms
    unfolding SwappingGives_def 
    by simp
  from arg_cong[OF this, where f="\<lambda>m. ValuePart m s"]
  show ?thesis
    by (auto simp: ValueAndStatePart_simp)
qed

lemma SwappingGivesE_StatePart [elim!]:
  assumes "SwappingGives m n m' n'"
  shows "StatePart n (StatePart m s) = StatePart m' (StatePart n' s)"
proof -
  have "bind m (\<lambda>_. n) = bind n' (\<lambda>a. bind m' (\<lambda>_. return a))"
    using assms
    unfolding SwappingGives_def 
    by simp
  from arg_cong[OF this, where f="\<lambda>m. StatePart m s"]
  show ?thesis
    by (auto simp: ValueAndStatePart_simp)
qed

lemma SwappingGives_left_return:
  shows "SwappingGives (return x) m (return undefined) m"
unfolding SwappingGives_def
by simp

lemma SwappingGives_left_read_state:
  shows "SwappingGives (read_state f) m (return undefined) m"
unfolding SwappingGives_def
by simp

lemma SwappingGives_right_bind:
  assumes "SwappingGives m n\<^sub>1 m' n\<^sub>1'"
      and "\<And>a. SwappingGives m' (n\<^sub>2 a) m'' (n\<^sub>2' a)"
  shows "SwappingGives m (bind n\<^sub>1 n\<^sub>2) m'' (bind n\<^sub>1' n\<^sub>2')"
proof -
  have "bind m (\<lambda>_. bind n\<^sub>1 n\<^sub>2) = 
        bind (bind n\<^sub>1' (\<lambda>a. bind m' (\<lambda>_. return a))) n\<^sub>2"
    using assms(1)
    unfolding SwappingGives_def
    by (simp add: bind_associativity[THEN sym])
  also have "... = bind (bind n\<^sub>1' n\<^sub>2') (\<lambda>a. bind m'' (\<lambda>_. return a))"
    using assms(2)
    unfolding SwappingGives_def
    by (simp add: bind_associativity)
  finally show ?thesis
    unfolding SwappingGives_def
    by simp
qed

text \<open>Note that the two assumptions below require that \<open>m\<close> stays the same when it is swapped with
\<open>n\<^sub>1\<close> or with \<open>n\<^sub>2\<close>, because this prevents duplicating \<open>m\<close>. However, it also means that the lemma
will not always be applicable.\<close>

lemma SwappingGives_right_if:
  assumes "SwappingGives m n\<^sub>1 m n\<^sub>1'"
      and "SwappingGives m n\<^sub>2 m n\<^sub>2'"
  shows "SwappingGives m (if b then n\<^sub>1 else n\<^sub>2) m (if b then n\<^sub>1' else n\<^sub>2')"
using assms
by auto

lemma SwappingGives_right_option:
  assumes "SwappingGives m n\<^sub>1 m n\<^sub>1'"
      and "\<And>y. SwappingGives m (n\<^sub>2 y) m (n\<^sub>2' y)"
  shows "SwappingGives m (case x of None \<Rightarrow> n\<^sub>1 | Some y \<Rightarrow> n\<^sub>2 y) 
                       m (case x of None \<Rightarrow> n\<^sub>1' | Some y \<Rightarrow> n\<^sub>2' y)"
using assms
by (cases x) auto

lemma SwappingGives_right_conj:
  assumes "SwappingGives m n\<^sub>1 m n\<^sub>1'"
      and "SwappingGives m n\<^sub>2 m n\<^sub>2'"
  shows "SwappingGives m (n\<^sub>1 \<and>\<^sub>b n\<^sub>2) m (n\<^sub>1' \<and>\<^sub>b n\<^sub>2')"
using SwappingGivesE_ValuePart[OF assms(1)]
using SwappingGivesE_ValuePart[OF assms(2)]
unfolding SwappingGives_def
by (intro monad_eqI) (auto simp: ValueAndStatePart_simp)

lemma SwappingGives_right_disj:
  assumes "SwappingGives m n\<^sub>1 m n\<^sub>1'"
      and "SwappingGives m n\<^sub>2 m n\<^sub>2'"
  shows "SwappingGives m (n\<^sub>1 \<or>\<^sub>b n\<^sub>2) m (n\<^sub>1' \<or>\<^sub>b n\<^sub>2')"
using SwappingGivesE_ValuePart[OF assms(1)]
using SwappingGivesE_ValuePart[OF assms(2)]
unfolding SwappingGives_def
by (intro monad_eqI) (auto simp: ValueAndStatePart_simp)

lemma SwappingGives_right_equals:
  assumes "SwappingGives m n\<^sub>1 m n\<^sub>1'"
      and "SwappingGives m n\<^sub>2 m n\<^sub>2'"
  shows "SwappingGives m (n\<^sub>1 =\<^sub>b n\<^sub>2) m (n\<^sub>1' =\<^sub>b n\<^sub>2')"
using SwappingGivesE_ValuePart[OF assms(1)]
using SwappingGivesE_ValuePart[OF assms(2)]
unfolding SwappingGives_def
by (intro monad_eqI) (auto simp: ValueAndStatePart_simp)

lemma SwappingGives_right_bind_read_if_heuristic:
  assumes "SwappingGives m (read_state f) m (return b)"
      and "if_simp = (if b then n else n')"
      and "SwappingGives m if_simp m' if_simp'"
  shows "SwappingGives m (bind (read_state f) (\<lambda>x. if x then n else n')) m' if_simp'"
using SwappingGivesE_ValuePart[OF assms(1)]
using SwappingGivesE_StatePart[OF assms(1)]
using SwappingGivesE_ValuePart[OF assms(3)]
using SwappingGivesE_StatePart[OF assms(3)]
using assms(2)
unfolding SwappingGives_def
by (intro monad_eqI) (auto simp: ValueAndStatePart_simp)

lemma SwappingGives_Commute:
  assumes "Commute m n"
  shows "SwappingGives m n m n"
using assms
unfolding Commute_def SwappingGives_def 
by (simp add: monad_eqI ValuePart_bind StatePart_bind)

lemma SwappingGives_merge_setter_getter:
  assumes "\<And>s. StatePart n s = s"
      and "\<And>s. ValuePart n (StatePart m s) = x"
  shows "SwappingGives m n m (return x)"
using assms
unfolding SwappingGives_def
by (intro monad_eqI) (simp_all add: ValuePart_bind StatePart_bind)

lemma SwappingGives_stuck:
  shows "SwappingGives m n (return undefined) (bind m (\<lambda>_. n))"
unfolding SwappingGives_def
by simp

method PushBackwards uses intro simp =
  (rule SwappingGives_left_return 
        SwappingGives_left_read_state) |
  (rule SwappingGives_right_bind_read_if_heuristic,
     PushBackwards intro: intro simp: simp,
     solves \<open>simp add: simp\<close>,
     PushBackwards intro: intro simp: simp) |
  (rule SwappingGives_right_bind,
     PushBackwards intro: intro simp: simp,
     PushBackwards intro: intro simp: simp) |
  (rule SwappingGives_right_if 
        SwappingGives_right_option
        SwappingGives_right_conj
        SwappingGives_right_disj
        SwappingGives_right_equals,
     PushBackwards intro: intro simp: simp,
     PushBackwards intro: intro simp: simp) |
  -- \<open>The following rule is an optimisation: if \<open>SwappingGives_right_xxx\<close> does not work, then
  \<open>SwappingGives_Commute\<close> also won't work.\<close>
  (rule SwappingGives_stuck[where n="if _ then _ else _"]
        SwappingGives_stuck[where n="case _ of None \<Rightarrow> _ | Some y \<Rightarrow> _ y"]
        SwappingGives_stuck[where n="_ \<and>\<^sub>b _"]
        SwappingGives_stuck[where n="_ \<or>\<^sub>b _"]
        SwappingGives_stuck[where n="_ =\<^sub>b _"]) |
  (rule SwappingGives_Commute,
     solves \<open>Commute intro: intro\<close>) |
  (rule SwappingGives_merge_setter_getter;
     solves \<open>simp add: simp\<close>) |
  (rule SwappingGives_stuck)

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemmas below is testing the proof method.\<close>

lemma "SwappingGives (write'CAPR x) (write'PCC y) (write'CAPR x) (write'PCC y)"
by PushBackwards

lemma "SwappingGives (write'CAPR x) 
                     (bind (write'PCC y) (\<lambda>_. write'MEM z))
                     (write'CAPR x)
                     (bind (write'PCC y) (\<lambda>_. write'MEM z))"
by PushBackwards

lemma "SwappingGives (write'CAPR x) 
                     (bind (GPR i) (\<lambda>a. write'GPR (a, j)))
                     (write'CAPR x)
                     (bind (GPR i) (\<lambda>a. write'GPR (a, j)))"
by PushBackwards

lemma "SwappingGives (write'CAPR x) 
                     (foreach_loop (l, \<lambda>a. write'MEM (y, a)))
                     (write'CAPR x)
                     (foreach_loop (l, \<lambda>a. write'MEM (y, a)))"
by PushBackwards

lemma "SwappingGives (foreach_loop (l, \<lambda>a. write'CAPR (y, a)))
                     (write'MEM x) 
                     (foreach_loop (l, \<lambda>a. write'CAPR (y, a)))
                     (write'MEM x)"
by PushBackwards

lemma 
  assumes "\<And>cap cd s. ValuePart (CAPR cd) (StatePart (write'CAPR (cap, cd)) s) = cap"
      and "\<And>cd s. StatePart (CAPR cd) s = s"
  shows "SwappingGives (write'CAPR (cap, cd)) 
                       (bind (CAPR cd) (\<lambda>a. write'PCC a))
                       (write'CAPR (cap, cd))
                       (bind (return cap) write'PCC)"
by (PushBackwards simp: assms)

lemma 
  assumes "\<And>cap cd s. ValuePart (CAPR cd) (StatePart (write'CAPR (cap, cd)) s) = cap"
      and "\<And>cd s. StatePart (CAPR cd) s = s"
  shows "SwappingGives (write'CAPR (cap, cd)) 
                       (bind (CAPR cd) (\<lambda>a. write'CAPR (a, cb)))
                       (return undefined)
                       (bind (return cap) 
                             (\<lambda>a. bind (write'CAPR (cap, cd)) 
                             (\<lambda>_. write'CAPR (a, cb))))"
by (PushBackwards simp: assms)

lemma 
  assumes "\<And>cap cd s. ValuePart (CAPR cd) (StatePart (write'CAPR (cap, cd)) s) = cap"
      and "\<And>cd s. StatePart (CAPR cd) s = s"
  shows "SwappingGives (write'CAPR (cap, cd)) 
                       (if b then CAPR cd else PCC)
                       (write'CAPR (cap, cd))
                       (if b then return cap else PCC)"
by (PushBackwards simp: assms)

lemma 
  assumes "\<And>cap cd s. ValuePart (CAPR cd) (StatePart (write'CAPR (cap, cd)) s) = cap"
      and "\<And>cd s. StatePart (CAPR cd) s = s"
  shows "SwappingGives (write'CAPR (cap, cd)) 
                       (case b of None \<Rightarrow> CAPR cd | Some y \<Rightarrow> return y)
                       (write'CAPR (cap, cd))
                       (case b of None \<Rightarrow> return cap | Some y \<Rightarrow> return y)"
by (PushBackwards simp: assms)

lemma 
  assumes "\<And>cap cd s. ValuePart (CAPR cd) (StatePart (write'CAPR (cap, cd)) s) = cap"
      and "\<And>cd s. StatePart (CAPR cd) s = s"
  shows "SwappingGives (write'CAPR (cap, cd)) 
                       (CAPR cd =\<^sub>b return cap')
                       (write'CAPR (cap, cd))
                       (return cap =\<^sub>b return cap')"
by (PushBackwards simp: assms)

lemma 
  assumes "\<And>s. getExceptionSignalled (StatePart (SignalException ex) s) = True"
  shows "SwappingGives (SignalException ex)
                       (bind (read_state getExceptionSignalled)
                             (\<lambda>b. if b then return 0 else read_state getPC))
                       (SignalException ex)
                       (return 0)"
by (PushBackwards simp: assms)

lemma 
  assumes "Commute p n"
  shows "SwappingGives n p n p"
by (PushBackwards intro: assms)

section \<open>Hoare triples\<close>

subsection \<open>Hoare triples\<close>

definition PrePost where
  "PrePost p m q \<equiv> 
   \<forall>s. ValuePart p s \<longrightarrow> ValuePart (bind m q) s"

lemma PrePostI:
  assumes "\<And>s. ValuePart p s \<Longrightarrow> ValuePart (bind m q) s"
  shows "PrePost p m q"
using assms
unfolding PrePost_def
by auto

lemma PrePostE:
  assumes "PrePost p m q"
      and "ValuePart p s"
  shows "ValuePart (bind m q) s"
using assms
unfolding PrePost_def
by auto

lemma PrePost_pre_strengthening:
  assumes "PrePost p' m q"
      and "\<And>s. ValuePart p s \<Longrightarrow> ValuePart p' s"
  shows   "PrePost p m q"
using assms
unfolding PrePost_def
by simp

lemma PrePost_post_weakening:
  assumes "PrePost p m q'"
      and "\<And>a s. ValuePart (q' a) s \<Longrightarrow> ValuePart (q a) s"
  shows   "PrePost p m q"
using assms
unfolding PrePost_def
by (simp add: ValuePart_bind)

lemma PrePostIE:
  assumes "PrePost p' m q'"
      and "\<And>s. ValuePart p s \<Longrightarrow> ValuePart p' s"
      and "\<And>a s. ValuePart (q' a) s \<Longrightarrow> ValuePart (q a) s"
  shows   "PrePost p m q"
using PrePost_pre_strengthening
  PrePost_post_weakening
  assms
by metis

lemma PrePost_weakest_pre_any:
  shows "PrePost (bind m q) m q"
unfolding PrePost_def
by simp

lemma PrePost_weakest_pre_return:
  shows "PrePost (q x) (return x) q"
unfolding PrePost_def
by simp

lemmas PrePost_weakest_pre_read_state =
  PrePost_weakest_pre_any[where m="read_state f"] for f

lemma PrePost_weakest_pre_read_only:
  assumes "\<And>s. StatePart m s = s"
  shows "PrePost (bind (read_state (ValuePart m)) q) m q"
using assms
unfolding PrePost_def
by (simp add: ValuePart_bind)

lemmas PrePost_weakest_pre_update_state =
  PrePost_weakest_pre_any[where m="update_state f"] for f

text \<open>Introducing \<open>p'_simp\<close> in the lemma below might seem redundant, but it allows the proof method
to simplify \<open>p'_simp\<close> before using it.\<close>

lemma PrePost_weakest_pre_bind:
  assumes "\<And>a. PrePost (p' a) (n a) q"
      and "p'_simp = p'"
      and "PrePost p m p'_simp"
  shows   "PrePost p (bind m n) q"
using assms
unfolding PrePost_def
by (simp add: ValuePart_bind StatePart_bind)

lemma PrePost_weakest_pre_if:
  assumes "PrePost p m q"
      and "PrePost p' n q"
  shows   "PrePost (if b then p else p') 
                   (if b then m else n) 
                   q"
using assms
unfolding PrePost_def
by auto

lemma PrePost_weakest_pre_let:
  assumes "\<And>y. PrePost (p y) (m y) q"
  shows   "PrePost (let x = y in p x) 
                   (let x = y in m x) 
                   q"
using assms
by auto

lemma PrePost_weakest_pre_prod:
  assumes "\<And>y z. PrePost (p y z) (m y z) q"
  shows   "PrePost (case x of (y, z) \<Rightarrow> p y z) 
                   (case x of (y, z) \<Rightarrow> m y z) 
                   q"
using assms
by (cases x) simp

lemma PrePost_weakest_pre_option:
  assumes "PrePost p1 m1 q"
      and "\<And>y. PrePost (p2 y) (m2 y) q"
  shows   "PrePost (case x of None \<Rightarrow> p1 | Some y \<Rightarrow> p2 y)
                   (case x of None \<Rightarrow> m1 | Some y \<Rightarrow> m2 y)
                   q"
using assms
by (cases x) auto

lemma PrePost_weakest_pre_list:
  assumes "PrePost p1 m1 q"
      and "\<And>h t. PrePost (p2 h t) (m2 h t) q"
  shows   "PrePost (case l of [] \<Rightarrow> p1 | h # t \<Rightarrow> p2 h t)
                   (case l of [] \<Rightarrow> m1 | h # t \<Rightarrow> m2 h t)
                   q"
using assms
by (cases l) auto

lemma PrePost_weakest_pre_DataType:
  assumes "\<And>cap. PrePost (p1 cap) (m1 cap) q"
      and "\<And>v. PrePost (p2 v) (m2 v) q"
  shows   "PrePost (case t of Cap cap \<Rightarrow> p1 cap | Raw v \<Rightarrow> p2 v) 
                   (case t of Cap cap \<Rightarrow> m1 cap | Raw v \<Rightarrow> m2 v) 
                   q"
using assms
by (cases t) auto

lemma PrePost_weakest_pre_RegSet:
  assumes "PrePost p1 m1 q"
      and "PrePost p2 m2 q"
      and "PrePost p3 m3 q"
      and "PrePost p4 m4 q"
  shows   "PrePost (case x of Lo_rs \<Rightarrow> p1
                            | Hi_rs \<Rightarrow> p2
                            | CLo_rs \<Rightarrow> p3
                            | CHi_rs \<Rightarrow> p4) 
                   (case x of Lo_rs \<Rightarrow> m1
                            | Hi_rs \<Rightarrow> m2
                            | CLo_rs \<Rightarrow> m3
                            | CHi_rs \<Rightarrow> m4) 
                   q"
using assms
by (cases x) auto

lemma PrePost_weakest_pre_CmpType:
  assumes "PrePost p1 m1 q"
      and "PrePost p2 m2 q"
      and "PrePost p3 m3 q"
      and "PrePost p4 m4 q"
      and "PrePost p5 m5 q"
      and "PrePost p6 m6 q"
      and "PrePost p7 m7 q"
      and "PrePost p8 m8 q"
  shows   "PrePost (case x of EQ \<Rightarrow> p1
                            | NE \<Rightarrow> p2
                            | LT \<Rightarrow> p3
                            | LE \<Rightarrow> p4
                            | LTU \<Rightarrow> p5
                            | LEU \<Rightarrow> p6
                            | EXEQ \<Rightarrow> p7
                            | NEXEQ \<Rightarrow> p8) 
                   (case x of EQ \<Rightarrow> m1
                            | NE \<Rightarrow> m2
                            | LT \<Rightarrow> m3
                            | LE \<Rightarrow> m4
                            | LTU \<Rightarrow> m5
                            | LEU \<Rightarrow> m6
                            | EXEQ \<Rightarrow> m7
                            | NEXEQ \<Rightarrow> m8) 
                   q"
using assms
by (cases x) auto

lemmas PrePost_weakest_pre_cases_arity_1 =
  PrePost_weakest_pre_let
  PrePost_weakest_pre_prod

lemmas PrePost_weakest_pre_cases_arity_2 =
  PrePost_weakest_pre_if
  PrePost_weakest_pre_option
  PrePost_weakest_pre_list
  PrePost_weakest_pre_DataType

lemmas PrePost_weakest_pre_cases =
  PrePost_weakest_pre_cases_arity_1
  PrePost_weakest_pre_cases_arity_2
  PrePost_weakest_pre_RegSet
  PrePost_weakest_pre_CmpType

lemmas PrePost_weakest_pre_foreach_loop =
  PrePost_weakest_pre_any[where m="foreach_loop (l, m)"] for l m

lemmas PrePost_weakest_pre_foreach_loop_agg =
  PrePost_weakest_pre_any[where m="foreach_loop_agg l v m"] for l v m

lemma PrePost_splitValueAndStatePart:
  assumes "\<And>a. PrePost (p a) m (\<lambda>_. q a)"
  shows "PrePost (bind (read_state (ValuePart m)) p) m q"
using assms
unfolding PrePost_def
by (auto simp: ValuePart_bind)

lemmas PrePost_splitValueAndStatePart_foreach_loop_agg =
  PrePost_splitValueAndStatePart[where m="foreach_loop_agg l v m"] for l v m

lemma PrePost_weakest_pre_conj:
  assumes "PrePost p\<^sub>1 m q\<^sub>1"
      and "PrePost p\<^sub>2 m q\<^sub>2"
  shows "PrePost (p\<^sub>1 \<and>\<^sub>b p\<^sub>2) m (\<lambda>a. (q\<^sub>1 a) \<and>\<^sub>b (q\<^sub>2 a))"
using assms
unfolding PrePost_def
by (simp add: ValueAndStatePart_simp)

lemma PrePost_weakest_pre_disj:
  assumes "PrePost p\<^sub>1 m q\<^sub>1"
      and "PrePost p\<^sub>2 m q\<^sub>2"
  shows "PrePost (p\<^sub>1 \<or>\<^sub>b p\<^sub>2) m (\<lambda>a. (q\<^sub>1 a) \<or>\<^sub>b (q\<^sub>2 a))"
using assms
unfolding PrePost_def
by (simp add: ValueAndStatePart_simp)

text \<open>Negation and equality does not decompose in their parts. To compute the weakest precondition
we just unfold those definitions.\<close>

lemma PrePost_weakest_pre_not:
  assumes "q' = (\<lambda>a. bind (read_state (ValuePart (q a))) 
                          (\<lambda>x. return (\<not> x)))"
      and "PrePost p m q'"
  shows "PrePost p m (\<lambda>a. \<not>\<^sub>b (q a))"
using assms
unfolding NotMonadic_def UnaryLift_def
by simp

lemma PrePost_weakest_pre_equals:
  assumes "q' = (\<lambda>a. bind (read_state (ValuePart (q\<^sub>1 a))) 
                          (\<lambda>x. bind (read_state (ValuePart (q\<^sub>2 a))) 
                          (\<lambda>x'. return (x = x'))))"
      and "PrePost p m q'"
  shows "PrePost p m (\<lambda>a. (q\<^sub>1 a) =\<^sub>b (q\<^sub>2 a))"
using assms
unfolding EqMonadic_def BinaryLift_def
by simp

lemma PrePostE_read_states [elim]:
  assumes "PrePost (read_state f) m (\<lambda>a. read_state (g a))"
      and "f s"
  shows "g (ValuePart m s) (StatePart m s)"
using assms
unfolding PrePost_def
by (simp add: ValuePart_bind)

subsection \<open>Invariants\<close>

abbreviation "IsInvariant p f \<equiv> PrePost p f (\<lambda>_. p)"

lemma IsInvariant_def:
  shows "IsInvariant p f = (\<forall>s. ValuePart p s \<longrightarrow> ValuePart (bind f (\<lambda>_. p)) s)"
unfolding PrePost_def ..

lemma IsInvariant_constant [intro!, simp]:
  shows "IsInvariant (return x) m"
unfolding IsInvariant_def
by simp

lemma IsInvariant_return [intro!, simp]:
  shows "IsInvariant p (return x)"
unfolding IsInvariant_def
by simp

lemma IsInvariant_read_state [intro!, simp]:
  shows "IsInvariant p (read_state f)"
unfolding IsInvariant_def
by simp

lemma IsInvariant_bind [intro]:
  assumes "IsInvariant p m"
      and "\<And>a. IsInvariant p (n a)"
  shows "IsInvariant p (bind m n)"
using assms
unfolding IsInvariant_def
by (simp add: ValueAndStatePart_simp)

lemma IsInvariant_foreach_loop [intro]:
  assumes "\<And>a. IsInvariant p (m a)"
  shows "IsInvariant p (foreach_loop (l, m))"
using assms
by (induct l) auto

lemma IsInvariant_foreach_loop_agg [intro]:
  assumes "\<And>a b. IsInvariant p (m a b)"
  shows "IsInvariant p (foreach_loop_agg l b m)"
using assms
by (induct l arbitrary: b) auto

lemmas IsInvariant_cases [intro] =
  all_split[where P="IsInvariant p", THEN iffD2] for p

lemma IsInvariant_update_state_StatePart [simp]:
  shows "IsInvariant p (update_state (StatePart m)) = IsInvariant p m"
unfolding IsInvariant_def
by (simp add: ValueAndStatePart_simp)

lemmas IsInvariant_update_state_StatePartE =
  IsInvariant_update_state_StatePart[THEN iffD2]

lemma IsInvariant_Commute [elim!]:
  assumes "Commute p m"
  shows "IsInvariant p m"
using assms
unfolding Commute_def IsInvariant_def
by (simp add: ValuePart_bind)

lemmas IsInvariant_Commute_swapped [elim!] = 
  IsInvariant_Commute[OF Commute_is_symmetric[THEN iffD1]]

lemmas IsInvariant_conj = 
  PrePost_weakest_pre_conj[where p\<^sub>1=p and q\<^sub>1="\<lambda>_. p" and p\<^sub>2=q and q\<^sub>2="\<lambda>_. q"] for p q

lemmas IsInvariant_disj = 
  PrePost_weakest_pre_disj[where p\<^sub>1=p and q\<^sub>1="\<lambda>_. p" and p\<^sub>2=q and q\<^sub>2="\<lambda>_. q"] for p q

method Invariant uses intro =
  assumption |
  (rule intro 
        IsInvariant_return
        IsInvariant_read_state
        IsInvariant_update_state_StatePartE
        IsInvariant_bind
        IsInvariant_foreach_loop
        IsInvariant_foreach_loop_agg
        IsInvariant_cases
        IsInvariant_conj
        IsInvariant_disj;
      (intro allI conjI impI)?;
      Invariant intro: intro) |
  (rule IsInvariant_Commute,
      solves \<open>Commute intro: intro\<close>)

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemmas below is testing the proof method.\<close>

lemma "IsInvariant (read_state getCP0StatusEXL) (return cap)"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (read_state getPC)"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (write'CAPR x)"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (update_state (StatePart (write'CAPR x)))"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (bind PCC (\<lambda>cap. write'CAPR (cap, cd)))"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (foreach_loop (l, \<lambda>cd. write'CAPR (nullCap, cd)))"
by Invariant

lemma "IsInvariant (read_state getCP0StatusEXL) (if b then write'CAPR x else write'CAPR y)"
by Invariant

subsection \<open>Strengthening prefixes\<close>

definition StrengthenedPrefix where
  "StrengthenedPrefix p q m \<equiv>
   \<forall>s. ValuePart (bind q m) s \<longrightarrow> ValuePart (bind p m) s"

lemma StrengthenedPrefix_same_prefix:
  shows "StrengthenedPrefix p p m"
unfolding StrengthenedPrefix_def 
by simp

text \<open>Introducing \<open>m'\<close> in the lemma below might seem redundant, but it allows the proof method to
simplify \<open>m'\<close> before using it. This speeds up the proof method considerably. \<close>

lemma StrengthenedPrefix_bindI:
  assumes "\<And>a. StrengthenedPrefix (p' a) (q' a) m"
      and "m' = (\<lambda>a. bind (q' a) m)"
      and "StrengthenedPrefix p q m'"
  shows "StrengthenedPrefix (bind p p') (bind q q') m"
using assms
unfolding StrengthenedPrefix_def ValuePart_def
unfolding monad_def Let_def
by auto

lemma StrengthenedPrefix_ifI:
  assumes "StrengthenedPrefix p\<^sub>1 q\<^sub>1 m"
      and "StrengthenedPrefix p\<^sub>2 q\<^sub>2 m"
  shows   "StrengthenedPrefix (if b then p\<^sub>1 else p\<^sub>2) 
                              (if b then q\<^sub>1 else q\<^sub>2) 
                              m"
using assms
by auto

lemma StrengthenedPrefix_letI:
  assumes "\<And>y. StrengthenedPrefix (p y) (q y) m"
  shows   "StrengthenedPrefix (let x = y in p x) 
                              (let x = y in q x) 
                              m"
using assms
by auto

lemma StrengthenedPrefix_prodI:
  assumes "\<And>y z. StrengthenedPrefix (p y z) (q y z) m"
  shows   "StrengthenedPrefix (case x of (y, z) \<Rightarrow> p y z) 
                              (case x of (y, z) \<Rightarrow> q y z) 
                              m"
using assms
by (cases x) simp

lemma StrengthenedPrefix_optionI:
  assumes "StrengthenedPrefix p\<^sub>1 q\<^sub>1 m"
      and "\<And>y. StrengthenedPrefix (p\<^sub>2 y) (q\<^sub>2 y) m"
  shows   "StrengthenedPrefix (case x of None \<Rightarrow> p\<^sub>1 | Some y \<Rightarrow> p\<^sub>2 y)
                              (case x of None \<Rightarrow> q\<^sub>1 | Some y \<Rightarrow> q\<^sub>2 y)
                              m"
using assms
by (cases x) auto

lemma StrengthenedPrefix_listI:
  assumes "StrengthenedPrefix p\<^sub>1 q\<^sub>1 m"
      and "\<And>h t. StrengthenedPrefix (p\<^sub>2 h t) (q\<^sub>2 h t) m"
  shows   "StrengthenedPrefix (case l of [] \<Rightarrow> p\<^sub>1 | h # t \<Rightarrow> p\<^sub>2 h t)
                              (case l of [] \<Rightarrow> q\<^sub>1 | h # t \<Rightarrow> q\<^sub>2 h t)
                              m"
using assms
by (cases l) auto

lemma StrengthenedPrefix_DataTypeI:
  assumes "\<And>cap. StrengthenedPrefix (p\<^sub>1 cap) (q\<^sub>1 cap) m"
      and "\<And>v. StrengthenedPrefix (p\<^sub>2 v) (q\<^sub>2 v) m"
  shows   "StrengthenedPrefix (case t of Cap cap \<Rightarrow> p\<^sub>1 cap | Raw v \<Rightarrow> p\<^sub>2 v) 
                              (case t of Cap cap \<Rightarrow> q\<^sub>1 cap | Raw v \<Rightarrow> q\<^sub>2 v) 
                              m"
using assms
by (cases t) auto

lemmas StrengthenedPrefix_casesI =
  StrengthenedPrefix_ifI
  StrengthenedPrefix_letI
  StrengthenedPrefix_prodI
  StrengthenedPrefix_optionI
  StrengthenedPrefix_listI
  StrengthenedPrefix_DataTypeI

lemma StrengthenedPrefix_IsInvariant:
  assumes "\<And>a. IsInvariant (m a) (update_state (StatePart p))"
  shows "StrengthenedPrefix p (read_state (ValuePart p)) m"
using assms
unfolding StrengthenedPrefix_def
unfolding IsInvariant_def ValuePart_def StatePart_def
unfolding monad_def Let_def
by simp

lemma StrengthenedPrefix_IsInvariant_no_ValuePart:
  assumes "\<And>a. m a = m undefined"
      and "\<And>a. IsInvariant (m a) (update_state (StatePart p))"
  shows "StrengthenedPrefix p (return undefined) m"
unfolding StrengthenedPrefix_def
proof clarsimp
  fix s
  assume "ValuePart (m undefined) s"
  thus "ValuePart (bind p m) s"
    using assms(1)[of "ValuePart p s"]
    using assms(2)
    unfolding IsInvariant_def ValuePart_def StatePart_def
    unfolding monad_def Let_def
    by simp
qed

lemma StrengthenedPrefix_IsInvariant_update_state:
  assumes "IsInvariant (m ()) (update_state f)"
  shows "StrengthenedPrefix (update_state f) (return undefined) m"
using assms
by - (rule StrengthenedPrefix_IsInvariant_no_ValuePart, simp_all) 

text \<open>The rule \<open>StrengthenedPrefix_bindI\<close> doesn't play nicely with structural composition ``;'' (the
reason is the combination of instantiating schematic variables and sub-goal scoping). Therefore we
use repeated sequential composition ``,'' in the method below.\<close>

method StrengthenPrefix uses intro = 
  assumption | 
  (rule StrengthenedPrefix_bindI, 
      StrengthenPrefix intro: intro, 
      solves \<open>strong_cong_simp\<close>,
      StrengthenPrefix intro: intro) |
  (rule StrengthenedPrefix_casesI; 
      StrengthenPrefix intro: intro) |
  (rule StrengthenedPrefix_IsInvariant_no_ValuePart, 
      solves \<open>simp\<close>, 
      solves \<open>Invariant intro: intro\<close>) |
  (rule StrengthenedPrefix_IsInvariant, 
      solves \<open>Invariant intro: intro\<close>) |
  (rule StrengthenedPrefix_same_prefix)

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemmas below is testing the proof method.\<close>

lemma
  "StrengthenedPrefix (write'CAPR x) 
                      (write'CAPR x) 
                      (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = cap)))"
by StrengthenPrefix

lemma
  "StrengthenedPrefix (update_state (setPC x))
                      (return undefined) 
                      (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = cap)))"
by StrengthenPrefix

lemma
  "StrengthenedPrefix (bind (write'CAPR x) (\<lambda>_. update_state (setPC y))) 
                      (bind (write'CAPR x) (\<lambda>a. return undefined)) 
                      (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = cap)))"
by StrengthenPrefix

lemma
  "StrengthenedPrefix (if b then (write'CAPR x) else update_state (setPC y)) 
                      (if b then (write'CAPR x) else return undefined) 
                      (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = cap)))"
by StrengthenPrefix

lemma
  assumes "IsInvariant m p"
  shows "StrengthenedPrefix p (return undefined) (\<lambda>_. m)"
using assms
by - StrengthenPrefix

lemma
  assumes "\<And>a. IsInvariant m (p a)"
  shows "StrengthenedPrefix (foreach_loop (l, p))
                            (return undefined) 
                            (\<lambda>_. m)"
using assms
by - StrengthenPrefix

subsection \<open>Proving Hoare triples\<close>

text \<open>Introducing \<open>q'_simp\<close> in the lemma below might seem redundant, but it allows the proof method
to simplify \<open>q'_simp\<close> before using it.\<close>

lemma PrePost_from_pushingBack:
  assumes "\<And>a. SwappingGives (update_state (StatePart m)) (q a) x (q' a)"
      and "q'_simp = (bind (read_state (ValuePart m)) q')"
  shows "PrePost q'_simp m q"
unfolding PrePost_def assms(2)
proof (intro allI impI)
  fix s
  assume *: "ValuePart (bind (read_state (ValuePart m)) q') s"
  have "ValuePart (bind m q) s = 
        ValuePart (bind (read_state (ValuePart m)) 
                        (\<lambda>a. bind (update_state (StatePart m))
                        (\<lambda>_. q a)))
                  s"
    by (simp add: ValuePart_bind StatePart_bind)
  also have "... = ValuePart (bind (read_state (ValuePart m)) q') s"
    using assms
    unfolding SwappingGives_def
    by (simp add: ValuePart_bind StatePart_bind)
  finally show "ValuePart (bind m q) s"
    using * by simp
qed

lemma PrePost_update_state_from_pushingBack:
  assumes "SwappingGives (update_state f) q x q'"
  shows "PrePost q' (update_state f) (\<lambda>_. q)"
using assms
unfolding SwappingGives_def PrePost_def
by (simp add: ValuePart_bind StatePart_bind)

lemma PrePost_from_StrengthenedPrefix:
  assumes "StrengthenedPrefix m m' q"
  shows "PrePost (bind m' q) m q"
using assms
unfolding StrengthenedPrefix_def PrePost_def .

lemmas PrePost_from_StrengthenedPrefix_cases_arity_2 =
  PrePost_from_StrengthenedPrefix[where m="If _ _ _"]
  PrePost_from_StrengthenedPrefix[where m="case_option _ _ _"]
  PrePost_from_StrengthenedPrefix[where m="case_list _ _ _"]
  PrePost_from_StrengthenedPrefix[where m="case_DataType _ _ _"]

lemmas PrePost_casesI = 
  all_split[where P="\<lambda>x. PrePost p x q", THEN iffD2] for p q

method PrePost_cases =
  rule PrePost_casesI; 
  (intro conjI impI allI)?;
  PrePost_cases?
     
method ParametricPrePost methods f uses simp =
  PrePost_cases?;
  rule PrePost_pre_strengthening,
  f, 
  strong_cong_simp_all add: ValueAndStatePart_simp simp

method ComputePreAuto uses simp =
  auto simp: ValueAndStatePart_simp simp 
       cong del: weak_cong cong: cong
       split: option.splits

method ComputePre methods compositeI atomI uses intro simp = 

  -- \<open>If the post condition is @{term "return True"} then we use the following rule.\<close>
  (rule IsInvariant_constant[where x=True]) |

  -- \<open>We try the supplied method for composites (@{const bind}, cases, loops and the empty
      composite @{const return}).\<close>
  solves \<open>compositeI\<close> |
  -- \<open>If that did not work, we handle composites in a general way.\<close>
  (rule PrePost_weakest_pre_return) |
  (rule PrePost_weakest_pre_bind,
      ComputePre compositeI atomI intro: intro simp: simp,
      solves \<open>strong_cong_simp add: simp\<close>,
      ComputePre compositeI atomI intro: intro simp: simp) |
  (rule PrePost_weakest_pre_cases;
      ComputePre compositeI atomI intro: intro simp: simp) |
  -- \<open>If the loop is IsInvariant under the post condition we can remove the loop.\<close>
  (rule IsInvariant_foreach_loop,
      ParametricPrePost \<open>ComputePre compositeI atomI intro: intro simp: simp\<close> simp: simp;
      solves \<open>ComputePreAuto simp: simp\<close>) |
  (rule PrePost_splitValueAndStatePart_foreach_loop_agg,
      rule IsInvariant_foreach_loop_agg,
      ParametricPrePost \<open>ComputePre compositeI atomI intro: intro simp: simp\<close> simp: simp;
      solves \<open>ComputePreAuto simp: simp\<close>) |
  -- \<open>Otherwise, we append the loop to the precondition.\<close>
  (rule PrePost_weakest_pre_foreach_loop
        PrePost_weakest_pre_foreach_loop_agg) |

  -- \<open>Then we try the supplied method for atoms (@{const read_state}, @{const update_state} and
      CHERI functions).\<close>
  solves \<open>atomI\<close> |
  -- \<open>We decompose the monadic connectives.\<close>
  (rule PrePost_weakest_pre_conj PrePost_weakest_pre_disj;
      ComputePre compositeI atomI intro: intro simp: simp) |
  (rule PrePost_weakest_pre_not PrePost_weakest_pre_equals,
      solves \<open>strong_cong_simp add: simp\<close>,
      ComputePre compositeI atomI intro: intro simp: simp) |
  -- \<open>If that did not work, we handle atoms in a general way.\<close>
  (rule PrePost_weakest_pre_read_state) |
  (rule PrePost_update_state_from_pushingBack,
      solves \<open>PushBackwards intro: intro simp: simp\<close>) | 
  (rule PrePost_from_pushingBack,
      solves \<open>PushBackwards intro: intro simp: simp\<close>,
      solves \<open>strong_cong_simp add: simp\<close>)

text \<open>The following method corresponds to @\<open>method ComputePre\<close> without any recursive calls. The
purpose is to step through the method when debugging.\<close>

method ComputePre_debug_step methods compositeI atomI uses intro simp = 
  (rule IsInvariant_constant[where x=True]) |
  solves \<open>compositeI\<close> |
  (rule PrePost_weakest_pre_return) |
  (rule PrePost_weakest_pre_bind) |
  (rule PrePost_weakest_pre_cases) |
  (rule IsInvariant_foreach_loop,
      ParametricPrePost \<open>ComputePre compositeI atomI intro: intro simp: simp\<close> simp: simp;
      solves \<open>ComputePreAuto simp: simp\<close>) |
  (rule PrePost_splitValueAndStatePart_foreach_loop_agg,
      rule IsInvariant_foreach_loop_agg,
      ParametricPrePost \<open>ComputePre compositeI atomI intro: intro simp: simp\<close> simp: simp;
      solves \<open>ComputePreAuto simp: simp\<close>) |
  solves \<open>atomI\<close> |
  (rule PrePost_weakest_pre_conj PrePost_weakest_pre_disj) |
  (rule PrePost_weakest_pre_not PrePost_weakest_pre_equals) |
  (rule PrePost_weakest_pre_read_state) |
  (rule PrePost_update_state_from_pushingBack,
      solves \<open>PushBackwards intro: intro\<close>) | 
  (rule PrePost_from_pushingBack,
      solves \<open>PushBackwards intro: intro\<close>,
      solves \<open>strong_cong_simp add: simp\<close>) | 
  solves \<open>strong_cong_simp add: simp\<close>

method ComputePreDefault uses intro simp =
  ComputePre \<open>rule TrueI intro;
              solves \<open>ComputePreAuto simp: simp\<close>\<close> 
             fail 
             intro: intro simp: simp

method ComputePreDefault_debug_step uses intro simp =
  ComputePre_debug_step \<open>rule TrueI intro;
                         solves \<open>ComputePreAuto simp: simp\<close>\<close> 
                        fail 
                        intro: intro simp: simp

method ComputePreNoExplosion methods compositeI atomI uses intro simp =
  ComputePre \<open>compositeI |
              (rule PrePost_weakest_pre_cases_arity_1, 
                  ComputePreNoExplosion compositeI atomI intro: intro simp: simp) |
              (rule PrePost_from_StrengthenedPrefix_cases_arity_2,
                  solves \<open>StrengthenPrefix\<close>)\<close> 
              atomI
              intro: intro simp: simp

method ComputePreNoExplosionDefault uses intro simp =
  ComputePreNoExplosion \<open>rule TrueI intro;
                          solves \<open>ComputePreAuto simp: simp\<close>\<close> 
                         fail 
                         intro: intro simp: simp

method PrePost uses intro simp = 
  ParametricPrePost \<open>ComputePreDefault intro: intro simp: simp\<close> simp: simp

method PrePostNoExplosion uses intro simp =
  ParametricPrePost \<open>ComputePreNoExplosionDefault intro: intro simp: simp\<close> simp: simp

subsubsection \<open>Tests\<close>

text \<open>The purpose of the lemmas below is testing the proof method.\<close>

lemma "PrePost (return True)
               (bind (write'CAPR (cap, cd)) (\<lambda>_. write'PCC y)) 
               (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = (if cd = 0 then nullCap else cap))))"
proof -
  have [simp]: "bind (update_state (StatePart (write'CAPR (cap, cd)))) 
                     (\<lambda>_. CAPR cd) =
                bind (update_state (StatePart (write'CAPR (cap, cd)))) 
                     (\<lambda>_. return (if cd = 0 then nullCap else cap))" for cap cd
    unfolding write'CAPR_alt_def CAPR_alt_def StatePart_def
    unfolding monad_def Let_def
    by simp
  show ?thesis
    by PrePost
qed

lemma "IsInvariant (bind (CAPR cd) (\<lambda>a. return (a = cap))) (write'PCC x)"
by PrePost

lemma "IsInvariant (bind (read_state getPC) (\<lambda>a. return (a = pc))) (write'PCC x)"
by PrePost

lemma "IsInvariant (bind (CAPR cd) (\<lambda>a. return (a = cap)) \<and>\<^sub>b
                  bind (read_state getPC) (\<lambda>a. return (a = pc))) 
                 (write'PCC x)"
by PrePost

lemma 
  assumes "\<And>a. IsInvariant p (m a)"
  shows "IsInvariant p (foreach_loop (l, m))"
by (PrePost intro: assms)

lemma "PrePost (bind (CAPR cd) (\<lambda>a. return (a = cap))) 
               (write'PCC x)
               (\<lambda>_. return True)"
by PrePost 

lemma "PrePost (return False) 
               (write'PCC x)
               (\<lambda>_. bind (CAPR cd) (\<lambda>a. return (a = cap))) "
by PrePost 

(*<*)
end
(*>*)