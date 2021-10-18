(*<*) 

(* Author: Kyndylan Nienhuis *)

theory RestrictCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
  "Execute"
begin

(*>*)
section \<open>Semantics of @{const RestrictCapAction}}\<close>

subsection \<open>Derivations of @{const TakeBranch}\<close>

named_theorems SemanticsRestrict_BranchI
  
method SemanticsRestrict_Branch uses intro =
  Invariant intro: intro SemanticsRestrict_BranchI

definition SemanticsRestrict_Branch where
  "SemanticsRestrict_Branch cap r r' \<equiv>
   bind (read_state getBranchDelayPccCap)
        (\<lambda>cap'. bind TakeBranchActions
        (\<lambda>prov. return ((cap' = cap) \<and> RestrictCapAction r r' \<in> prov)))"

lemma SemanticsRestrict_Branch_StatePart [simp]:
  shows "StatePart (SemanticsRestrict_Branch cap r r') s = s"
unfolding SemanticsRestrict_Branch_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_SemanticsRestrict_Branch [Commute_compositeI]:
  assumes "Commute (read_state BranchDelayPCC) m"
  shows "Commute (SemanticsRestrict_Branch cap r r') m"
unfolding SemanticsRestrict_Branch_def
by (Commute intro: assms)

(* Code generation - start - SemanticsRestrict *)

(* Code generation - override - raise'exception *)

lemma SemanticsRestrict_Branch_raise'exception [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                    read_state isUnpredictable \<or>\<^sub>b 
                    SemanticsRestrict_Branch cap r r')
                 (raise'exception (UNPREDICTABLE v))"
by PrePost

(* Code generation - end override *)

lemma SemanticsRestrict_Branch_CheckBranch [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 CheckBranch"
unfolding CheckBranch_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_BranchNotTaken [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 BranchNotTaken"
unfolding BranchNotTaken_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_BranchLikelyNotTaken [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 BranchLikelyNotTaken"
unfolding BranchLikelyNotTaken_alt_def
by SemanticsRestrict_Branch

(* Code generation - override - SignalException *)

lemma SemanticsRestrict_Branch_SignalException [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                    read_state isUnpredictable \<or>\<^sub>b 
                    SemanticsRestrict_Branch cap r r')
                 (SignalException v)"
by PrePost

(* Code generation - end override *)

lemma SemanticsRestrict_Branch_SignalCP2UnusableException [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 SignalCP2UnusableException"
unfolding SignalCP2UnusableException_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_SignalCapException_internal [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (SignalCapException_internal v)"
unfolding SignalCapException_internal_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_SignalCapException [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (SignalCapException v)"
unfolding SignalCapException_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_SignalCapException_noReg [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (SignalCapException_noReg v)"
unfolding SignalCapException_noReg_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ERET [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'ERET"
unfolding dfn'ERET_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_SignalTLBException [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (SignalTLBException v)"
unfolding SignalTLBException_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_check_cca [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (check_cca v)"
unfolding check_cca_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_AddressTranslation [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (AddressTranslation v)"
unfolding AddressTranslation_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_SignalTLBCapException [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (SignalTLBCapException v)"
unfolding SignalTLBCapException_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_AdjustEndian [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (AdjustEndian v)"
unfolding AdjustEndian_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_LoadMemoryCap [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (LoadMemoryCap v)"
unfolding LoadMemoryCap_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_LoadMemory [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (LoadMemory v)"
unfolding LoadMemory_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_LoadCap [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (LoadCap v)"
unfolding LoadCap_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_StoreMemoryCap [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (StoreMemoryCap v)"
unfolding StoreMemoryCap_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_StoreMemory [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (StoreMemory v)"
unfolding StoreMemory_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_StoreCap [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (StoreCap v)"
unfolding StoreCap_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_Fetch [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 Fetch"
unfolding Fetch_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_write'CP0R [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (write'CP0R v)"
unfolding write'CP0R_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_mtc [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (mtc v)"
unfolding mtc_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dmtc [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dmtc v)"
unfolding dmtc_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_mfc [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (mfc v)"
unfolding mfc_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dmfc [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dmfc v)"
unfolding dmfc_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ADDI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ADDI v)"
unfolding dfn'ADDI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ADDIU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ADDIU v)"
unfolding dfn'ADDIU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DADDI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DADDI v)"
unfolding dfn'DADDI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DADDIU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DADDIU v)"
unfolding dfn'DADDIU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLTI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLTI v)"
unfolding dfn'SLTI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLTIU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLTIU v)"
unfolding dfn'SLTIU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ANDI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ANDI v)"
unfolding dfn'ANDI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ORI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ORI v)"
unfolding dfn'ORI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'XORI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'XORI v)"
unfolding dfn'XORI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LUI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LUI v)"
unfolding dfn'LUI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ADD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ADD v)"
unfolding dfn'ADD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ADDU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ADDU v)"
unfolding dfn'ADDU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SUB [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SUB v)"
unfolding dfn'SUB_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SUBU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SUBU v)"
unfolding dfn'SUBU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DADD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DADD v)"
unfolding dfn'DADD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DADDU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DADDU v)"
unfolding dfn'DADDU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSUB [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSUB v)"
unfolding dfn'DSUB_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSUBU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSUBU v)"
unfolding dfn'DSUBU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLT [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLT v)"
unfolding dfn'SLT_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLTU v)"
unfolding dfn'SLTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'AND [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'AND v)"
unfolding dfn'AND_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'OR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'OR v)"
unfolding dfn'OR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'XOR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'XOR v)"
unfolding dfn'XOR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'NOR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'NOR v)"
unfolding dfn'NOR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MOVN [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MOVN v)"
unfolding dfn'MOVN_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MOVZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MOVZ v)"
unfolding dfn'MOVZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MADD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MADD v)"
unfolding dfn'MADD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MADDU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MADDU v)"
unfolding dfn'MADDU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MSUB [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MSUB v)"
unfolding dfn'MSUB_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MSUBU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MSUBU v)"
unfolding dfn'MSUBU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MUL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MUL v)"
unfolding dfn'MUL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MULT [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MULT v)"
unfolding dfn'MULT_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MULTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MULTU v)"
unfolding dfn'MULTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DMULT [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DMULT v)"
unfolding dfn'DMULT_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DMULTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DMULTU v)"
unfolding dfn'DMULTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DIV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DIV v)"
unfolding dfn'DIV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DIVU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DIVU v)"
unfolding dfn'DIVU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DDIV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DDIV v)"
unfolding dfn'DDIV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DDIVU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DDIVU v)"
unfolding dfn'DDIVU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MFHI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MFHI v)"
unfolding dfn'MFHI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MFLO [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MFLO v)"
unfolding dfn'MFLO_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MTHI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MTHI v)"
unfolding dfn'MTHI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MTLO [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MTLO v)"
unfolding dfn'MTLO_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLL v)"
unfolding dfn'SLL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SRL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SRL v)"
unfolding dfn'SRL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SRA [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SRA v)"
unfolding dfn'SRA_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SLLV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SLLV v)"
unfolding dfn'SLLV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SRLV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SRLV v)"
unfolding dfn'SRLV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SRAV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SRAV v)"
unfolding dfn'SRAV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSLL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSLL v)"
unfolding dfn'DSLL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRL v)"
unfolding dfn'DSRL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRA [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRA v)"
unfolding dfn'DSRA_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSLLV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSLLV v)"
unfolding dfn'DSLLV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRLV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRLV v)"
unfolding dfn'DSRLV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRAV [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRAV v)"
unfolding dfn'DSRAV_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSLL32 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSLL32 v)"
unfolding dfn'DSLL32_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRL32 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRL32 v)"
unfolding dfn'DSRL32_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DSRA32 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DSRA32 v)"
unfolding dfn'DSRA32_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TGE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TGE v)"
unfolding dfn'TGE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TGEU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TGEU v)"
unfolding dfn'TGEU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLT [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TLT v)"
unfolding dfn'TLT_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TLTU v)"
unfolding dfn'TLTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TEQ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TEQ v)"
unfolding dfn'TEQ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TNE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TNE v)"
unfolding dfn'TNE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TGEI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TGEI v)"
unfolding dfn'TGEI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TGEIU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TGEIU v)"
unfolding dfn'TGEIU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLTI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TLTI v)"
unfolding dfn'TLTI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLTIU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TLTIU v)"
unfolding dfn'TLTIU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TEQI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TEQI v)"
unfolding dfn'TEQI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TNEI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'TNEI v)"
unfolding dfn'TNEI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_loadByte [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (loadByte v)"
unfolding loadByte_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_loadHalf [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (loadHalf v)"
unfolding loadHalf_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_loadWord [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (loadWord v)"
unfolding loadWord_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_loadDoubleword [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (loadDoubleword v)"
unfolding loadDoubleword_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LB [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LB v)"
unfolding dfn'LB_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LBU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LBU v)"
unfolding dfn'LBU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LH [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LH v)"
unfolding dfn'LH_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LHU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LHU v)"
unfolding dfn'LHU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LW [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LW v)"
unfolding dfn'LW_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LWU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LWU v)"
unfolding dfn'LWU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LL v)"
unfolding dfn'LL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LD v)"
unfolding dfn'LD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LLD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LLD v)"
unfolding dfn'LLD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LWL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LWL v)"
unfolding dfn'LWL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LWR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LWR v)"
unfolding dfn'LWR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LDL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LDL v)"
unfolding dfn'LDL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'LDR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'LDR v)"
unfolding dfn'LDR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SB [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SB v)"
unfolding dfn'SB_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SH [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SH v)"
unfolding dfn'SH_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_storeWord [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (storeWord v)"
unfolding storeWord_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_storeDoubleword [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (storeDoubleword v)"
unfolding storeDoubleword_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SW [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SW v)"
unfolding dfn'SW_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SD v)"
unfolding dfn'SD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SC v)"
unfolding dfn'SC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SCD [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SCD v)"
unfolding dfn'SCD_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SWL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SWL v)"
unfolding dfn'SWL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SWR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SWR v)"
unfolding dfn'SWR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SDL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SDL v)"
unfolding dfn'SDL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SDR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'SDR v)"
unfolding dfn'SDR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BREAK [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'BREAK"
unfolding dfn'BREAK_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'SYSCALL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'SYSCALL"
unfolding dfn'SYSCALL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MTC0 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MTC0 v)"
unfolding dfn'MTC0_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DMTC0 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DMTC0 v)"
unfolding dfn'DMTC0_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'MFC0 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'MFC0 v)"
unfolding dfn'MFC0_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'DMFC0 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'DMFC0 v)"
unfolding dfn'DMFC0_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'J [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'J v)"
unfolding dfn'J_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'JAL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'JAL v)"
unfolding dfn'JAL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'JALR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'JALR v)"
unfolding dfn'JALR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'JR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'JR v)"
unfolding dfn'JR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BEQ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BEQ v)"
unfolding dfn'BEQ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BNE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BNE v)"
unfolding dfn'BNE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLEZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLEZ v)"
unfolding dfn'BLEZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGTZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGTZ v)"
unfolding dfn'BGTZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLTZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLTZ v)"
unfolding dfn'BLTZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGEZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGEZ v)"
unfolding dfn'BGEZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLTZAL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLTZAL v)"
unfolding dfn'BLTZAL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGEZAL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGEZAL v)"
unfolding dfn'BGEZAL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BEQL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BEQL v)"
unfolding dfn'BEQL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BNEL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BNEL v)"
unfolding dfn'BNEL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLEZL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLEZL v)"
unfolding dfn'BLEZL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGTZL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGTZL v)"
unfolding dfn'BGTZL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLTZL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLTZL v)"
unfolding dfn'BLTZL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGEZL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGEZL v)"
unfolding dfn'BGEZL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BLTZALL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BLTZALL v)"
unfolding dfn'BLTZALL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'BGEZALL [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'BGEZALL v)"
unfolding dfn'BGEZALL_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'RDHWR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'RDHWR v)"
unfolding dfn'RDHWR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CACHE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CACHE v)"
unfolding dfn'CACHE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ReservedInstruction [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'ReservedInstruction"
unfolding dfn'ReservedInstruction_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'Unpredictable [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'Unpredictable"
unfolding dfn'Unpredictable_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLBP [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'TLBP"
unfolding dfn'TLBP_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLBR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'TLBR"
unfolding dfn'TLBR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLBWI [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'TLBWI"
unfolding dfn'TLBWI_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'TLBWR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'TLBWR"
unfolding dfn'TLBWR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'COP1 [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'COP1 v)"
unfolding dfn'COP1_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetBase [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetBase v)"
unfolding dfn'CGetBase_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetOffset [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetOffset v)"
unfolding dfn'CGetOffset_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetLen [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetLen v)"
unfolding dfn'CGetLen_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetTag [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetTag v)"
unfolding dfn'CGetTag_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetSealed [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetSealed v)"
unfolding dfn'CGetSealed_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetPerm [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetPerm v)"
unfolding dfn'CGetPerm_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetType [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetType v)"
unfolding dfn'CGetType_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetAddr [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetAddr v)"
unfolding dfn'CGetAddr_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetPCC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetPCC v)"
unfolding dfn'CGetPCC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetPCCSetOffset [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetPCCSetOffset v)"
unfolding dfn'CGetPCCSetOffset_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CGetCause [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CGetCause v)"
unfolding dfn'CGetCause_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSetCause [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSetCause v)"
unfolding dfn'CSetCause_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CIncOffset [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CIncOffset v)"
unfolding dfn'CIncOffset_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CIncOffsetImmediate [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CIncOffsetImmediate v)"
unfolding dfn'CIncOffsetImmediate_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSetBounds [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSetBounds v)"
unfolding dfn'CSetBounds_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSetBoundsExact [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSetBoundsExact v)"
unfolding dfn'CSetBoundsExact_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSetBoundsImmediate [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSetBoundsImmediate v)"
unfolding dfn'CSetBoundsImmediate_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_ClearRegs [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (ClearRegs v)"
unfolding ClearRegs_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ClearLo [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ClearLo v)"
unfolding dfn'ClearLo_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'ClearHi [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'ClearHi v)"
unfolding dfn'ClearHi_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CClearLo [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CClearLo v)"
unfolding dfn'CClearLo_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CClearHi [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CClearHi v)"
unfolding dfn'CClearHi_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CClearTag [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CClearTag v)"
unfolding dfn'CClearTag_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CAndPerm [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CAndPerm v)"
unfolding dfn'CAndPerm_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSetOffset [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSetOffset v)"
unfolding dfn'CSetOffset_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSub [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSub v)"
unfolding dfn'CSub_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CCheckPerm [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CCheckPerm v)"
unfolding dfn'CCheckPerm_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CCheckType [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CCheckType v)"
unfolding dfn'CCheckType_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CFromPtr [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CFromPtr v)"
unfolding dfn'CFromPtr_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CToPtr [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CToPtr v)"
unfolding dfn'CToPtr_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_CPtrCmp [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (CPtrCmp v)"
unfolding CPtrCmp_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CEQ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CEQ v)"
unfolding dfn'CEQ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CNE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CNE v)"
unfolding dfn'CNE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLT [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLT v)"
unfolding dfn'CLT_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLE [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLE v)"
unfolding dfn'CLE_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLTU v)"
unfolding dfn'CLTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLEU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLEU v)"
unfolding dfn'CLEU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CEXEQ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CEXEQ v)"
unfolding dfn'CEXEQ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CNEXEQ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CNEXEQ v)"
unfolding dfn'CNEXEQ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CBTU [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CBTU v)"
unfolding dfn'CBTU_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CBTS [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CBTS v)"
unfolding dfn'CBTS_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CBEZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CBEZ v)"
unfolding dfn'CBEZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CBNZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CBNZ v)"
unfolding dfn'CBNZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSC v)"
unfolding dfn'CSC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLC v)"
unfolding dfn'CLC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLoad [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLoad v)"
unfolding dfn'CLoad_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_store [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (store v)"
unfolding store_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CStore [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CStore v)"
unfolding dfn'CStore_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLLC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLLC v)"
unfolding dfn'CLLC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CLLx [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CLLx v)"
unfolding dfn'CLLx_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSCC [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSCC v)"
unfolding dfn'CSCC_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSCx [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSCx v)"
unfolding dfn'CSCx_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CMOVN [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CMOVN v)"
unfolding dfn'CMOVN_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CMOVZ [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CMOVZ v)"
unfolding dfn'CMOVZ_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CMove [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CMove v)"
unfolding dfn'CMove_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CTestSubset [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CTestSubset v)"
unfolding dfn'CTestSubset_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CBuildCap [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CBuildCap v)"
unfolding dfn'CBuildCap_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CCopyType [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CCopyType v)"
unfolding dfn'CCopyType_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CJR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CJR v)"
unfolding dfn'CJR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CJALR [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CJALR v)"
unfolding dfn'CJALR_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CSeal [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CSeal v)"
unfolding dfn'CSeal_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CUnseal [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CUnseal v)"
unfolding dfn'CUnseal_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CCall [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CCall v)"
unfolding dfn'CCall_alt_def
by SemanticsRestrict_Branch

(* Code generation - skip - dfn'CCallFast *)

lemma SemanticsRestrict_Branch_dfn'CReadHwr [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CReadHwr v)"
unfolding dfn'CReadHwr_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CWriteHwr [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 (dfn'CWriteHwr v)"
unfolding dfn'CWriteHwr_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'CReturn [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'CReturn"
unfolding dfn'CReturn_alt_def
by SemanticsRestrict_Branch

lemma SemanticsRestrict_Branch_dfn'UnknownCapInstruction [SemanticsRestrict_BranchI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')
                 dfn'UnknownCapInstruction"
unfolding dfn'UnknownCapInstruction_alt_def
by SemanticsRestrict_Branch

(* Code generation - override - Run *)

lemma SemanticsRestrict_Branch_Run_aux1:
  shows "PrePost (SemanticsRestrict_Branch cap r r' \<and>\<^sub>b
                  return (case v of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                  | _ \<Rightarrow> True))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r')"
unfolding Run_alt_def
by (PrePost intro: SemanticsRestrict_BranchI)

lemma SemanticsRestrict_Branch_Run_aux2:
  assumes "ValuePart (SemanticsRestrict_Branch cap r r') s"
  shows "getRegisterIsAccessible r s" "getRegisterIsAccessible r' s"
using assms
unfolding SemanticsRestrict_Branch_def 
unfolding TakeBranchActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma SemanticsRestrict_Branch_Run:
  shows "PrePost ((return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  SemanticsRestrict_Branch cap r r' \<and>\<^sub>b
                  return (case v of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                  | _ \<Rightarrow> True))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Branch cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
  (is "PrePost ?pre _ ?post")
proof (intro PrePostI)
  fix s
  assume "ValuePart ?pre s"
  hence [simp]: "rAccessible = getRegisterIsAccessible r s"
                "r'Accessible = getRegisterIsAccessible r' s"
    by (auto simp: ValueAndStatePart_simp)
  have der: "ValuePart (SemanticsRestrict_Branch cap r r') s"
    using `ValuePart ?pre s`
    by (auto simp: ValueAndStatePart_simp)
  hence access: "getRegisterIsAccessible r s" "getRegisterIsAccessible r' s"
    using SemanticsRestrict_Branch_Run_aux2
    by auto
  thus "ValuePart (bind (Run v) ?post) s"
    using `ValuePart ?pre s`
    using SemanticsRestrict_Branch_Run_aux1
        [where cap=cap and r=r and r'=r' and v=v, THEN PrePostE[where s=s]]
    using der
    by (auto simp: ValueAndStatePart_simp)
qed

(* Code generation - end override *)

(* Code generation - skip - Next *)

(* Code generation - end *)

subsection \<open>Derivations from instructions\<close>

named_theorems SemanticsRestrict_InstructionI

definition SemanticsRestrict_Instruction where
  "SemanticsRestrict_Instruction cap r r' \<equiv>
   (bind (read_state BranchDelayPCC)
         (\<lambda>branchDelay. bind (read_state BranchToPCC)
         (\<lambda>branchTo. bind (read_state (getCapReg r'))
         (\<lambda>cap_loc'. if r' = RegPCC then return ((cap_loc' \<le> cap) \<and> (branchDelay = None))
                     else if r'= RegBranchDelayPCC 
                          then (case branchTo of None \<Rightarrow> return (cap_loc' \<le> cap)
                                               | Some (_, x) \<Rightarrow> return (x \<le> cap))
                     else return (cap_loc' \<le> cap)))))"

lemma SemanticsRestrict_Instruction_StatePart [simp]:
  shows "StatePart (SemanticsRestrict_Instruction cap r r') s = s"
unfolding SemanticsRestrict_Instruction_def
by (strong_cong_simp add: ValueAndStatePart_simp)

lemma Commute_SemanticsRestrict_Instruction [Commute_compositeI]:
  assumes "Commute (read_state getPCC) m"
      and "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state BranchToPCC) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMemCap a)) m"
  shows "Commute (SemanticsRestrict_Instruction cap r r') m"
unfolding SemanticsRestrict_Instruction_def
by (Commute intro: assms)

lemma SemanticsRestrict_Instruction_dfn'ERET [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind ERETActions (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 dfn'ERET
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'ERET_alt_def CheckBranch_alt_def ERETActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: ValueAndStatePart_simp special_register_accessible_alt_def)

lemma SemanticsRestrict_Instruction_dfn'CGetPCC [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                   bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                  bind (CGetPCCActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CGetPCC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CGetPCC_alt_def CheckBranch_alt_def CGetPCCActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CGetPCCSetOffset [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                   bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                  bind (CGetPCCSetOffsetActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CGetPCCSetOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CGetPCCSetOffset_alt_def CheckBranch_alt_def CGetPCCSetOffsetActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CIncOffset [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CIncOffsetActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CIncOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CIncOffset_alt_def CheckBranch_alt_def CIncOffsetActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CIncOffsetImmediate [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CIncOffsetImmediateActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CIncOffsetImmediate v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CIncOffsetImmediate_alt_def CheckBranch_alt_def CIncOffsetImmediateActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CSetBounds [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CSetBoundsActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CSetBounds v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CSetBounds_alt_def CSetBoundsActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost 
   (simple_auto simp: if_splits if_simps(6) not_less 
                      uint_plus_simple word_le_def
                      setBounds_le
                      ValueAndStatePart_simp
                intro: disjCI
                elim: notE[OF _ Region_subsetI])

lemma SemanticsRestrict_Instruction_dfn'CSetBoundsExact [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CSetBoundsExactActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CSetBoundsExact v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CSetBoundsExact_alt_def CSetBoundsExactActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost 
   (simple_auto simp: if_splits if_simps(6) not_less 
                      uint_plus_simple word_le_def
                      setBounds_le
                      ValueAndStatePart_simp
                intro: disjCI
                elim: notE[OF _ Region_subsetI])

lemma SemanticsRestrict_Instruction_dfn'CSetBoundsImmediate [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CSetBoundsImmediateActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CSetBoundsImmediate v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CSetBoundsImmediate_alt_def CSetBoundsImmediateActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost 
   (simple_auto simp: if_splits if_simps(6) not_less 
                      uint_plus_simple word_le_def
                      setBounds_le
                      ValueAndStatePart_simp
                intro: disjCI
                elim: notE[OF _ Region_subsetI])

definition ClearRegLoopPre where
  "ClearRegLoopPre cond l cap r r' \<equiv>
   (bind (read_state BranchDelayPCC)
         (\<lambda>branchDelay. bind (read_state BranchToPCC)
         (\<lambda>branchTo. bind (read_state (getCapReg r'))
         (\<lambda>cap_loc'. case r' of RegPCC \<Rightarrow> 
                                return ((cap_loc' \<le> cap) \<and> (branchDelay = None))
                              | RegBranchDelayPCC \<Rightarrow>
                                (case branchTo of None \<Rightarrow> return (cap_loc' \<le> cap)
                                                | Some (_, x) \<Rightarrow> return (x \<le> cap))
                              | RegGeneral cd \<Rightarrow>
                                return ((\<exists>i\<in>set l. cd = word_of_int (int i) \<and> cond i) \<or>
                                        (cap_loc' \<le> cap))
                              | _ \<Rightarrow> return (cap_loc' \<le> cap)))))"

lemma SemanticsRestrict_Instruction_ClearRegsLoop_aux:
  shows "PrePost (ClearRegLoopPre cond l cap r r')
                 (foreach_loop (l, \<lambda>i. if cond i 
                                       then write'CAPR (nullCap, word_of_int (int i)) 
                                       else return ()))
                 (\<lambda>_. SemanticsRestrict_Instruction cap r r')"
proof (induct l)
  case Nil
  thus ?case
    unfolding PrePost_def
    unfolding ClearRegLoopPre_def
    unfolding SemanticsRestrict_Instruction_def
    by (cases r') (simp_all add: ValueAndStatePart_simp)
next
  case (Cons a l)
  show ?case
    by (auto simp: ValueAndStatePart_simp 
                   ClearRegLoopPre_def
                   PrePost_def[where m="write'CAPR _"]
             intro!: PrePost_weakest_pre_bind[OF Cons refl]
                     PrePost_pre_strengthening[OF Cons]
             split: CapRegister.splits option.splits)   
qed

lemma ExceptionSignalled_ClearRegsLoop:
  shows "IsInvariant (read_state getExceptionSignalled) 
                     (foreach_loop (l, \<lambda>i. if cond i 
                                           then write'CAPR (nullCap, word_of_int (int i)) 
                                           else return ()))"
by PrePost

lemma UndefinedCase_ClearRegsLoop:
  shows "IsInvariant (read_state isUnpredictable) 
                     (foreach_loop (l, \<lambda>i. if cond i 
                                           then write'CAPR (nullCap, word_of_int (int i)) 
                                           else return ()))"
by PrePost

lemmas SemanticsRestrict_Instruction_ClearRegsLoop =
  PrePost_weakest_pre_disj[OF 
    ExceptionSignalled_ClearRegsLoop
    PrePost_weakest_pre_disj[OF 
      UndefinedCase_ClearRegsLoop
      PrePost_weakest_pre_conj[OF 
        SemanticsRestrict_Instruction_ClearRegsLoop_aux
        IsInvariant_constant[where x="rAccessible \<and> r'Accessible"]]]]
  for rAccessible r'Accessible

lemma SemanticsRestrict_Instruction_dfn'CClearHi [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CClearHiActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CClearHi v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
proof -
  note intros = SemanticsRestrict_Instruction_ClearRegsLoop
                  [where rAccessible=rAccessible and r'Accessible=r'Accessible and
                         cap=cap and r=r and r'=r']
  show ?thesis
    unfolding dfn'CClearHi_alt_def CheckBranch_alt_def CClearHiActions_def
    unfolding ClearRegs_alt_def
    by (PrePost intro: intros[THEN PrePost_post_weakening])
       (auto simp: ValueAndStatePart_simp ClearRegLoopPre_def)
qed

lemma SemanticsRestrict_Instruction_dfn'CClearLo [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CClearLoActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CClearLo v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CClearLo_alt_def CheckBranch_alt_def CClearLoActions_def
unfolding ClearRegs_alt_def
by (PrePost simp: ClearRegLoopPre_def
            intro: SemanticsRestrict_Instruction_ClearRegsLoop)
   auto

lemma SemanticsRestrict_Instruction_dfn'CReadHwr [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CReadHwrActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CReadHwr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CReadHwr_alt_def CheckBranch_alt_def CReadHwrActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost auto?

lemma SemanticsRestrict_Instruction_dfn'CWriteHwr [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CWriteHwrActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CWriteHwr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CWriteHwr_alt_def CheckBranch_alt_def CWriteHwrActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost auto?

lemma SemanticsRestrict_Instruction_dfn'CClearTag [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CClearTagActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CClearTag v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CClearTag_alt_def CheckBranch_alt_def CClearTagActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost auto?

lemma SemanticsRestrict_Instruction_CAndPerm [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CAndPermActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CAndPerm v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
proof -
  have trans: "setUPerms (setPerms (c, p), up) \<le> c"
  if "setUPerms (setPerms (c, p), up) \<le> setPerms (c, p)" "setPerms (c, p) \<le> c"
  for c p up
    using preorder_class.order_trans[OF that] .
  show ?thesis
    unfolding dfn'CAndPerm_alt_def CAndPermActions_def
    unfolding SemanticsRestrict_Instruction_def
    by PrePost
       (simple_auto simp: if_splits if_simps(6)
                          setPerms_le setUPerms_le
                          ValueAndStatePart_simp
                    intro: disjCI
                           rec'Perms_AND_leq_forget_right
                           rec'UPerms_AND_leq_forget_right
                    elim: notE[OF _ trans])
qed

lemma SemanticsRestrict_Instruction_dfn'CSetOffset [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CSetOffsetActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CSetOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CSetOffset_alt_def CheckBranch_alt_def CSetOffsetActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CFromPtr [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CFromPtrActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CFromPtr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CFromPtr_alt_def CheckBranch_alt_def CFromPtrActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_LoadCap:
  fixes rAccessible r'Accessible cd
  defines "q \<equiv> bind (read_state (getCAPR cd))
                     (\<lambda>cap. return (\<not> Permit_Load_Capability (getPerms cap) \<and> 
                                    rAccessible \<and> r'Accessible))"
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b
                  read_state isUnpredictable \<or>\<^sub>b 
                  bind (read_state (getTranslateAddr (fst v, LOAD)))
                       (\<lambda>a. case a of None \<Rightarrow> return True
                                    | Some _ \<Rightarrow> q))
                 (LoadCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b 
                      q)"
proof -
  note intro = PrePost_DefinedAddressTranslation[where p="\<lambda>x. q", THEN PrePost_post_weakening]
  show ?thesis
    unfolding LoadCap_alt_def
    by (PrePost simp: q_def intro: intro) auto?
qed

lemma SemanticsRestrict_Instruction_dfn'CLC [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CLCActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
  (is "PrePost ?pre _ ?post")
proof (intro PrePostI)
  fix s
  assume pre: "ValuePart ?pre s"
  have [simp]: "r = (case v of (cd, cb, rt, offset) \<Rightarrow> RegGeneral cd)"
               "r' = (case v of (cd, cb, rt, offset) \<Rightarrow> RegGeneral cd)"
    using pre
    unfolding CLCActions_def
    by (auto simp: ValueAndStatePart_simp
             split: option.splits if_splits)
  note intro = SemanticsRestrict_Instruction_LoadCap
                 [where rAccessible=rAccessible and r'Accessible=r'Accessible, 
                  THEN PrePost_post_weakening]
  -- \<open>It is a bit backward to first assume the precondition and then prove the entire Hoare triple
      instead of proving the post condition. The reason we do this is so we can use the proof 
      methods that work on Hoare triples, while we already simplify r and r' based on the pre
      condition.\<close>
  have "PrePost ?pre (dfn'CLC v) ?post"
    unfolding dfn'CLC_alt_def CheckBranch_alt_def CLCActions_def
    unfolding SemanticsRestrict_Instruction_def
    by (cases v, simp, PrePost intro: intro)
       (auto split: option.splits)
  thus "ValuePart (bind (dfn'CLC v) ?post) s"
    unfolding PrePost_def
    using pre
    by auto
qed

lemma SemanticsRestrict_Instruction_dfn'CLLC [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CLLCActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CLLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
  (is "PrePost ?pre _ ?post")
proof (intro PrePostI)
  fix s
  assume pre: "ValuePart ?pre s"
  have [simp]: "r = (case v of (cd, cb) \<Rightarrow> RegGeneral cd)"
               "r' = (case v of (cd, cb) \<Rightarrow> RegGeneral cd)"
    using pre
    unfolding CLLCActions_def
    by (auto simp: ValueAndStatePart_simp
             split: option.splits if_splits)
  note intro = SemanticsRestrict_Instruction_LoadCap
                 [where rAccessible=rAccessible and r'Accessible=r'Accessible, 
                  THEN PrePost_post_weakening]
  -- \<open>It is a bit backward to first assume the precondition and then prove the entire Hoare triple
      instead of proving the post condition. The reason we do this is so we can use the proof 
      methods that work on Hoare triples, while we already simplify r and r' based on the pre
      condition.\<close>
  have "PrePost ?pre (dfn'CLLC v) ?post"
    unfolding dfn'CLLC_alt_def CheckBranch_alt_def CLLCActions_def
    unfolding SemanticsRestrict_Instruction_def
    by (cases v, simp, PrePost intro: intro)
       (auto split: option.splits)
  thus "ValuePart (bind (dfn'CLLC v) ?post) s"
    unfolding PrePost_def
    using pre
    by auto
qed

lemma SemanticsRestrict_Instruction_dfn'CMOVN [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CMOVNActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CMOVN v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CMOVN_alt_def CheckBranch_alt_def CMOVNActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: ValueAndStatePart_simp split: CapLocation.splits)

lemma SemanticsRestrict_Instruction_dfn'CMOVZ [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CMOVZActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CMOVZ v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CMOVZ_alt_def CMOVZActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: ValueAndStatePart_simp split: if_splits CapLocation.splits)

lemma SemanticsRestrict_Instruction_dfn'CMove [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CMoveActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CMove v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CMove_alt_def CheckBranch_alt_def CMoveActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost auto?

lemma SemanticsRestrict_Instruction_dfn'CBuildCap [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CBuildCapActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CBuildCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CBuildCap_alt_def CheckBranch_alt_def CBuildCapActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost
   (auto simp: ValueAndStatePart_simp not_le not_less word_le_def ucast_and
               less_eq_Capability_ext_def less_eq_Capability_def
               less_eq_Perms_ext_def less_eq_Perms_def
               less_eq_UPerms_ext_def less_eq_UPerms_def
               uint_sub_lem
               bitwise_semilattice_inf.inf.absorb_iff1
         intro!: Region_subsetI
         dest!: arg_cong[where f="\<lambda>x. (ucast x::32 word)" and y="ucast (reg'Perms _)"]
                arg_cong[where f="\<lambda>x. (ucast x::32 word)" and y="ucast (reg'UPerms _)"])

lemma SemanticsRestrict_Instruction_dfn'CCopyType [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CCopyTypeActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CCopyType v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CCopyType_alt_def CheckBranch_alt_def CCopyTypeActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_dfn'CJR [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  bind (CJRActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CJR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CJR_alt_def CheckBranch_alt_def CJRActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost auto?

lemma SemanticsRestrict_Instruction_dfn'CJALR [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                   bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                  bind (CJALRActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (dfn'CJALR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding dfn'CJALR_alt_def CheckBranch_alt_def CJALRActions_def
unfolding SemanticsRestrict_Instruction_def
by PrePost (auto simp: setOffset_le)

lemma SemanticsRestrict_Instruction_Run [SemanticsRestrict_InstructionI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                   bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      SemanticsRestrict_Instruction cap r r' \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding Run_alt_def RunActions_def
by (PrePost_cases;
    rule PrePost_pre_strengthening,
    rule SemanticsRestrict_InstructionI
         PrePost_weakest_pre_any,
    solves \<open>auto simp: ValueAndStatePart_simp\<close>)

subsection \<open>SemanticsRestrict\<close>  

lemma SemanticsRestrict_TakeBranch:
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b 
                  read_state isUnpredictable \<or>\<^sub>b 
                  (SemanticsRestrict_Branch cap r r' \<or>\<^sub>b 
                   SemanticsRestrict_Instruction cap r r') \<and>\<^sub>b
                  return (rAccessible \<and> r'Accessible))
                 TakeBranch
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      bind (read_state (getCapReg r'))
                           (\<lambda>cap'. return (cap' \<le> cap)) \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
unfolding SemanticsRestrict_Branch_def SemanticsRestrict_Instruction_def
unfolding TakeBranch_def TakeBranchActions_def
by PrePost
   (auto simp: ValueAndStatePart_simp getBranchDelayPccCap_def 
         split: option.splits if_splits)

lemmas SemanticsRestrict_Run =
  PrePost_weakest_pre_disj[OF 
    UndefinedCase_Run
    PrePost_weakest_pre_disj[OF 
      SemanticsRestrict_Branch_Run
        [where cap=cap and r=r and r'=r' and rAccessible=rAccessible and r'Accessible=r'Accessible]
      SemanticsRestrict_Instruction_Run
        [where cap=cap and r=r and r'=r' and rAccessible=rAccessible and r'Accessible=r'Accessible]]]
  for cap r r' rAccessible r'Accessible

lemma SemanticsRestrict_Fetch:
  fixes cap r r' rAccessible r'Accessible
  defines "p \<equiv> \<lambda>w. ((return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                     (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                     return (case Decode w of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                            | _ \<Rightarrow> True) \<and>\<^sub>b 
                     bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                     (SemanticsRestrict_Branch cap r r' \<or>\<^sub>b 
                      ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                       bind (RunActions (Decode w)) (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemma SemanticsRestrict_Branch_getCap:
  assumes "RestrictCapAction r r' \<in> ValuePart TakeBranchActions s"
  shows "ValuePart (SemanticsRestrict_Branch (getCapReg r s) r r') s"
using assms
unfolding SemanticsRestrict_Branch_def TakeBranchActions_def
by (auto simp add: ValueAndStatePart_simp split: if_splits)

lemma SemanticsRestrict_NextWithGhostState:
  shows "PrePost ((return cap =\<^sub>b read_state (getCapReg r)) \<and>\<^sub>b
                  (return rAccessible =\<^sub>b RegisterIsAccessible r) \<and>\<^sub>b
                  (return r'Accessible =\<^sub>b RegisterIsAccessible r') \<and>\<^sub>b
                  (read_state CCallFastInstructionParam =\<^sub>b return None) \<and>\<^sub>b
                   bind (read_state getPCC) (\<lambda>cap. return (\<not> getSealed cap)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>prov. return (RestrictCapAction r r' \<in> prov)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      bind (read_state (getCapReg r')) (\<lambda>cap'. return (cap' \<le> cap)) \<and>\<^sub>b
                      return (rAccessible \<and> r'Accessible))"
proof -
  note intros = SemanticsRestrict_Run[where cap=cap and r=r and r'=r' and
                                     rAccessible=rAccessible and
                                     r'Accessible=r'Accessible]
                SemanticsRestrict_Fetch[where cap=cap and r=r and r'=r' and
                                        rAccessible=rAccessible and
                                        r'Accessible=r'Accessible]
                SemanticsRestrict_TakeBranch[where cap=cap and r=r and r'=r' and
                                             rAccessible=rAccessible and
                                             r'Accessible=r'Accessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (PrePost intro: intros[THEN PrePost_post_weakening])
       (auto split: option.splits 
             elim!: SemanticsRestrict_Branch_getCap CCallFastInstructionParam_None)
qed

theorem SemanticsRestrictCap:
  assumes prov: "RestrictCapAction r r' \<in> actions"
      and valid: "getStateIsValid s"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "getCapReg r' s' \<le> getCapReg r s"
        "getRegisterIsAccessible r s"
        "getRegisterIsAccessible r' s"
using assms
using SemanticsRestrict_NextWithGhostState
         [where cap="getCapReg r s" and r=r and r'=r' and
                rAccessible="getRegisterIsAccessible r s" and
                r'Accessible="getRegisterIsAccessible r' s",
          THEN PrePostE[where s=s]]
using SemanticsExecute[OF suc] prov
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary RestrictCapInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "RestrictCapProp s lbl s'"
unfolding RestrictCapProp_def
using assms SemanticsRestrictCap
by auto

(*<*)
end
(*>*)