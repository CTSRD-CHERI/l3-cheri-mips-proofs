(*<*) 

(* Author: Kyndylan Nienhuis *)

theory Exception

imports 
  "ExecutionStep"
begin

(*>*)
section \<open>Effects of @{const RaiseException}}\<close>

definition ExceptionOccurredPre where 
  "ExceptionOccurredPre exl pc pcc capr scapr mem \<equiv> 
   (return exl =\<^sub>b read_state getCP0StatusEXL) \<and>\<^sub>b
   (return pc =\<^sub>b read_state getPC) \<and>\<^sub>b
   (return pcc =\<^sub>b read_state getPCC) \<and>\<^sub>b
   (return capr =\<^sub>b read_state (\<lambda>s cd. getCAPR cd s)) \<and>\<^sub>b
   (return scapr =\<^sub>b read_state (\<lambda>s cd. getSCAPR cd s)) \<and>\<^sub>b
   (return mem =\<^sub>b read_state (\<lambda>s a. getMEM a s))"

abbreviation "getExceptionOccurredPre exl pc pcc capr scapr mem \<equiv>
              ValuePart (ExceptionOccurredPre exl pc pcc capr scapr mem)"

lemma getExceptionOccurredPreI [intro!, simp]:
  shows "getExceptionOccurredPre (getCP0StatusEXL s) 
                                 (getPC s)
                                 (getPCC s)
                                 (\<lambda>cd. getCAPR cd s)
                                 (\<lambda>cd. getSCAPR cd s)
                                 (\<lambda>a. getMEM a s)
                                 s"
unfolding ExceptionOccurredPre_def
by (simp add: ValueAndStatePart_simp)

lemma Commute_getExceptionOccurredPre [Commute_compositeI]:
  assumes "Commute (read_state getCP0StatusEXL) m"
      and "Commute (read_state getPC) m"
      and "Commute (read_state getPCC) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMEM a)) m"
  shows "Commute (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) m"
unfolding ExceptionOccurredPre_def
by (Commute intro: assms)

definition ExceptionOccurredPost where
  "ExceptionOccurredPost exl pc pcc capr scapr mem \<equiv>
   (read_state getCP0StatusEXL) \<and>\<^sub>b
   (bind (read_state getPCC)
         (\<lambda>pcc. bind (read_state getPC)
         (\<lambda>pc. return (getBase pcc + pc \<in> ExceptionPCs)))) \<and>\<^sub>b
   (read_state getPCC =\<^sub>b return (scapr 29)) \<and>\<^sub>b
   (\<forall>\<^sub>bcd. read_state (getCAPR cd) =\<^sub>b return (capr cd)) \<and>\<^sub>b
   (\<forall>\<^sub>bcd. read_state (getSCAPR cd) =\<^sub>b 
          return (if cd = 31 \<and> \<not> exl
                  then setOffset (pcc, pc) 
                  else scapr cd)) \<and>\<^sub>b
   (\<forall>\<^sub>ba. read_state (getMEM a) =\<^sub>b return (mem a)) \<and>\<^sub>b
   (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
   (read_state BranchDelayPCC =\<^sub>b return None) \<and>\<^sub>b
   (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
   (read_state getBranchDelay =\<^sub>b return None)"

abbreviation "getExceptionOccurredPost exl pc pcc capr scapr mem \<equiv>
              ValuePart (ExceptionOccurredPost exl pc pcc capr scapr mem)"

lemma getExceptionOccurredPostE [elim!]:
  assumes "getExceptionOccurredPost exl pc pcc capr scapr mem s"
  shows "getCP0StatusEXL s"
    and "getBase (getPCC s) + getPC s \<in> ExceptionPCs"
    and "getPCC s = scapr 29"
    and "getCAPR cd s = capr cd"
    and "getMEM a s = mem a"
    and "BranchToPCC s = None"
    and "BranchDelayPCC s = None"
    and "getBranchTo s = None"
    and "getBranchDelay s = None"
using assms
unfolding ExceptionOccurredPost_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_getExceptionOccurredPost [Commute_compositeI]:
  assumes "Commute (read_state getCP0StatusEXL) m"
      and "Commute (read_state getPC) m"
      and "Commute (read_state getPCC) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMEM a)) m"
      and "Commute (read_state BranchToPCC) m"
      and "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state getBranchTo) m"
      and "Commute (read_state getBranchDelay) m"
  shows "Commute (read_state (getExceptionOccurredPost exl pc pcc capr scapr mem)) m"
unfolding ExceptionOccurredPost_def
by (Commute intro: assms)

named_theorems ExceptionCases

abbreviation (out) 
  "exceptionLemmaPre exl pc pcc capr scapr mem \<equiv> 
   \<not>\<^sub>b read_state getExceptionSignalled \<and>\<^sub>b
   read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)"

abbreviation (out) 
  "exceptionLemmaPost exl pc pcc capr scapr mem \<equiv> 
   \<not>\<^sub>b read_state getExceptionSignalled \<or>\<^sub>b
   read_state (getExceptionOccurredPost exl pc pcc capr scapr mem)"

lemma ExceptionCase_NoException:
  defines "q \<equiv> (bind (read_state getExceptionSignalled) (\<lambda>a. return (\<not> a)))"
  assumes "IsInvariant q m"
  shows "HoareTriple q m (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
using assms
unfolding HoareTriple_def 
by (simp add: ValueAndStatePart_simp)

lemmas ExceptionCase_NoException_loops =
  ExceptionCase_NoException[where m="foreach_loop _"]
  ExceptionCase_NoException[where m="foreach_loop_agg _ _ _"] 
  
method ExceptionCase =
  ParametricHoareTriple
      \<open>ComputePre \<open>rule ExceptionCase_NoException_loops; 
                      solves \<open>Invariant intro: ExceptionCases\<close> |
                   rule ExceptionCases[THEN HoareTriple_post_weakening];
                      solves \<open>auto split: all_split simp add: ValueAndStatePart_simp\<close>\<close>
                  \<open>rule HoareTriple_weakest_pre_read_state |
                   rule ExceptionCase_NoException; 
                      solves \<open>Invariant intro: ExceptionCases\<close>\<close>\<close>

(* Code generation - start - exception lemma *)

(* Code generation - override - next_unknown *)

lemma ExceptionCase_next_unknown [ExceptionCases]:
  shows "IsInvariant (exceptionLemmaPost exl pc pcc capr scapr mem) (next_unknown v)"
by Invariant

(* Code generation - end override *)

(* Code generation - override - SignalException *)

lemma SignalException_getExceptionOccurredHoareTriple:
  assumes "getExceptionOccurredPre exl pc pcc capr scapr mem s"
  shows "getExceptionOccurredPost exl pc pcc capr scapr mem (setSignalException ex s)"
using assms
unfolding ExceptionOccurredPre_def ExceptionOccurredPost_def
by (auto simp: ValueAndStatePart_simp SignalExceptionSCAPR_def)

lemma ExceptionCase_SignalException [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 (SignalException v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding HoareTriple_def
by (auto simp: ValueAndStatePart_simp
         elim: SignalException_getExceptionOccurredHoareTriple)

(* Code generation - end override *)

(* Code generation - override - SignalCP2UnusableException *)

lemma ExceptionCase_SignalCP2UnusableException [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 SignalCP2UnusableException
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalCP2UnusableException_alt_def
by (HoareTriple intro: ExceptionCase_SignalException)

(* Code generation - end override *)

(* Code generation - override - SignalCapException_internal *)

lemma ExceptionCase_SignalCapException_internal [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 (SignalCapException_internal v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalCapException_internal_alt_def
by (HoareTriple intro: ExceptionCase_SignalException)

(* Code generation - end override *)

(* Code generation - override - SignalCapException *)

lemma ExceptionCase_SignalCapException [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 (SignalCapException v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalCapException_alt_def
by (HoareTriple intro: ExceptionCase_SignalCapException_internal)

(* Code generation - end override *)

(* Code generation - override - SignalCapException_noReg *)

lemma ExceptionCase_SignalCapException_noReg [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 (SignalCapException_noReg v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalCapException_noReg_alt_def
by (HoareTriple intro: ExceptionCase_SignalCapException_internal)

(* Code generation - end override *)

lemma ExceptionCase_dfn'ERET [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'ERET
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ERET_alt_def
by ExceptionCase

(* Code generation - override - SignalTLBException *)

lemma ExceptionCase_SignalTLBException [ExceptionCases]:
  shows "HoareTriple (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem)) 
                 (SignalTLBException v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalTLBException_alt_def
by (HoareTriple intro: ExceptionCase_SignalException)

(* Code generation - end override *)

(* Code generation - override - AddressTranslation *)

lemma ExceptionCase_AddressTranslation [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (AddressTranslation v)
                 (\<lambda>_. bind (read_state getExceptionSignalled)
                      (\<lambda>a. bind (read_state (getExceptionOccurredPre exl pc pcc capr scapr mem))
                      (\<lambda>b. bind (read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))
                      (\<lambda>c. return (if a then c else b)))))"
unfolding AddressTranslation_alt_def
by ExceptionCase

(* Code generation - end override *)

(* Code generation - override - SignalTLBCapException *)

lemma ExceptionCase_SignalTLBCapException [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (SignalTLBCapException v)
                 (\<lambda>_. read_state getExceptionSignalled \<and>\<^sub>b
                      read_state (getExceptionOccurredPost exl pc pcc capr scapr mem))"
unfolding SignalTLBCapException_alt_def
by (HoareTriple intro: ExceptionCase_SignalCapException_noReg)

(* Code generation - end override *)

lemma ExceptionCase_LoadMemoryCap [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (LoadMemoryCap v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding LoadMemoryCap_alt_def
by ExceptionCase

lemma ExceptionCase_LoadMemory [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (LoadMemory v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding LoadMemory_alt_def
by ExceptionCase

lemma ExceptionCase_LoadCap [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (LoadCap v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding LoadCap_alt_def
by ExceptionCase

lemma ExceptionCase_StoreMemoryCap [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (StoreMemoryCap v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding StoreMemoryCap_alt_def
by ExceptionCase

lemma ExceptionCase_StoreMemory [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (StoreMemory v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding StoreMemory_alt_def
by ExceptionCase

lemma ExceptionCase_StoreCap [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (StoreCap v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding StoreCap_alt_def
by ExceptionCase

(* Code generation - skip - Fetch *)

lemma ExceptionCase_mtc [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (mtc v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding mtc_alt_def
by ExceptionCase

lemma ExceptionCase_dmtc [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dmtc v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dmtc_alt_def
by ExceptionCase

lemma ExceptionCase_mfc [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (mfc v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding mfc_alt_def
by ExceptionCase

lemma ExceptionCase_dmfc [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dmfc v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dmfc_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ADDI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ADDI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ADDI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ADDIU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ADDIU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ADDIU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DADDI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DADDI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DADDI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DADDIU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DADDIU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DADDIU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLTI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLTI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLTI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLTIU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLTIU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLTIU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ANDI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ANDI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ANDI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ORI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ORI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ORI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'XORI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'XORI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'XORI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LUI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LUI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LUI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ADD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ADD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ADD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ADDU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ADDU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ADDU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SUB [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SUB v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SUB_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SUBU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SUBU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SUBU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DADD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DADD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DADD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DADDU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DADDU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DADDU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSUB [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSUB v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSUB_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSUBU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSUBU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSUBU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLT [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLT v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLT_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'AND [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'AND v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'AND_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'OR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'OR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'OR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'XOR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'XOR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'XOR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'NOR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'NOR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'NOR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MOVN [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MOVN v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MOVN_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MOVZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MOVZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MOVZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MADD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MADD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MADD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MADDU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MADDU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MADDU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MSUB [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MSUB v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MSUB_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MSUBU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MSUBU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MSUBU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MUL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MUL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MUL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MULT [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MULT v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MULT_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MULTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MULTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MULTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DMULT [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DMULT v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DMULT_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DMULTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DMULTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DMULTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DIV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DIV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DIV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DIVU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DIVU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DIVU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DDIV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DDIV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DDIV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DDIVU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DDIVU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DDIVU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MFHI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MFHI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MFHI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MFLO [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MFLO v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MFLO_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MTHI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MTHI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MTHI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MTLO [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MTLO v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MTLO_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SRL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SRL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SRL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SRA [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SRA v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SRA_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SLLV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SLLV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SLLV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SRLV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SRLV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SRLV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SRAV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SRAV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SRAV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSLL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSLL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSLL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRA [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRA v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRA_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSLLV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSLLV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSLLV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRLV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRLV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRLV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRAV [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRAV v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRAV_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSLL32 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSLL32 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSLL32_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRL32 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRL32 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRL32_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DSRA32 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DSRA32 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DSRA32_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TGE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TGE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TGE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TGEU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TGEU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TGEU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLT [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TLT v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLT_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TLTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TEQ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TEQ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TEQ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TNE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TNE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TNE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TGEI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TGEI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TGEI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TGEIU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TGEIU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TGEIU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLTI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TLTI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLTI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLTIU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TLTIU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLTIU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TEQI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TEQI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TEQI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TNEI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'TNEI v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TNEI_alt_def
by ExceptionCase

lemma ExceptionCase_loadByte [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (loadByte v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding loadByte_alt_def
by ExceptionCase

lemma ExceptionCase_loadHalf [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (loadHalf v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding loadHalf_alt_def
by ExceptionCase

lemma ExceptionCase_loadWord [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (loadWord v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding loadWord_alt_def
by ExceptionCase

lemma ExceptionCase_loadDoubleword [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (loadDoubleword v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding loadDoubleword_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LB [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LB v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LB_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LBU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LBU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LBU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LH [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LH v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LH_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LHU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LHU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LHU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LW [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LW v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LW_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LWU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LWU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LWU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LLD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LLD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LLD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LWL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LWL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LWL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LWR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LWR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LWR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LDL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LDL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LDL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'LDR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'LDR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'LDR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SB [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SB v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SB_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SH [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SH v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SH_alt_def
by ExceptionCase

lemma ExceptionCase_storeWord [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (storeWord v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding storeWord_alt_def
by ExceptionCase

lemma ExceptionCase_storeDoubleword [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (storeDoubleword v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding storeDoubleword_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SW [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SW v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SW_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SCD [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SCD v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SCD_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SWL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SWL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SWL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SWR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SWR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SWR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SDL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SDL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SDL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SDR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'SDR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SDR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BREAK [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'BREAK
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BREAK_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'SYSCALL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'SYSCALL
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'SYSCALL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MTC0 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MTC0 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MTC0_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DMTC0 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DMTC0 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DMTC0_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'MFC0 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'MFC0 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'MFC0_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'DMFC0 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'DMFC0 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'DMFC0_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'J [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'J v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'J_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'JAL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'JAL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'JAL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'JALR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'JALR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'JALR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'JR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'JR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'JR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BEQ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BEQ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BEQ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BNE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BNE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BNE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLEZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLEZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLEZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGTZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGTZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGTZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLTZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLTZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLTZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGEZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGEZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGEZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLTZAL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLTZAL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLTZAL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGEZAL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGEZAL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGEZAL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BEQL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BEQL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BEQL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BNEL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BNEL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BNEL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLEZL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLEZL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLEZL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGTZL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGTZL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGTZL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLTZL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLTZL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLTZL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGEZL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGEZL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGEZL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BLTZALL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BLTZALL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BLTZALL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'BGEZALL [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'BGEZALL v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'BGEZALL_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'RDHWR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'RDHWR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'RDHWR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CACHE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CACHE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CACHE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ReservedInstruction [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'ReservedInstruction
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ReservedInstruction_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'Unpredictable [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'Unpredictable
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'Unpredictable_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLBP [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'TLBP
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLBP_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLBR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'TLBR
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLBR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLBWI [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'TLBWI
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLBWI_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'TLBWR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'TLBWR
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'TLBWR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'COP1 [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'COP1 v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'COP1_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetBase [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetBase v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetBase_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetOffset [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetOffset v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetOffset_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetLen [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetLen v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetLen_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetTag [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetTag v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetTag_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetSealed [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetSealed v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetSealed_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetPerm [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetPerm v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetPerm_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetType [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetType v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetType_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetAddr [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetAddr v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetAddr_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetPCC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetPCC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetPCC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetPCCSetOffset [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetPCCSetOffset v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetPCCSetOffset_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CGetCause [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CGetCause v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CGetCause_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSetCause [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSetCause v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSetCause_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CIncOffset [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CIncOffset v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CIncOffset_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CIncOffsetImmediate [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CIncOffsetImmediate v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CIncOffsetImmediate_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSetBounds [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSetBounds v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSetBounds_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSetBoundsExact [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSetBoundsExact v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSetBoundsExact_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSetBoundsImmediate [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSetBoundsImmediate v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSetBoundsImmediate_alt_def
by ExceptionCase

lemma ExceptionCase_ClearRegs [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (ClearRegs v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding ClearRegs_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ClearLo [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ClearLo v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ClearLo_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'ClearHi [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'ClearHi v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'ClearHi_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CClearLo [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CClearLo v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CClearLo_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CClearHi [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CClearHi v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CClearHi_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CClearTag [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CClearTag v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CClearTag_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CAndPerm [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CAndPerm v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CAndPerm_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSetOffset [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSetOffset v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSetOffset_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSub [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSub v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSub_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CCheckPerm [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CCheckPerm v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CCheckPerm_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CCheckType [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CCheckType v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CCheckType_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CFromPtr [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CFromPtr v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CFromPtr_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CToPtr [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CToPtr v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CToPtr_alt_def
by ExceptionCase

lemma ExceptionCase_CPtrCmp [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (CPtrCmp v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding CPtrCmp_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CEQ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CEQ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CEQ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CNE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CNE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CNE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLT [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLT v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLT_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLE [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLE v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLE_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLEU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLEU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLEU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CEXEQ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CEXEQ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CEXEQ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CNEXEQ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CNEXEQ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CNEXEQ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CBTU [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CBTU v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CBTU_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CBTS [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CBTS v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CBTS_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CBEZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CBEZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CBEZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CBNZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CBNZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CBNZ_alt_def
by ExceptionCase

(* Code generation - prefix - dfn'CSC *)

lemma ExceptionCase_setLLbit [ExceptionCases]:
  shows "IsInvariant (exceptionLemmaPost exl pc pcc capr scapr mem)
                   (update_state (setLLbit None))"
by Invariant

(* Code generation - end prefix *)

lemma ExceptionCase_dfn'CSC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLoad [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLoad v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLoad_alt_def
by ExceptionCase

lemma ExceptionCase_store [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (store v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding store_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CStore [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CStore v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CStore_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLLC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLLC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLLC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CLLx [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CLLx v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CLLx_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSCC [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSCC v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSCC_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSCx [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSCx v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSCx_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CMOVN [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CMOVN v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CMOVN_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CMOVZ [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CMOVZ v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CMOVZ_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CMove [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CMove v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CMove_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CTestSubset [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CTestSubset v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CTestSubset_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CBuildCap [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CBuildCap v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CBuildCap_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CCopyType [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CCopyType v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CCopyType_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CJR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CJR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CJR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CJALR [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CJALR v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CJALR_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CSeal [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CSeal v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CSeal_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CUnseal [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CUnseal v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CUnseal_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CCall [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CCall v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CCall_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CCallFast [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CCallFast v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CCallFast_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CReadHwr [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CReadHwr v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CReadHwr_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CWriteHwr [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (dfn'CWriteHwr v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CWriteHwr_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'CReturn [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'CReturn
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'CReturn_alt_def
by ExceptionCase

lemma ExceptionCase_dfn'UnknownCapInstruction [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 dfn'UnknownCapInstruction
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding dfn'UnknownCapInstruction_alt_def
by ExceptionCase

lemma ExceptionCase_Run [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 (Run v)
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding Run_alt_def
by ExceptionCase

(* Code generation - override - Next *)

lemma ExceptionCase_TakeBranch [ExceptionCases]:
  shows "IsInvariant (exceptionLemmaPost exl pc pcc capr scapr mem) TakeBranch"
unfolding TakeBranch_def 
by ExceptionCase (auto split: option.splits dest: getExceptionOccurredPostE)

lemma ExceptionCase_Fetch [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem) 
                 Fetch
                 (\<lambda>v. case v of None \<Rightarrow> read_state getExceptionSignalled \<and>\<^sub>b
                                        read_state (getExceptionOccurredPost exl pc pcc capr scapr mem)
                              | Some y \<Rightarrow> \<not>\<^sub>b read_state getExceptionSignalled \<and>\<^sub>b 
                                          read_state (getExceptionOccurredPre exl pc pcc capr scapr mem))"
unfolding Fetch_alt_def
by ExceptionCase

lemma ExceptionCase_NextWithGhostState [ExceptionCases]:
  shows "HoareTriple (exceptionLemmaPre exl pc pcc capr scapr mem)
                 NextWithGhostState
                 (\<lambda>_. exceptionLemmaPost exl pc pcc capr scapr mem)"
unfolding NextWithGhostState_def
by (HoareTriple intro: ExceptionCases[THEN HoareTriple_post_weakening])

lemma ExceptionCase_Next:
  assumes "\<not> getExceptionSignalled s"
      and "getExceptionSignalled (StatePart NextWithGhostState s)"
  shows "getExceptionOccurredPost (getCP0StatusEXL s) 
                                  (getPC s)
                                  (getPCC s)
                                  (\<lambda>cd. getCAPR cd s)
                                  (\<lambda>cd. getSCAPR cd s)
                                  (\<lambda>a. getMEM a s)
                                  (StatePart Next s)"
proof -
  have "getExceptionOccurredPost exl pc pcc capr scapr mem (StatePart Next s)"
  if "getExceptionOccurredPost exl pc pcc capr scapr mem (StatePart NextWithGhostState s)" 
  for exl pc pcc capr scapr mem
    using that
    unfolding Next_NextWithGhostState
    unfolding ExceptionOccurredPost_def
    by (auto simp: ValueAndStatePart_simp)
  thus ?thesis
    using assms
    using HoareTripleE[OF ExceptionCase_NextWithGhostState, where s=s]
    by (auto simp: ValueAndStatePart_simp)
qed

(* Code generation - end override *)

(* Code generation - end *)

theorem SemanticsException:
  assumes valid: "getStateIsValid s"
      and suc: "(SwitchDomain RaiseException, s') \<in> SemanticsCheriMips s"
  shows "getCP0StatusEXL s'"
    and "getBase (getPCC s') + getPC s' \<in> ExceptionPCs"
    and "getPCC s' = getKCC s"
    and "getCAPR cd s' = getCAPR cd s"
    and "getSCAPR cd' s' = SignalExceptionSCAPR cd' s"
    and "getMEM a s' = getMEM a s"
    and "BranchToPCC s' = None"
    and "BranchDelayPCC s' = None"
    and "getBranchTo s' = None"
    and "getBranchDelay s' = None"
using valid 
using ExceptionCase_Next[where s=s]
using SemanticsCheriMips_Exception[OF suc]
unfolding StateIsValid_def GhostStateIsValid_def
unfolding SignalExceptionSCAPR_def
unfolding ExceptionOccurredPre_def ExceptionOccurredPost_def
by (auto simp: ValueAndStatePart_simp)

corollary SemanticsException_extra:
  assumes valid: "getStateIsValid s"
      and suc: "(SwitchDomain RaiseException, s') \<in> SemanticsCheriMips s"
  shows "getMemCap a s' = getMemCap a s"
    and "getMemByte a' s' = getMemByte a' s"
    and "getBranchToPccCap s' = nullCap"
    and "getBranchDelayPccCap s' = nullCap"
using SemanticsException[OF assms]
using getMemCap_getMEM[where s=s and s'=s' and a=a]
using getMemByte_getMEM[where s=s and s'=s' and a=a']
unfolding getBranchToPccCap_def
unfolding getBranchDelayPccCap_def
by auto

corollary ExceptionInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "ExceptionProp s lbl s'"
unfolding ExceptionProp_def
using assms SemanticsException
by auto 

(*<*)
end
(*>*)