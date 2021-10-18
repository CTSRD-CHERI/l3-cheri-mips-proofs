(*<*) 

(* Author: Kyndylan Nienhuis *)

theory AddressTranslation

imports 
  "ExceptionFlag"
  "ExecutionStep"
  "UnpredictableBehaviour"
begin

(*>*)
section \<open>Invariance of address translation\<close>

definition TranslateAddrFuncEquals :: 
  "(VirtualAddress \<times> AccessType \<Rightarrow> PhysicalAddress option) \<Rightarrow> state \<Rightarrow> bool" where
  "TranslateAddrFuncEquals X \<equiv> (\<lambda>s. \<forall>a. getTranslateAddr a s = X a)"

lemma Commute_getTranslateAddrFunc [Commute_compositeI]:
  assumes "\<And>a. Commute (read_state (getTranslateAddr a)) m"
  shows "Commute (read_state (TranslateAddrFuncEquals X)) m"
using assms
unfolding TranslateAddrFuncEquals_def Commute_def
by auto

abbreviation (out) 
  "AddressTranslationPre X \<equiv> 
   read_state (TranslateAddrFuncEquals X)"

abbreviation (out) 
  "AddressTranslationPost X \<equiv> 
   read_state getExceptionSignalled \<or>\<^sub>b
   read_state isUnpredictable \<or>\<^sub>b
   read_state (TranslateAddrFuncEquals X)"

named_theorems MapVirtualAddressInvariantI

declare nonExceptionCase_exceptions [MapVirtualAddressInvariantI]
  
method MapVirtualAddressInvariant =
  HoareTriple intro: MapVirtualAddressInvariantI[THEN HoareTriple_post_weakening]

(* Code generation - start - address translation invariant *)

(* Code generation - override - raise'exception *)

(* lemma AddressTranslationInvariant_raise'exception [MapVirtualAddressInvariantI]:
  shows "HoareTriple (return True) 
                 (raise'exception (UNPREDICTABLE x)) 
                 (\<lambda>_. bind (read_state exception)
                           (\<lambda>a. return (a \<noteq> NoException)))"
unfolding raise'exception_alt_def 
by MapVirtualAddressInvariant *)

(* Code generation - end override *)

(* Code generation - override - CheckBranch *)

lemma AddressTranslationInvariant_CheckBranch [MapVirtualAddressInvariantI]:
  shows "IsInvariant (AddressTranslationPost X) CheckBranch"
unfolding CheckBranch_alt_def 
by MapVirtualAddressInvariant

(* Code generation - end override *)

lemma AddressTranslationInvariant_BranchNotTaken [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) BranchNotTaken (\<lambda>_. AddressTranslationPost X)" 
unfolding BranchNotTaken_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_BranchLikelyNotTaken [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) BranchLikelyNotTaken (\<lambda>_. AddressTranslationPost X)" 
unfolding BranchLikelyNotTaken_alt_def
by MapVirtualAddressInvariant

(* Code generation - skip - SignalException *)

(* Code generation - skip - SignalCP2UnusableException *)

(* Code generation - skip - SignalCapException_internal *)

(* Code generation - skip - SignalCapException *)

(* Code generation - skip - SignalCapException_noReg *)

(* Code generation - override - dfn'ERET *)

lemma AddressTranslationInvariant_dfn'ERET [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 dfn'ERET
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable)"
unfolding dfn'ERET_alt_def CheckBranch_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

(* Code generation - skip - write'TLB_direct *)

(* Code generation - skip - write'TLB_assoc *)

(* Code generation - skip - SignalTLBException_internal *)

(* Code generation - skip - SignalTLBException *)

(* Code generation - override - check_cca *)

lemma AddressTranslationInvariant_check_cca [MapVirtualAddressInvariantI]:
  shows "IsInvariant (AddressTranslationPost X) (check_cca v)"
unfolding check_cca_alt_def 
by MapVirtualAddressInvariant

(* Code generation - end override *)

lemma AddressTranslationInvariant_AddressTranslation [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (AddressTranslation v) (\<lambda>_. AddressTranslationPost X)" 
unfolding AddressTranslation_alt_def
by MapVirtualAddressInvariant

(* Code generation - skip - SignalTLBCapException *)

(* Code generation - override - AdjustEndian *)

lemma AddressTranslationInvariant_AdjustEndian [MapVirtualAddressInvariantI]:
  shows "IsInvariant (AddressTranslationPost X) (AdjustEndian v)"
unfolding AdjustEndian_alt_def 
by MapVirtualAddressInvariant

(* Code generation - end override *)

lemma AddressTranslationInvariant_LoadMemoryCap [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (LoadMemoryCap v) (\<lambda>_. AddressTranslationPost X)" 
unfolding LoadMemoryCap_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_LoadMemory [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (LoadMemory v) (\<lambda>_. AddressTranslationPost X)" 
unfolding LoadMemory_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_LoadCap [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (LoadCap v) (\<lambda>_. AddressTranslationPost X)" 
unfolding LoadCap_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_StoreMemoryCap [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (StoreMemoryCap v) (\<lambda>_. AddressTranslationPost X)" 
unfolding StoreMemoryCap_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_StoreMemory [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (StoreMemory v) (\<lambda>_. AddressTranslationPost X)" 
unfolding StoreMemory_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_StoreCap [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (StoreCap v) (\<lambda>_. AddressTranslationPost X)" 
unfolding StoreCap_alt_def
by MapVirtualAddressInvariant

(* Code generation - skip - Fetch *)

(* Code generation - skip - write'CP0R *)

(* Code generation - skip - mtc *)

(* Code generation - skip - dmtc *)

lemma AddressTranslationInvariant_mfc [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (mfc v) (\<lambda>_. AddressTranslationPost X)" 
unfolding mfc_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dmfc [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dmfc v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dmfc_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ADDI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ADDI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ADDI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ADDIU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ADDIU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ADDIU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DADDI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DADDI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DADDI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DADDIU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DADDIU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DADDIU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLTI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLTI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLTI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLTIU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLTIU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLTIU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ANDI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ANDI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ANDI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ORI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ORI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ORI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'XORI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'XORI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'XORI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LUI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LUI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LUI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ADD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ADD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ADD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ADDU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ADDU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ADDU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SUB [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SUB v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SUB_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SUBU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SUBU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SUBU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DADD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DADD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DADD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DADDU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DADDU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DADDU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSUB [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSUB v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSUB_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSUBU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSUBU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSUBU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLT [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLT v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLT_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'AND [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'AND v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'AND_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'OR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'OR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'OR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'XOR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'XOR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'XOR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'NOR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'NOR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'NOR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MOVN [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MOVN v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MOVN_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MOVZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MOVZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MOVZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MADD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MADD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MADD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MADDU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MADDU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MADDU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MSUB [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MSUB v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MSUB_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MSUBU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MSUBU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MSUBU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MUL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MUL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MUL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MULT [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MULT v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MULT_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MULTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MULTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MULTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DMULT [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DMULT v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DMULT_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DMULTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DMULTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DMULTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DIV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DIV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DIV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DIVU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DIVU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DIVU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DDIV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DDIV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DDIV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DDIVU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DDIVU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DDIVU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MFHI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MFHI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MFHI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MFLO [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MFLO v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MFLO_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MTHI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MTHI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MTHI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'MTLO [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MTLO v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MTLO_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SRL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SRL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SRL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SRA [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SRA v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SRA_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SLLV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SLLV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SLLV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SRLV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SRLV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SRLV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SRAV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SRAV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SRAV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSLL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSLL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSLL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRA [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRA v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRA_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSLLV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSLLV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSLLV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRLV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRLV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRLV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRAV [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRAV v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRAV_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSLL32 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSLL32 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSLL32_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRL32 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRL32 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRL32_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DSRA32 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DSRA32 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DSRA32_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TGE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TGE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TGE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TGEU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TGEU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TGEU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TLT [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TLT v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TLT_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TLTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TLTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TLTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TEQ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TEQ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TEQ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TNE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TNE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TNE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TGEI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TGEI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TGEI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TGEIU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TGEIU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TGEIU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TLTI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TLTI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TLTI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TLTIU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TLTIU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TLTIU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TEQI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TEQI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TEQI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TNEI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'TNEI v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TNEI_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_loadByte [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (loadByte v) (\<lambda>_. AddressTranslationPost X)" 
unfolding loadByte_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_loadHalf [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (loadHalf v) (\<lambda>_. AddressTranslationPost X)" 
unfolding loadHalf_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_loadWord [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (loadWord v) (\<lambda>_. AddressTranslationPost X)" 
unfolding loadWord_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_loadDoubleword [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (loadDoubleword v) (\<lambda>_. AddressTranslationPost X)" 
unfolding loadDoubleword_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LB [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LB v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LB_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LBU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LBU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LBU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LH [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LH v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LH_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LHU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LHU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LHU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LW [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LW v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LW_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LWU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LWU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LWU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LLD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LLD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LLD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LWL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LWL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LWL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LWR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LWR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LWR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LDL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LDL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LDL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'LDR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'LDR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'LDR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SB [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SB v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SB_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SH [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SH v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SH_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_storeWord [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (storeWord v) (\<lambda>_. AddressTranslationPost X)" 
unfolding storeWord_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_storeDoubleword [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (storeDoubleword v) (\<lambda>_. AddressTranslationPost X)" 
unfolding storeDoubleword_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SW [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SW v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SW_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SCD [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SCD v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SCD_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SWL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SWL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SWL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SWR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SWR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SWR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SDL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SDL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SDL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SDR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'SDR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SDR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BREAK [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'BREAK (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BREAK_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'SYSCALL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'SYSCALL (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'SYSCALL_alt_def
by MapVirtualAddressInvariant

(* Code generation - override - dfn'MTC0 *)

lemma AddressTranslationInvariant_dfn'MTC0 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 (dfn'MTC0 v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable)"
unfolding dfn'MTC0_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

(* Code generation - override - dfn'DMTC0 *)

lemma AddressTranslationInvariant_dfn'DMTC0 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 (dfn'DMTC0 v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable)"
unfolding dfn'DMTC0_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

lemma AddressTranslationInvariant_dfn'MFC0 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'MFC0 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'MFC0_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'DMFC0 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'DMFC0 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'DMFC0_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'J [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'J v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'J_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'JAL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'JAL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'JAL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'JALR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'JALR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'JALR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'JR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'JR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'JR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BEQ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BEQ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BEQ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BNE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BNE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BNE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLEZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLEZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLEZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGTZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGTZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGTZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLTZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLTZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLTZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGEZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGEZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGEZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLTZAL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLTZAL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLTZAL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGEZAL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGEZAL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGEZAL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BEQL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BEQL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BEQL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BNEL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BNEL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BNEL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLEZL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLEZL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLEZL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGTZL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGTZL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGTZL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLTZL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLTZL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLTZL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGEZL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGEZL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGEZL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BLTZALL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BLTZALL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BLTZALL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'BGEZALL [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'BGEZALL v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'BGEZALL_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'RDHWR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'RDHWR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'RDHWR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CACHE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CACHE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CACHE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ReservedInstruction [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'ReservedInstruction (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ReservedInstruction_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'Unpredictable [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'Unpredictable (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'Unpredictable_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'TLBP [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'TLBP (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'TLBP_alt_def
by MapVirtualAddressInvariant

(* Code generation - override - dfn'TLBR *)

lemma AddressTranslationInvariant_dfn'TLBR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 dfn'TLBR
                 (\<lambda>_. AddressTranslationPost X)"
unfolding dfn'TLBR_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

(* Code generation - override - dfn'TLBWI *)

lemma AddressTranslationInvariant_dfn'TLBWI [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 dfn'TLBWI
                 (\<lambda>_. AddressTranslationPost X)"
unfolding dfn'TLBWI_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

(* Code generation - override - dfn'TLBWR *)

lemma AddressTranslationInvariant_dfn'TLBWR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 dfn'TLBWR
                 (\<lambda>_. AddressTranslationPost X)"
unfolding dfn'TLBWR_alt_def
by MapVirtualAddressInvariant

(* Code generation - end override *)

lemma AddressTranslationInvariant_dfn'COP1 [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'COP1 v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'COP1_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetBase [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetBase v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetBase_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetOffset [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetOffset v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetOffset_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetLen [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetLen v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetLen_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetTag [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetTag v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetTag_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetSealed [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetSealed v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetSealed_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetPerm [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetPerm v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetPerm_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetType [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetType v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetType_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetAddr [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetAddr v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetAddr_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetPCC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetPCC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetPCC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetPCCSetOffset [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetPCCSetOffset v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetPCCSetOffset_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CGetCause [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CGetCause v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CGetCause_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSetCause [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSetCause v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSetCause_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CIncOffset [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CIncOffset v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CIncOffset_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CIncOffsetImmediate [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CIncOffsetImmediate v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CIncOffsetImmediate_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSetBounds [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSetBounds v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSetBounds_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSetBoundsExact [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSetBoundsExact v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSetBoundsExact_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSetBoundsImmediate [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSetBoundsImmediate v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSetBoundsImmediate_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_ClearRegs [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (ClearRegs v) (\<lambda>_. AddressTranslationPost X)" 
unfolding ClearRegs_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ClearLo [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ClearLo v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ClearLo_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'ClearHi [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'ClearHi v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'ClearHi_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CClearLo [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CClearLo v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CClearLo_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CClearHi [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CClearHi v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CClearHi_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CClearTag [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CClearTag v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CClearTag_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CAndPerm [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CAndPerm v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CAndPerm_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSetOffset [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSetOffset v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSetOffset_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSub [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSub v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSub_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CCheckPerm [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CCheckPerm v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CCheckPerm_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CCheckType [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CCheckType v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CCheckType_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CFromPtr [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CFromPtr v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CFromPtr_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CToPtr [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CToPtr v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CToPtr_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_CPtrCmp [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (CPtrCmp v) (\<lambda>_. AddressTranslationPost X)" 
unfolding CPtrCmp_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CEQ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CEQ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CEQ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CNE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CNE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CNE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLT [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLT v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLT_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLE [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLE v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLE_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLEU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLEU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLEU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CEXEQ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CEXEQ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CEXEQ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CNEXEQ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CNEXEQ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CNEXEQ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CBTU [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CBTU v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CBTU_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CBTS [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CBTS v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CBTS_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CBEZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CBEZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CBEZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CBNZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CBNZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CBNZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLoad [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLoad v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLoad_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_store [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (store v) (\<lambda>_. AddressTranslationPost X)" 
unfolding store_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CStore [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CStore v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CStore_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLLC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLLC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLLC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CLLx [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CLLx v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CLLx_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSCC [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSCC v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSCC_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSCx [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSCx v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSCx_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CMOVN [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CMOVN v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CMOVN_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CMOVZ [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CMOVZ v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CMOVZ_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CMove [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CMove v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CMove_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CTestSubset [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CTestSubset v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CTestSubset_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CBuildCap [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CBuildCap v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CBuildCap_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CCopyType [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CCopyType v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CCopyType_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CJR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CJR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CJR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CJALR [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CJALR v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CJALR_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CSeal [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CSeal v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CSeal_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CUnseal [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CUnseal v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CUnseal_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CCall [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CCall v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CCall_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CCallFast [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CCallFast v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CCallFast_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CReadHwr [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CReadHwr v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CReadHwr_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CWriteHwr [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) (dfn'CWriteHwr v) (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CWriteHwr_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'CReturn [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'CReturn (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'CReturn_alt_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_dfn'UnknownCapInstruction [MapVirtualAddressInvariantI]:
  shows "HoareTriple (AddressTranslationPre X) dfn'UnknownCapInstruction (\<lambda>_. AddressTranslationPost X)" 
unfolding dfn'UnknownCapInstruction_alt_def
by MapVirtualAddressInvariant

(* Code generation - override - Run *)

lemma AddressTranslationInvariant_Run_aux:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 (Run v)
                 (\<lambda>_. AddressTranslationPost X)"
unfolding Run_alt_def
by MapVirtualAddressInvariant auto?

lemmas AddressTranslationInvariant_Run [MapVirtualAddressInvariantI] =
  HoareTriple_weakest_pre_disj[OF AddressTranslationInvariant_Run_aux
                              UndefinedCase_Run]

(* Code generation - end override *)

(* Code generation - skip - Next *)

(* Code generation - end *)

lemma AddressTranslationInvariant_TakeBranch [MapVirtualAddressInvariantI]:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      read_state (TranslateAddrFuncEquals X))
                     TakeBranch"
unfolding TakeBranch_def
by HoareTriple

lemma AddressTranslationInvariant_Fetch [MapVirtualAddressInvariantI]:
  fixes X
  defines "p \<equiv> \<lambda>w. read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b 
                                bind (read_state getPCC)
                                     (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc)))"
  shows "HoareTriple (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro HoareTriple_Fetch) Commute+

lemma AddressTranslationInvariant_NextWithGhostState:
  shows "HoareTriple (read_state (TranslateAddrFuncEquals X) \<and>\<^sub>b
                  bind (read_state getPCC)
                       (\<lambda>pcc. return (\<not> Access_System_Registers (getPerms pcc))))
                 NextWithGhostState
                 (\<lambda>_. AddressTranslationPost X)"
unfolding NextWithGhostState_def
by MapVirtualAddressInvariant

lemma AddressTranslationInvariant_Unpredictable:
  assumes "\<not> getKernelMode s"
      and suc: "s' \<in> UnpredictableNext s"
  shows "getTranslateAddr a s' = getTranslateAddr a s"
using assms
by auto

theorem InvarianceAddressTranslation:
  assumes "\<not> Access_System_Registers (getPerms (getPCC s))"
      and valid: "getStateIsValid s"
      and suc: "(step, s') \<in> SemanticsCheriMips s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
  shows "getTranslateAddr a s' = getTranslateAddr a s"
using assms
using AddressTranslationInvariant_NextWithGhostState
        [where X="\<lambda>a. getTranslateAddr a s", THEN HoareTripleE[where s=s]]
using AddressTranslationInvariant_Unpredictable[where s=s and s'=s']
using SemanticsCheriMips_PredictableNonException[OF suc no_ex]
unfolding SemanticsCheriMips_def
unfolding TranslateAddrFuncEquals_def
by (cases a) (auto simp: ValueAndStatePart_simp split: if_splits)

corollary AddressTranslationInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "AddressTranslationProp s lbl s'"
unfolding AddressTranslationProp_def
using assms InvarianceAddressTranslation
by auto 

(*<*)
end
(*>*)