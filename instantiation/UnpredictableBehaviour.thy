(*<*) 

(* Author: Kyndylan Nienhuis *)

theory UnpredictableBehaviour

imports 
  "CHERI-core.CheriLemmas"
begin

(*>*)
section \<open>Undefined states\<close>

named_theorems UndefinedCasesI

method UndefinedCases = 
  Invariant intro: UndefinedCasesI

(* Code generation - start - undefinedness lemma *)

(* Code generation - override - raise'exception *)

lemma UndefinedCase_raise'exception:
  shows "PrePost (return True)
                 (raise'exception (UNPREDICTABLE v))
                 (\<lambda>_. read_state isUnpredictable)"
by PrePost

lemma UndefinedCase_raise'exception_IsInvariant [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (raise'exception (UNPREDICTABLE v))"
by PrePost

(* Code generation - end override *)

lemma UndefinedCase_CheckBranch [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) CheckBranch"
unfolding CheckBranch_alt_def 
by UndefinedCases

lemma UndefinedCase_BranchNotTaken [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) BranchNotTaken"
unfolding BranchNotTaken_alt_def 
by UndefinedCases

lemma UndefinedCase_BranchLikelyNotTaken [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) BranchLikelyNotTaken"
unfolding BranchLikelyNotTaken_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ERET [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'ERET"
unfolding dfn'ERET_alt_def 
by UndefinedCases

lemma UndefinedCase_check_cca [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (check_cca v)"
unfolding check_cca_alt_def 
by UndefinedCases

lemma UndefinedCase_AddressTranslation [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (AddressTranslation v)"
unfolding AddressTranslation_alt_def 
by UndefinedCases

lemma UndefinedCase_AdjustEndian [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (AdjustEndian v)"
unfolding AdjustEndian_alt_def 
by UndefinedCases

lemma UndefinedCase_LoadMemoryCap [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (LoadMemoryCap v)"
unfolding LoadMemoryCap_alt_def 
by UndefinedCases

lemma UndefinedCase_LoadMemory [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (LoadMemory v)"
unfolding LoadMemory_alt_def 
by UndefinedCases

lemma UndefinedCase_LoadCap [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (LoadCap v)"
unfolding LoadCap_alt_def 
by UndefinedCases

lemma UndefinedCase_StoreMemoryCap [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (StoreMemoryCap v)"
unfolding StoreMemoryCap_alt_def 
by UndefinedCases

lemma UndefinedCase_StoreMemory [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (StoreMemory v)"
unfolding StoreMemory_alt_def 
by UndefinedCases

lemma UndefinedCase_StoreCap [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (StoreCap v)"
unfolding StoreCap_alt_def 
by UndefinedCases

lemma UndefinedCase_Fetch [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) Fetch"
unfolding Fetch_alt_def 
by UndefinedCases

lemma UndefinedCase_write'CP0R [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (write'CP0R v)"
unfolding write'CP0R_alt_def 
by UndefinedCases

lemma UndefinedCase_mtc [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (mtc v)"
unfolding mtc_alt_def 
by UndefinedCases

lemma UndefinedCase_dmtc [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dmtc v)"
unfolding dmtc_alt_def 
by UndefinedCases

lemma UndefinedCase_mfc [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (mfc v)"
unfolding mfc_alt_def 
by UndefinedCases

lemma UndefinedCase_dmfc [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dmfc v)"
unfolding dmfc_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ADDI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ADDI v)"
unfolding dfn'ADDI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ADDIU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ADDIU v)"
unfolding dfn'ADDIU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DADDI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DADDI v)"
unfolding dfn'DADDI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DADDIU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DADDIU v)"
unfolding dfn'DADDIU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLTI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLTI v)"
unfolding dfn'SLTI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLTIU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLTIU v)"
unfolding dfn'SLTIU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ANDI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ANDI v)"
unfolding dfn'ANDI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ORI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ORI v)"
unfolding dfn'ORI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'XORI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'XORI v)"
unfolding dfn'XORI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LUI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LUI v)"
unfolding dfn'LUI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ADD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ADD v)"
unfolding dfn'ADD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ADDU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ADDU v)"
unfolding dfn'ADDU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SUB [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SUB v)"
unfolding dfn'SUB_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SUBU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SUBU v)"
unfolding dfn'SUBU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DADD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DADD v)"
unfolding dfn'DADD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DADDU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DADDU v)"
unfolding dfn'DADDU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSUB [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSUB v)"
unfolding dfn'DSUB_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSUBU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSUBU v)"
unfolding dfn'DSUBU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLT [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLT v)"
unfolding dfn'SLT_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLTU v)"
unfolding dfn'SLTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'AND [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'AND v)"
unfolding dfn'AND_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'OR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'OR v)"
unfolding dfn'OR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'XOR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'XOR v)"
unfolding dfn'XOR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'NOR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'NOR v)"
unfolding dfn'NOR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MOVN [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MOVN v)"
unfolding dfn'MOVN_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MOVZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MOVZ v)"
unfolding dfn'MOVZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MADD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MADD v)"
unfolding dfn'MADD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MADDU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MADDU v)"
unfolding dfn'MADDU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MSUB [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MSUB v)"
unfolding dfn'MSUB_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MSUBU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MSUBU v)"
unfolding dfn'MSUBU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MUL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MUL v)"
unfolding dfn'MUL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MULT [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MULT v)"
unfolding dfn'MULT_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MULTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MULTU v)"
unfolding dfn'MULTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DMULT [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DMULT v)"
unfolding dfn'DMULT_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DMULTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DMULTU v)"
unfolding dfn'DMULTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DIV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DIV v)"
unfolding dfn'DIV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DIVU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DIVU v)"
unfolding dfn'DIVU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DDIV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DDIV v)"
unfolding dfn'DDIV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DDIVU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DDIVU v)"
unfolding dfn'DDIVU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MFHI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MFHI v)"
unfolding dfn'MFHI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MFLO [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MFLO v)"
unfolding dfn'MFLO_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MTHI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MTHI v)"
unfolding dfn'MTHI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MTLO [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MTLO v)"
unfolding dfn'MTLO_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLL v)"
unfolding dfn'SLL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SRL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SRL v)"
unfolding dfn'SRL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SRA [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SRA v)"
unfolding dfn'SRA_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SLLV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SLLV v)"
unfolding dfn'SLLV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SRLV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SRLV v)"
unfolding dfn'SRLV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SRAV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SRAV v)"
unfolding dfn'SRAV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSLL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSLL v)"
unfolding dfn'DSLL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRL v)"
unfolding dfn'DSRL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRA [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRA v)"
unfolding dfn'DSRA_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSLLV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSLLV v)"
unfolding dfn'DSLLV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRLV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRLV v)"
unfolding dfn'DSRLV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRAV [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRAV v)"
unfolding dfn'DSRAV_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSLL32 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSLL32 v)"
unfolding dfn'DSLL32_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRL32 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRL32 v)"
unfolding dfn'DSRL32_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DSRA32 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DSRA32 v)"
unfolding dfn'DSRA32_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TGE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TGE v)"
unfolding dfn'TGE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TGEU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TGEU v)"
unfolding dfn'TGEU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLT [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TLT v)"
unfolding dfn'TLT_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TLTU v)"
unfolding dfn'TLTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TEQ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TEQ v)"
unfolding dfn'TEQ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TNE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TNE v)"
unfolding dfn'TNE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TGEI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TGEI v)"
unfolding dfn'TGEI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TGEIU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TGEIU v)"
unfolding dfn'TGEIU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLTI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TLTI v)"
unfolding dfn'TLTI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLTIU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TLTIU v)"
unfolding dfn'TLTIU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TEQI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TEQI v)"
unfolding dfn'TEQI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TNEI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'TNEI v)"
unfolding dfn'TNEI_alt_def 
by UndefinedCases

lemma UndefinedCase_loadByte [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (loadByte v)"
unfolding loadByte_alt_def 
by UndefinedCases

lemma UndefinedCase_loadHalf [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (loadHalf v)"
unfolding loadHalf_alt_def 
by UndefinedCases

lemma UndefinedCase_loadWord [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (loadWord v)"
unfolding loadWord_alt_def 
by UndefinedCases

lemma UndefinedCase_loadDoubleword [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (loadDoubleword v)"
unfolding loadDoubleword_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LB [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LB v)"
unfolding dfn'LB_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LBU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LBU v)"
unfolding dfn'LBU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LH [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LH v)"
unfolding dfn'LH_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LHU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LHU v)"
unfolding dfn'LHU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LW [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LW v)"
unfolding dfn'LW_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LWU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LWU v)"
unfolding dfn'LWU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LL v)"
unfolding dfn'LL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LD v)"
unfolding dfn'LD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LLD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LLD v)"
unfolding dfn'LLD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LWL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LWL v)"
unfolding dfn'LWL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LWR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LWR v)"
unfolding dfn'LWR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LDL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LDL v)"
unfolding dfn'LDL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'LDR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'LDR v)"
unfolding dfn'LDR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SB [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SB v)"
unfolding dfn'SB_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SH [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SH v)"
unfolding dfn'SH_alt_def 
by UndefinedCases

lemma UndefinedCase_storeWord [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (storeWord v)"
unfolding storeWord_alt_def 
by UndefinedCases

lemma UndefinedCase_storeDoubleword [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (storeDoubleword v)"
unfolding storeDoubleword_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SW [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SW v)"
unfolding dfn'SW_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SD v)"
unfolding dfn'SD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SC v)"
unfolding dfn'SC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SCD [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SCD v)"
unfolding dfn'SCD_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SWL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SWL v)"
unfolding dfn'SWL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SWR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SWR v)"
unfolding dfn'SWR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SDL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SDL v)"
unfolding dfn'SDL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SDR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'SDR v)"
unfolding dfn'SDR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BREAK [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'BREAK"
unfolding dfn'BREAK_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'SYSCALL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'SYSCALL"
unfolding dfn'SYSCALL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MTC0 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MTC0 v)"
unfolding dfn'MTC0_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DMTC0 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DMTC0 v)"
unfolding dfn'DMTC0_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'MFC0 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'MFC0 v)"
unfolding dfn'MFC0_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'DMFC0 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'DMFC0 v)"
unfolding dfn'DMFC0_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'J [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'J v)"
unfolding dfn'J_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'JAL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'JAL v)"
unfolding dfn'JAL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'JALR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'JALR v)"
unfolding dfn'JALR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'JR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'JR v)"
unfolding dfn'JR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BEQ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BEQ v)"
unfolding dfn'BEQ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BNE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BNE v)"
unfolding dfn'BNE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLEZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLEZ v)"
unfolding dfn'BLEZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGTZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGTZ v)"
unfolding dfn'BGTZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLTZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLTZ v)"
unfolding dfn'BLTZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGEZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGEZ v)"
unfolding dfn'BGEZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLTZAL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLTZAL v)"
unfolding dfn'BLTZAL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGEZAL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGEZAL v)"
unfolding dfn'BGEZAL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BEQL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BEQL v)"
unfolding dfn'BEQL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BNEL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BNEL v)"
unfolding dfn'BNEL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLEZL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLEZL v)"
unfolding dfn'BLEZL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGTZL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGTZL v)"
unfolding dfn'BGTZL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLTZL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLTZL v)"
unfolding dfn'BLTZL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGEZL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGEZL v)"
unfolding dfn'BGEZL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BLTZALL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BLTZALL v)"
unfolding dfn'BLTZALL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'BGEZALL [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'BGEZALL v)"
unfolding dfn'BGEZALL_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'RDHWR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'RDHWR v)"
unfolding dfn'RDHWR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CACHE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CACHE v)"
unfolding dfn'CACHE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ReservedInstruction [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'ReservedInstruction"
unfolding dfn'ReservedInstruction_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'Unpredictable [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'Unpredictable"
unfolding dfn'Unpredictable_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLBP [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'TLBP"
unfolding dfn'TLBP_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLBR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'TLBR"
unfolding dfn'TLBR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLBWI [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'TLBWI"
unfolding dfn'TLBWI_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'TLBWR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'TLBWR"
unfolding dfn'TLBWR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'COP1 [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'COP1 v)"
unfolding dfn'COP1_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetBase [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetBase v)"
unfolding dfn'CGetBase_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetOffset [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetOffset v)"
unfolding dfn'CGetOffset_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetLen [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetLen v)"
unfolding dfn'CGetLen_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetTag [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetTag v)"
unfolding dfn'CGetTag_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetSealed [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetSealed v)"
unfolding dfn'CGetSealed_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetPerm [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetPerm v)"
unfolding dfn'CGetPerm_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetType [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetType v)"
unfolding dfn'CGetType_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetAddr [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetAddr v)"
unfolding dfn'CGetAddr_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetPCC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetPCC v)"
unfolding dfn'CGetPCC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetPCCSetOffset [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetPCCSetOffset v)"
unfolding dfn'CGetPCCSetOffset_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CGetCause [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CGetCause v)"
unfolding dfn'CGetCause_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSetCause [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSetCause v)"
unfolding dfn'CSetCause_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CIncOffset [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CIncOffset v)"
unfolding dfn'CIncOffset_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CIncOffsetImmediate [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CIncOffsetImmediate v)"
unfolding dfn'CIncOffsetImmediate_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSetBounds [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSetBounds v)"
unfolding dfn'CSetBounds_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSetBoundsExact [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSetBoundsExact v)"
unfolding dfn'CSetBoundsExact_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSetBoundsImmediate [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSetBoundsImmediate v)"
unfolding dfn'CSetBoundsImmediate_alt_def 
by UndefinedCases

lemma UndefinedCase_ClearRegs [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (ClearRegs v)"
unfolding ClearRegs_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ClearLo [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ClearLo v)"
unfolding dfn'ClearLo_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'ClearHi [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'ClearHi v)"
unfolding dfn'ClearHi_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CClearLo [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CClearLo v)"
unfolding dfn'CClearLo_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CClearHi [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CClearHi v)"
unfolding dfn'CClearHi_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CClearTag [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CClearTag v)"
unfolding dfn'CClearTag_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CAndPerm [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CAndPerm v)"
unfolding dfn'CAndPerm_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSetOffset [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSetOffset v)"
unfolding dfn'CSetOffset_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSub [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSub v)"
unfolding dfn'CSub_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CCheckPerm [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CCheckPerm v)"
unfolding dfn'CCheckPerm_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CCheckType [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CCheckType v)"
unfolding dfn'CCheckType_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CFromPtr [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CFromPtr v)"
unfolding dfn'CFromPtr_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CToPtr [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CToPtr v)"
unfolding dfn'CToPtr_alt_def 
by UndefinedCases

lemma UndefinedCase_CPtrCmp [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (CPtrCmp v)"
unfolding CPtrCmp_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CEQ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CEQ v)"
unfolding dfn'CEQ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CNE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CNE v)"
unfolding dfn'CNE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLT [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLT v)"
unfolding dfn'CLT_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLE [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLE v)"
unfolding dfn'CLE_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLTU v)"
unfolding dfn'CLTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLEU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLEU v)"
unfolding dfn'CLEU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CEXEQ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CEXEQ v)"
unfolding dfn'CEXEQ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CNEXEQ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CNEXEQ v)"
unfolding dfn'CNEXEQ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CBTU [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CBTU v)"
unfolding dfn'CBTU_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CBTS [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CBTS v)"
unfolding dfn'CBTS_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CBEZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CBEZ v)"
unfolding dfn'CBEZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CBNZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CBNZ v)"
unfolding dfn'CBNZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSC v)"
unfolding dfn'CSC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLC v)"
unfolding dfn'CLC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLoad [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLoad v)"
unfolding dfn'CLoad_alt_def 
by UndefinedCases

lemma UndefinedCase_store [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (store v)"
unfolding store_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CStore [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CStore v)"
unfolding dfn'CStore_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLLC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLLC v)"
unfolding dfn'CLLC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CLLx [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CLLx v)"
unfolding dfn'CLLx_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSCC [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSCC v)"
unfolding dfn'CSCC_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSCx [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSCx v)"
unfolding dfn'CSCx_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CMOVN [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CMOVN v)"
unfolding dfn'CMOVN_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CMOVZ [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CMOVZ v)"
unfolding dfn'CMOVZ_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CMove [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CMove v)"
unfolding dfn'CMove_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CTestSubset [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CTestSubset v)"
unfolding dfn'CTestSubset_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CBuildCap [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CBuildCap v)"
unfolding dfn'CBuildCap_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CCopyType [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CCopyType v)"
unfolding dfn'CCopyType_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CJR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CJR v)"
unfolding dfn'CJR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CJALR [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CJALR v)"
unfolding dfn'CJALR_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CSeal [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CSeal v)"
unfolding dfn'CSeal_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CUnseal [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CUnseal v)"
unfolding dfn'CUnseal_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CCall [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CCall v)"
unfolding dfn'CCall_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CCallFast [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CCallFast v)"
unfolding dfn'CCallFast_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CReadHwr [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CReadHwr v)"
unfolding dfn'CReadHwr_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CWriteHwr [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (dfn'CWriteHwr v)"
unfolding dfn'CWriteHwr_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'CReturn [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'CReturn"
unfolding dfn'CReturn_alt_def 
by UndefinedCases

lemma UndefinedCase_dfn'UnknownCapInstruction [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) dfn'UnknownCapInstruction"
unfolding dfn'UnknownCapInstruction_alt_def 
by UndefinedCases

lemma UndefinedCase_Run [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) (Run v)"
unfolding Run_alt_def 
by UndefinedCases

(* Code generation - prefix - Next *)

lemma UndefinedCase_TakeBranch [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) TakeBranch"
unfolding TakeBranch_def 
by UndefinedCases

(* Code generation - end prefix *)

lemma UndefinedCase_Next [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) Next"
unfolding Next_alt_def 
by UndefinedCases

(* Code generation - end *)

lemma UndefinedCase_NextWithGhostState [UndefinedCasesI]:
  shows "IsInvariant (read_state isUnpredictable) NextWithGhostState"
unfolding NextWithGhostState_def 
by UndefinedCases

end