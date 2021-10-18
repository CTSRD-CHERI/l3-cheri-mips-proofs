(*<*) 

(* Author: Kyndylan Nienhuis *)

theory ValidState

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Invariance of @{const StateIsValid}\<close>

named_theorems ValidStateInvariantI

abbreviation (out) 
  "ValidStateInvariant \<equiv> 
   read_state getCP0ConfigBE \<and>\<^sub>b
   \<not>\<^sub>b read_state getCP0StatusRE"

(* Code generation - start - StateIsValid invariant *)

lemma ValidStateInvariant_raise'exception [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (raise'exception v)" 
unfolding raise'exception_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_PIC_update [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (PIC_update v)" 
unfolding PIC_update_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_PIC_initialise [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (PIC_initialise v)" 
unfolding PIC_initialise_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_PIC_load [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (PIC_load v)" 
unfolding PIC_load_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_PIC_store [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (PIC_store v)" 
unfolding PIC_store_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_update_interrupt_bit [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (JTAG_UART_update_interrupt_bit v)" 
unfolding JTAG_UART_update_interrupt_bit_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_load [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant JTAG_UART_load" 
unfolding JTAG_UART_load_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_input [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (JTAG_UART_input v)" 
unfolding JTAG_UART_input_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_store [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (JTAG_UART_store v)" 
unfolding JTAG_UART_store_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_output [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant JTAG_UART_output" 
unfolding JTAG_UART_output_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_JTAG_UART_initialise [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (JTAG_UART_initialise v)" 
unfolding JTAG_UART_initialise_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_gpr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (gpr v)" 
unfolding gpr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'gpr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'gpr v)" 
unfolding write'gpr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_GPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (GPR v)" 
unfolding GPR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'GPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'GPR v)" 
unfolding write'GPR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_UserMode [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant UserMode" 
unfolding UserMode_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SupervisorMode [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant SupervisorMode" 
unfolding SupervisorMode_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_KernelMode [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant KernelMode" 
unfolding KernelMode_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_BigEndianMem [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant BigEndianMem" 
unfolding BigEndianMem_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_ReverseEndian [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant ReverseEndian" 
unfolding ReverseEndian_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_BigEndianCPU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant BigEndianCPU" 
unfolding BigEndianCPU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CheckBranch [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant CheckBranch" 
unfolding CheckBranch_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_BranchNotTaken [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant BranchNotTaken" 
unfolding BranchNotTaken_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_BranchLikelyNotTaken [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant BranchLikelyNotTaken" 
unfolding BranchLikelyNotTaken_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_initCoreStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant initCoreStats" 
unfolding initCoreStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_printCoreStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant printCoreStats" 
unfolding printCoreStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_next_unknown [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (next_unknown v)" 
unfolding next_unknown_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_PCC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant PCC" 
unfolding PCC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'PCC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'PCC v)" 
unfolding write'PCC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CAPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (CAPR v)" 
unfolding CAPR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'CAPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'CAPR v)" 
unfolding write'CAPR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SCAPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SCAPR v)" 
unfolding SCAPR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'SCAPR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'SCAPR v)" 
unfolding write'SCAPR_alt_def
by (Invariant intro: ValidStateInvariantI)

(* Code generation - override - SignalException *)

lemma ValidStateInvariant_SignalException [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalException v)" 
by (Invariant intro: ValidStateInvariantI)

(* Code generation - end override *)

lemma ValidStateInvariant_SignalCP2UnusableException [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant SignalCP2UnusableException" 
unfolding SignalCP2UnusableException_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalCapException_internal [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalCapException_internal v)" 
unfolding SignalCapException_internal_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalCapException [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalCapException v)" 
unfolding SignalCapException_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalCapException_noReg [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalCapException_noReg v)" 
unfolding SignalCapException_noReg_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ERET [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'ERET" 
unfolding dfn'ERET_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_TLB_direct [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (TLB_direct v)" 
unfolding TLB_direct_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'TLB_direct [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'TLB_direct v)" 
unfolding write'TLB_direct_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_TLB_assoc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (TLB_assoc v)" 
unfolding TLB_assoc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'TLB_assoc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'TLB_assoc v)" 
unfolding write'TLB_assoc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_LookupTLB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (LookupTLB v)" 
unfolding LookupTLB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalTLBException_internal [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalTLBException_internal v)" 
unfolding SignalTLBException_internal_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalTLBException [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalTLBException v)" 
unfolding SignalTLBException_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CheckSegment [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (CheckSegment v)" 
unfolding CheckSegment_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_check_cca [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (check_cca v)" 
unfolding check_cca_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_TLB_next_random [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (TLB_next_random v)" 
unfolding TLB_next_random_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_AddressTranslation [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (AddressTranslation v)" 
unfolding AddressTranslation_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CP0TLBEntry [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (CP0TLBEntry v)" 
unfolding CP0TLBEntry_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_SignalTLBCapException [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (SignalTLBCapException v)" 
unfolding SignalTLBCapException_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_printMemStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant printMemStats" 
unfolding printMemStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_initMemStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant initMemStats" 
unfolding initMemStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_data_reads_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_data_reads_updt v)" 
unfolding stats_data_reads_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_data_writes_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_data_writes_updt v)" 
unfolding stats_data_writes_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_inst_reads_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_inst_reads_updt v)" 
unfolding stats_inst_reads_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_valid_cap_reads_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_valid_cap_reads_updt v)" 
unfolding stats_valid_cap_reads_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_valid_cap_writes_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_valid_cap_writes_updt v)" 
unfolding stats_valid_cap_writes_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_invalid_cap_reads_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_invalid_cap_reads_updt v)" 
unfolding stats_invalid_cap_reads_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_stats_invalid_cap_writes_updt [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (stats_invalid_cap_writes_updt v)" 
unfolding stats_invalid_cap_writes_updt_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_MEM [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (MEM v)" 
unfolding MEM_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'MEM [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'MEM v)" 
unfolding write'MEM_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_InitMEM [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant InitMEM" 
unfolding InitMEM_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_ReadData [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (ReadData v)" 
unfolding ReadData_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_WriteData [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (WriteData v)" 
unfolding WriteData_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_ReadInst [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (ReadInst v)" 
unfolding ReadInst_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_ReadCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (ReadCap v)" 
unfolding ReadCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_WriteCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (WriteCap v)" 
unfolding WriteCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_AdjustEndian [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (AdjustEndian v)" 
unfolding AdjustEndian_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_initMemAccessStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant initMemAccessStats" 
unfolding initMemAccessStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_printMemAccessStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant printMemAccessStats" 
unfolding printMemAccessStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_getVirtualAddress [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (getVirtualAddress v)" 
unfolding getVirtualAddress_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_LoadMemoryCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (LoadMemoryCap v)" 
unfolding LoadMemoryCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_LoadMemory [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (LoadMemory v)" 
unfolding LoadMemory_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_LoadCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (LoadCap v)" 
unfolding LoadCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_StoreMemoryCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (StoreMemoryCap v)" 
unfolding StoreMemoryCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_StoreMemory [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (StoreMemory v)" 
unfolding StoreMemory_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_StoreCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (StoreCap v)" 
unfolding StoreCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_Fetch [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant Fetch" 
unfolding Fetch_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CP0R [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (CP0R v)" 
unfolding CP0R_alt_def
by (Invariant intro: ValidStateInvariantI)

(* Code generation - override - write'CP0R *)

(* For some reason the simplifier gets stuck on the following term: *)

lemma "\<And>x1 x2 x1a x2a a s.
   v = (x1, x2) \<Longrightarrow>
   x2 = (x1a, x2a) \<Longrightarrow>
   \<not> (x1a = 0 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 2 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 3 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 4 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 4 \<and> x2a = 2) \<Longrightarrow>
   \<not> (x1a = 5 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 6 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 7 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 9 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 10 \<and> x2a = 0) \<Longrightarrow>
   \<not> (x1a = 11 \<and> x2a = 0) \<Longrightarrow> x1a = 12 \<and> x2a = 0 \<Longrightarrow> 
   setCP0Status (write'reg'StatusRegister (a, ucast x1)) (setCP0StatusRE False s) = 
   setCP0StatusRE False (setCP0Status (write'reg'StatusRegister (a, ucast x1)) s)"
oops

(* With the following proof we avoid the problem. *)

lemma ValidStateInvariant_write'CP0R [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'CP0R v)" 
unfolding write'CP0R_alt_def
by (rule HoareTriple_pre_strengthening,
    ComputePreDefault,
    strong_cong_simp add: ValueAndStatePart_simp)

(* Code generation - end override *)

lemma ValidStateInvariant_resetStats [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant resetStats" 
unfolding resetStats_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_HI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant HI" 
unfolding HI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'HI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'HI v)" 
unfolding write'HI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_LO [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant LO" 
unfolding LO_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_write'LO [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (write'LO v)" 
unfolding write'LO_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_mtc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (mtc v)" 
unfolding mtc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dmtc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dmtc v)" 
unfolding dmtc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_mfc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (mfc v)" 
unfolding mfc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dmfc [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dmfc v)" 
unfolding dmfc_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ADDI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ADDI v)" 
unfolding dfn'ADDI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ADDIU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ADDIU v)" 
unfolding dfn'ADDIU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DADDI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DADDI v)" 
unfolding dfn'DADDI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DADDIU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DADDIU v)" 
unfolding dfn'DADDIU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLTI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLTI v)" 
unfolding dfn'SLTI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLTIU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLTIU v)" 
unfolding dfn'SLTIU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ANDI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ANDI v)" 
unfolding dfn'ANDI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ORI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ORI v)" 
unfolding dfn'ORI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'XORI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'XORI v)" 
unfolding dfn'XORI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LUI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LUI v)" 
unfolding dfn'LUI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ADD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ADD v)" 
unfolding dfn'ADD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ADDU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ADDU v)" 
unfolding dfn'ADDU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SUB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SUB v)" 
unfolding dfn'SUB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SUBU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SUBU v)" 
unfolding dfn'SUBU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DADD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DADD v)" 
unfolding dfn'DADD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DADDU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DADDU v)" 
unfolding dfn'DADDU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSUB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSUB v)" 
unfolding dfn'DSUB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSUBU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSUBU v)" 
unfolding dfn'DSUBU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLT [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLT v)" 
unfolding dfn'SLT_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLTU v)" 
unfolding dfn'SLTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'AND [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'AND v)" 
unfolding dfn'AND_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'OR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'OR v)" 
unfolding dfn'OR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'XOR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'XOR v)" 
unfolding dfn'XOR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'NOR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'NOR v)" 
unfolding dfn'NOR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MOVN [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MOVN v)" 
unfolding dfn'MOVN_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MOVZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MOVZ v)" 
unfolding dfn'MOVZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MADD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MADD v)" 
unfolding dfn'MADD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MADDU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MADDU v)" 
unfolding dfn'MADDU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MSUB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MSUB v)" 
unfolding dfn'MSUB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MSUBU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MSUBU v)" 
unfolding dfn'MSUBU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MUL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MUL v)" 
unfolding dfn'MUL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MULT [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MULT v)" 
unfolding dfn'MULT_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MULTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MULTU v)" 
unfolding dfn'MULTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DMULT [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DMULT v)" 
unfolding dfn'DMULT_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DMULTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DMULTU v)" 
unfolding dfn'DMULTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DIV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DIV v)" 
unfolding dfn'DIV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DIVU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DIVU v)" 
unfolding dfn'DIVU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DDIV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DDIV v)" 
unfolding dfn'DDIV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DDIVU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DDIVU v)" 
unfolding dfn'DDIVU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MFHI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MFHI v)" 
unfolding dfn'MFHI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MFLO [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MFLO v)" 
unfolding dfn'MFLO_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MTHI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MTHI v)" 
unfolding dfn'MTHI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MTLO [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MTLO v)" 
unfolding dfn'MTLO_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLL v)" 
unfolding dfn'SLL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SRL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SRL v)" 
unfolding dfn'SRL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SRA [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SRA v)" 
unfolding dfn'SRA_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SLLV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SLLV v)" 
unfolding dfn'SLLV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SRLV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SRLV v)" 
unfolding dfn'SRLV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SRAV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SRAV v)" 
unfolding dfn'SRAV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSLL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSLL v)" 
unfolding dfn'DSLL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRL v)" 
unfolding dfn'DSRL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRA [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRA v)" 
unfolding dfn'DSRA_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSLLV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSLLV v)" 
unfolding dfn'DSLLV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRLV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRLV v)" 
unfolding dfn'DSRLV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRAV [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRAV v)" 
unfolding dfn'DSRAV_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSLL32 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSLL32 v)" 
unfolding dfn'DSLL32_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRL32 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRL32 v)" 
unfolding dfn'DSRL32_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DSRA32 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DSRA32 v)" 
unfolding dfn'DSRA32_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TGE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TGE v)" 
unfolding dfn'TGE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TGEU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TGEU v)" 
unfolding dfn'TGEU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLT [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TLT v)" 
unfolding dfn'TLT_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TLTU v)" 
unfolding dfn'TLTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TEQ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TEQ v)" 
unfolding dfn'TEQ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TNE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TNE v)" 
unfolding dfn'TNE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TGEI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TGEI v)" 
unfolding dfn'TGEI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TGEIU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TGEIU v)" 
unfolding dfn'TGEIU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLTI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TLTI v)" 
unfolding dfn'TLTI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLTIU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TLTIU v)" 
unfolding dfn'TLTIU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TEQI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TEQI v)" 
unfolding dfn'TEQI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TNEI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'TNEI v)" 
unfolding dfn'TNEI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_loadByte [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (loadByte v)" 
unfolding loadByte_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_loadHalf [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (loadHalf v)" 
unfolding loadHalf_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_loadWord [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (loadWord v)" 
unfolding loadWord_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_loadDoubleword [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (loadDoubleword v)" 
unfolding loadDoubleword_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LB v)" 
unfolding dfn'LB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LBU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LBU v)" 
unfolding dfn'LBU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LH [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LH v)" 
unfolding dfn'LH_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LHU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LHU v)" 
unfolding dfn'LHU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LW [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LW v)" 
unfolding dfn'LW_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LWU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LWU v)" 
unfolding dfn'LWU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LL v)" 
unfolding dfn'LL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LD v)" 
unfolding dfn'LD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LLD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LLD v)" 
unfolding dfn'LLD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LWL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LWL v)" 
unfolding dfn'LWL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LWR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LWR v)" 
unfolding dfn'LWR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LDL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LDL v)" 
unfolding dfn'LDL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'LDR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'LDR v)" 
unfolding dfn'LDR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SB [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SB v)" 
unfolding dfn'SB_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SH [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SH v)" 
unfolding dfn'SH_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_storeWord [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (storeWord v)" 
unfolding storeWord_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_storeDoubleword [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (storeDoubleword v)" 
unfolding storeDoubleword_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SW [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SW v)" 
unfolding dfn'SW_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SD v)" 
unfolding dfn'SD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SC v)" 
unfolding dfn'SC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SCD [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SCD v)" 
unfolding dfn'SCD_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SWL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SWL v)" 
unfolding dfn'SWL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SWR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SWR v)" 
unfolding dfn'SWR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SDL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SDL v)" 
unfolding dfn'SDL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SDR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'SDR v)" 
unfolding dfn'SDR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BREAK [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'BREAK" 
unfolding dfn'BREAK_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'SYSCALL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'SYSCALL" 
unfolding dfn'SYSCALL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MTC0 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MTC0 v)" 
unfolding dfn'MTC0_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DMTC0 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DMTC0 v)" 
unfolding dfn'DMTC0_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'MFC0 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'MFC0 v)" 
unfolding dfn'MFC0_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'DMFC0 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'DMFC0 v)" 
unfolding dfn'DMFC0_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'J [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'J v)" 
unfolding dfn'J_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'JAL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'JAL v)" 
unfolding dfn'JAL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'JALR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'JALR v)" 
unfolding dfn'JALR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'JR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'JR v)" 
unfolding dfn'JR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BEQ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BEQ v)" 
unfolding dfn'BEQ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BNE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BNE v)" 
unfolding dfn'BNE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLEZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLEZ v)" 
unfolding dfn'BLEZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGTZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGTZ v)" 
unfolding dfn'BGTZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLTZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLTZ v)" 
unfolding dfn'BLTZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGEZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGEZ v)" 
unfolding dfn'BGEZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLTZAL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLTZAL v)" 
unfolding dfn'BLTZAL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGEZAL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGEZAL v)" 
unfolding dfn'BGEZAL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BEQL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BEQL v)" 
unfolding dfn'BEQL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BNEL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BNEL v)" 
unfolding dfn'BNEL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLEZL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLEZL v)" 
unfolding dfn'BLEZL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGTZL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGTZL v)" 
unfolding dfn'BGTZL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLTZL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLTZL v)" 
unfolding dfn'BLTZL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGEZL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGEZL v)" 
unfolding dfn'BGEZL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BLTZALL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BLTZALL v)" 
unfolding dfn'BLTZALL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'BGEZALL [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'BGEZALL v)" 
unfolding dfn'BGEZALL_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'RDHWR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'RDHWR v)" 
unfolding dfn'RDHWR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CACHE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CACHE v)" 
unfolding dfn'CACHE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ReservedInstruction [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'ReservedInstruction" 
unfolding dfn'ReservedInstruction_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'Unpredictable [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'Unpredictable" 
unfolding dfn'Unpredictable_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLBP [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'TLBP" 
unfolding dfn'TLBP_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLBR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'TLBR" 
unfolding dfn'TLBR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLBWI [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'TLBWI" 
unfolding dfn'TLBWI_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'TLBWR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'TLBWR" 
unfolding dfn'TLBWR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'COP1 [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'COP1 v)" 
unfolding dfn'COP1_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetBase [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetBase v)" 
unfolding dfn'CGetBase_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetOffset [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetOffset v)" 
unfolding dfn'CGetOffset_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetLen [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetLen v)" 
unfolding dfn'CGetLen_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetTag [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetTag v)" 
unfolding dfn'CGetTag_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetSealed [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetSealed v)" 
unfolding dfn'CGetSealed_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetPerm [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetPerm v)" 
unfolding dfn'CGetPerm_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetType [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetType v)" 
unfolding dfn'CGetType_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetAddr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetAddr v)" 
unfolding dfn'CGetAddr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetPCC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetPCC v)" 
unfolding dfn'CGetPCC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetPCCSetOffset [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetPCCSetOffset v)" 
unfolding dfn'CGetPCCSetOffset_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CGetCause [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CGetCause v)" 
unfolding dfn'CGetCause_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSetCause [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSetCause v)" 
unfolding dfn'CSetCause_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CIncOffset [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CIncOffset v)" 
unfolding dfn'CIncOffset_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CIncOffsetImmediate [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CIncOffsetImmediate v)" 
unfolding dfn'CIncOffsetImmediate_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSetBounds [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSetBounds v)" 
unfolding dfn'CSetBounds_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSetBoundsExact [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSetBoundsExact v)" 
unfolding dfn'CSetBoundsExact_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSetBoundsImmediate [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSetBoundsImmediate v)" 
unfolding dfn'CSetBoundsImmediate_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_ClearRegs [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (ClearRegs v)" 
unfolding ClearRegs_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ClearLo [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ClearLo v)" 
unfolding dfn'ClearLo_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'ClearHi [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'ClearHi v)" 
unfolding dfn'ClearHi_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CClearLo [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CClearLo v)" 
unfolding dfn'CClearLo_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CClearHi [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CClearHi v)" 
unfolding dfn'CClearHi_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CClearTag [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CClearTag v)" 
unfolding dfn'CClearTag_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CAndPerm [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CAndPerm v)" 
unfolding dfn'CAndPerm_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSetOffset [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSetOffset v)" 
unfolding dfn'CSetOffset_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSub [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSub v)" 
unfolding dfn'CSub_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CCheckPerm [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CCheckPerm v)" 
unfolding dfn'CCheckPerm_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CCheckType [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CCheckType v)" 
unfolding dfn'CCheckType_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CFromPtr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CFromPtr v)" 
unfolding dfn'CFromPtr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CToPtr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CToPtr v)" 
unfolding dfn'CToPtr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_CPtrCmp [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (CPtrCmp v)" 
unfolding CPtrCmp_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CEQ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CEQ v)" 
unfolding dfn'CEQ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CNE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CNE v)" 
unfolding dfn'CNE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLT [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLT v)" 
unfolding dfn'CLT_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLE [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLE v)" 
unfolding dfn'CLE_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLTU v)" 
unfolding dfn'CLTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLEU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLEU v)" 
unfolding dfn'CLEU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CEXEQ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CEXEQ v)" 
unfolding dfn'CEXEQ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CNEXEQ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CNEXEQ v)" 
unfolding dfn'CNEXEQ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CBTU [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CBTU v)" 
unfolding dfn'CBTU_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CBTS [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CBTS v)" 
unfolding dfn'CBTS_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CBEZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CBEZ v)" 
unfolding dfn'CBEZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CBNZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CBNZ v)" 
unfolding dfn'CBNZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSC v)" 
unfolding dfn'CSC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLC v)" 
unfolding dfn'CLC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLoad [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLoad v)" 
unfolding dfn'CLoad_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_store [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (store v)" 
unfolding store_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CStore [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CStore v)" 
unfolding dfn'CStore_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLLC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLLC v)" 
unfolding dfn'CLLC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CLLx [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CLLx v)" 
unfolding dfn'CLLx_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSCC [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSCC v)" 
unfolding dfn'CSCC_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSCx [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSCx v)" 
unfolding dfn'CSCx_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CMOVN [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CMOVN v)" 
unfolding dfn'CMOVN_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CMOVZ [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CMOVZ v)" 
unfolding dfn'CMOVZ_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CMove [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CMove v)" 
unfolding dfn'CMove_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CTestSubset [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CTestSubset v)" 
unfolding dfn'CTestSubset_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CBuildCap [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CBuildCap v)" 
unfolding dfn'CBuildCap_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CCopyType [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CCopyType v)" 
unfolding dfn'CCopyType_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CJR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CJR v)" 
unfolding dfn'CJR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CJALR [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CJALR v)" 
unfolding dfn'CJALR_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CSeal [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CSeal v)" 
unfolding dfn'CSeal_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CUnseal [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CUnseal v)" 
unfolding dfn'CUnseal_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CCall [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CCall v)" 
unfolding dfn'CCall_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CCallFast [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CCallFast v)" 
unfolding dfn'CCallFast_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_special_register_accessible [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (special_register_accessible v)" 
unfolding special_register_accessible_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CReadHwr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CReadHwr v)" 
unfolding dfn'CReadHwr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CWriteHwr [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (dfn'CWriteHwr v)" 
unfolding dfn'CWriteHwr_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'CReturn [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'CReturn" 
unfolding dfn'CReturn_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_dfn'UnknownCapInstruction [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant dfn'UnknownCapInstruction" 
unfolding dfn'UnknownCapInstruction_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_log_instruction [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (log_instruction v)" 
unfolding log_instruction_alt_def
by (Invariant intro: ValidStateInvariantI)

lemma ValidStateInvariant_Run [ValidStateInvariantI]:
  shows "IsInvariant ValidStateInvariant (Run v)" 
unfolding Run_alt_def
by (Invariant intro: ValidStateInvariantI)

(* Code generation - skip - Next *)

(* Code generation - end *)

lemma ValidStateInvariant_TakeBranch [ValidStateInvariantI]:
  shows "HoareTriple (read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE)
                 TakeBranch
                 (\<lambda>_. read_state isUnpredictable \<or>\<^sub>b
                      (read_state getCP0ConfigBE \<and>\<^sub>b
                       \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                       (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                       ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                        (read_state BranchDelayPCC =\<^sub>b return None))))"
unfolding TakeBranch_def
by HoareTriple auto?

lemma ValidStateInvariant_NextWithGhostState:
  shows "HoareTriple (read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE)
                 NextWithGhostState
                 (\<lambda>_. read_state isUnpredictable \<or>\<^sub>b
                      (read_state getCP0ConfigBE \<and>\<^sub>b
                       \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                       (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                       ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                        (read_state BranchDelayPCC =\<^sub>b return None))))"
unfolding NextWithGhostState_def
by (HoareTriple intro: ValidStateInvariantI[THEN HoareTriple_post_weakening])

lemma ValidStateInvariant_Unpredictable:
  assumes "getStateIsValid s"
      and "s' \<in> UnpredictableNext s"
  shows "getStateIsValid s'"
using assms
by auto

theorem InvarianceValidState:
  assumes "getStateIsValid s"
      and suc: "(step, s') \<in> NextStates s"
  shows "getStateIsValid s'"
using assms
using ValidStateInvariant_NextWithGhostState[THEN HoareTripleE[where s=s]]
using ValidStateInvariant_Unpredictable[where s=s and s'=s']
unfolding NextStates_def Next_NextWithGhostState
unfolding StateIsValid_def GhostStateIsValid_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

corollary ValidStateInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "ValidStateProp s lbl s'"
unfolding ValidStateProp_def
using assms InvarianceValidState
by auto 

(*<*)
end
(*>*)