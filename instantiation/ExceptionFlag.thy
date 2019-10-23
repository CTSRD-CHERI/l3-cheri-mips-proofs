(*<*) 

(* Author: Kyndylan Nienhuis *)

theory ExceptionFlag

imports 
  "CHERI-core.CheriLemmas"
begin

(*>*)
section \<open>Invariance of @{const getExceptionSignalled}\<close>

named_theorems ExceptionSignalledI

lemma ExceptionSignalled_to_PrePost:
  fixes m :: "state \<Rightarrow> 'a \<times> state"
  assumes "\<And>s. getExceptionSignalled (StatePart m s) = True"
  shows "PrePost (return True) m (\<lambda>_. read_state getExceptionSignalled)"
using assms
by - PrePost

lemmas nonExceptionCase_exceptions = 
  ExceptionSignalled_to_PrePost[OF setSignalException_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalCP2UnusableException_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalCapException_internal_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalCapException_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalCapException_noReg_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalTLBException_getExceptionSignalled]
  ExceptionSignalled_to_PrePost[OF setSignalTLBCapException_getExceptionSignalled]

(* Code generation - start - ExceptionSignalled invariant *)

lemma ExceptionSignalled_raise'exception [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (raise'exception v)"
unfolding raise'exception_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_PIC_update [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (PIC_update v)"
unfolding PIC_update_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_PIC_initialise [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (PIC_initialise v)"
unfolding PIC_initialise_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_PIC_load [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (PIC_load v)"
unfolding PIC_load_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_PIC_store [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (PIC_store v)"
unfolding PIC_store_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_update_interrupt_bit [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (JTAG_UART_update_interrupt_bit v)"
unfolding JTAG_UART_update_interrupt_bit_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_load [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) JTAG_UART_load"
unfolding JTAG_UART_load_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_input [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (JTAG_UART_input v)"
unfolding JTAG_UART_input_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_store [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (JTAG_UART_store v)"
unfolding JTAG_UART_store_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_output [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) JTAG_UART_output"
unfolding JTAG_UART_output_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_JTAG_UART_initialise [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (JTAG_UART_initialise v)"
unfolding JTAG_UART_initialise_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_gpr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (gpr v)"
unfolding gpr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'gpr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'gpr v)"
unfolding write'gpr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_GPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (GPR v)"
unfolding GPR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'GPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'GPR v)"
unfolding write'GPR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_UserMode [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) UserMode"
unfolding UserMode_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SupervisorMode [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) SupervisorMode"
unfolding SupervisorMode_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_KernelMode [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) KernelMode"
unfolding KernelMode_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_BigEndianMem [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) BigEndianMem"
unfolding BigEndianMem_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_ReverseEndian [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) ReverseEndian"
unfolding ReverseEndian_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_BigEndianCPU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) BigEndianCPU"
unfolding BigEndianCPU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CheckBranch [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) CheckBranch"
unfolding CheckBranch_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_BranchNotTaken [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) BranchNotTaken"
unfolding BranchNotTaken_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_BranchLikelyNotTaken [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) BranchLikelyNotTaken"
unfolding BranchLikelyNotTaken_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_initCoreStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) initCoreStats"
unfolding initCoreStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_printCoreStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) printCoreStats"
unfolding printCoreStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_next_unknown [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (next_unknown v)"
unfolding next_unknown_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_PCC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) PCC"
unfolding PCC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'PCC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'PCC v)"
unfolding write'PCC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CAPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (CAPR v)"
unfolding CAPR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'CAPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'CAPR v)"
unfolding write'CAPR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SCAPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SCAPR v)"
unfolding SCAPR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'SCAPR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'SCAPR v)"
unfolding write'SCAPR_alt_def
by (Invariant intro: ExceptionSignalledI)

(* Code generation - override - SignalException *)

lemma ExceptionSignalled_SignalException [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalException v)"
unfolding SignalException_alt_def
by (PrePost intro: ExceptionSignalledI)

(* Code generation - end override *)

lemma ExceptionSignalled_SignalCP2UnusableException [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) SignalCP2UnusableException"
unfolding SignalCP2UnusableException_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalCapException_internal [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalCapException_internal v)"
unfolding SignalCapException_internal_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalCapException [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalCapException v)"
unfolding SignalCapException_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalCapException_noReg [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalCapException_noReg v)"
unfolding SignalCapException_noReg_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ERET [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'ERET"
unfolding dfn'ERET_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_TLB_direct [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (TLB_direct v)"
unfolding TLB_direct_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'TLB_direct [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'TLB_direct v)"
unfolding write'TLB_direct_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_TLB_assoc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (TLB_assoc v)"
unfolding TLB_assoc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'TLB_assoc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'TLB_assoc v)"
unfolding write'TLB_assoc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_LookupTLB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (LookupTLB v)"
unfolding LookupTLB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalTLBException_internal [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalTLBException_internal v)"
unfolding SignalTLBException_internal_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalTLBException [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalTLBException v)"
unfolding SignalTLBException_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CheckSegment [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (CheckSegment v)"
unfolding CheckSegment_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_check_cca [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (check_cca v)"
unfolding check_cca_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_TLB_next_random [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (TLB_next_random v)"
unfolding TLB_next_random_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_AddressTranslation [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (AddressTranslation v)"
unfolding AddressTranslation_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CP0TLBEntry [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (CP0TLBEntry v)"
unfolding CP0TLBEntry_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_SignalTLBCapException [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (SignalTLBCapException v)"
unfolding SignalTLBCapException_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_printMemStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) printMemStats"
unfolding printMemStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_initMemStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) initMemStats"
unfolding initMemStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_data_reads_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_data_reads_updt v)"
unfolding stats_data_reads_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_data_writes_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_data_writes_updt v)"
unfolding stats_data_writes_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_inst_reads_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_inst_reads_updt v)"
unfolding stats_inst_reads_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_valid_cap_reads_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_valid_cap_reads_updt v)"
unfolding stats_valid_cap_reads_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_valid_cap_writes_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_valid_cap_writes_updt v)"
unfolding stats_valid_cap_writes_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_invalid_cap_reads_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_invalid_cap_reads_updt v)"
unfolding stats_invalid_cap_reads_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_stats_invalid_cap_writes_updt [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (stats_invalid_cap_writes_updt v)"
unfolding stats_invalid_cap_writes_updt_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_MEM [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (MEM v)"
unfolding MEM_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'MEM [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'MEM v)"
unfolding write'MEM_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_InitMEM [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) InitMEM"
unfolding InitMEM_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_ReadData [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (ReadData v)"
unfolding ReadData_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_WriteData [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (WriteData v)"
unfolding WriteData_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_ReadInst [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (ReadInst v)"
unfolding ReadInst_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_ReadCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (ReadCap v)"
unfolding ReadCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_WriteCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (WriteCap v)"
unfolding WriteCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_AdjustEndian [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (AdjustEndian v)"
unfolding AdjustEndian_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_initMemAccessStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) initMemAccessStats"
unfolding initMemAccessStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_printMemAccessStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) printMemAccessStats"
unfolding printMemAccessStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_getVirtualAddress [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (getVirtualAddress v)"
unfolding getVirtualAddress_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_LoadMemoryCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (LoadMemoryCap v)"
unfolding LoadMemoryCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_LoadMemory [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (LoadMemory v)"
unfolding LoadMemory_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_LoadCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (LoadCap v)"
unfolding LoadCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_StoreMemoryCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (StoreMemoryCap v)"
unfolding StoreMemoryCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_StoreMemory [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (StoreMemory v)"
unfolding StoreMemory_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_StoreCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (StoreCap v)"
unfolding StoreCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_Fetch [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) Fetch"
unfolding Fetch_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CP0R [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (CP0R v)"
unfolding CP0R_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'CP0R [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'CP0R v)"
unfolding write'CP0R_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_resetStats [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) resetStats"
unfolding resetStats_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_HI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) HI"
unfolding HI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'HI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'HI v)"
unfolding write'HI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_LO [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) LO"
unfolding LO_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_write'LO [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (write'LO v)"
unfolding write'LO_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_mtc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (mtc v)"
unfolding mtc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dmtc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dmtc v)"
unfolding dmtc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_mfc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (mfc v)"
unfolding mfc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dmfc [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dmfc v)"
unfolding dmfc_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ADDI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ADDI v)"
unfolding dfn'ADDI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ADDIU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ADDIU v)"
unfolding dfn'ADDIU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DADDI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DADDI v)"
unfolding dfn'DADDI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DADDIU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DADDIU v)"
unfolding dfn'DADDIU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLTI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLTI v)"
unfolding dfn'SLTI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLTIU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLTIU v)"
unfolding dfn'SLTIU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ANDI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ANDI v)"
unfolding dfn'ANDI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ORI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ORI v)"
unfolding dfn'ORI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'XORI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'XORI v)"
unfolding dfn'XORI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LUI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LUI v)"
unfolding dfn'LUI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ADD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ADD v)"
unfolding dfn'ADD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ADDU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ADDU v)"
unfolding dfn'ADDU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SUB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SUB v)"
unfolding dfn'SUB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SUBU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SUBU v)"
unfolding dfn'SUBU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DADD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DADD v)"
unfolding dfn'DADD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DADDU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DADDU v)"
unfolding dfn'DADDU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSUB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSUB v)"
unfolding dfn'DSUB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSUBU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSUBU v)"
unfolding dfn'DSUBU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLT [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLT v)"
unfolding dfn'SLT_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLTU v)"
unfolding dfn'SLTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'AND [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'AND v)"
unfolding dfn'AND_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'OR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'OR v)"
unfolding dfn'OR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'XOR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'XOR v)"
unfolding dfn'XOR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'NOR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'NOR v)"
unfolding dfn'NOR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MOVN [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MOVN v)"
unfolding dfn'MOVN_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MOVZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MOVZ v)"
unfolding dfn'MOVZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MADD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MADD v)"
unfolding dfn'MADD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MADDU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MADDU v)"
unfolding dfn'MADDU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MSUB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MSUB v)"
unfolding dfn'MSUB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MSUBU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MSUBU v)"
unfolding dfn'MSUBU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MUL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MUL v)"
unfolding dfn'MUL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MULT [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MULT v)"
unfolding dfn'MULT_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MULTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MULTU v)"
unfolding dfn'MULTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DMULT [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DMULT v)"
unfolding dfn'DMULT_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DMULTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DMULTU v)"
unfolding dfn'DMULTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DIV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DIV v)"
unfolding dfn'DIV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DIVU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DIVU v)"
unfolding dfn'DIVU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DDIV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DDIV v)"
unfolding dfn'DDIV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DDIVU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DDIVU v)"
unfolding dfn'DDIVU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MFHI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MFHI v)"
unfolding dfn'MFHI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MFLO [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MFLO v)"
unfolding dfn'MFLO_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MTHI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MTHI v)"
unfolding dfn'MTHI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MTLO [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MTLO v)"
unfolding dfn'MTLO_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLL v)"
unfolding dfn'SLL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SRL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SRL v)"
unfolding dfn'SRL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SRA [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SRA v)"
unfolding dfn'SRA_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SLLV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SLLV v)"
unfolding dfn'SLLV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SRLV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SRLV v)"
unfolding dfn'SRLV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SRAV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SRAV v)"
unfolding dfn'SRAV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSLL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSLL v)"
unfolding dfn'DSLL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRL v)"
unfolding dfn'DSRL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRA [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRA v)"
unfolding dfn'DSRA_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSLLV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSLLV v)"
unfolding dfn'DSLLV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRLV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRLV v)"
unfolding dfn'DSRLV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRAV [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRAV v)"
unfolding dfn'DSRAV_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSLL32 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSLL32 v)"
unfolding dfn'DSLL32_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRL32 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRL32 v)"
unfolding dfn'DSRL32_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DSRA32 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DSRA32 v)"
unfolding dfn'DSRA32_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TGE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TGE v)"
unfolding dfn'TGE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TGEU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TGEU v)"
unfolding dfn'TGEU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLT [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TLT v)"
unfolding dfn'TLT_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TLTU v)"
unfolding dfn'TLTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TEQ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TEQ v)"
unfolding dfn'TEQ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TNE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TNE v)"
unfolding dfn'TNE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TGEI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TGEI v)"
unfolding dfn'TGEI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TGEIU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TGEIU v)"
unfolding dfn'TGEIU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLTI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TLTI v)"
unfolding dfn'TLTI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLTIU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TLTIU v)"
unfolding dfn'TLTIU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TEQI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TEQI v)"
unfolding dfn'TEQI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TNEI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'TNEI v)"
unfolding dfn'TNEI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_loadByte [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (loadByte v)"
unfolding loadByte_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_loadHalf [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (loadHalf v)"
unfolding loadHalf_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_loadWord [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (loadWord v)"
unfolding loadWord_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_loadDoubleword [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (loadDoubleword v)"
unfolding loadDoubleword_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LB v)"
unfolding dfn'LB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LBU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LBU v)"
unfolding dfn'LBU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LH [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LH v)"
unfolding dfn'LH_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LHU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LHU v)"
unfolding dfn'LHU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LW [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LW v)"
unfolding dfn'LW_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LWU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LWU v)"
unfolding dfn'LWU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LL v)"
unfolding dfn'LL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LD v)"
unfolding dfn'LD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LLD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LLD v)"
unfolding dfn'LLD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LWL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LWL v)"
unfolding dfn'LWL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LWR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LWR v)"
unfolding dfn'LWR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LDL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LDL v)"
unfolding dfn'LDL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'LDR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'LDR v)"
unfolding dfn'LDR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SB [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SB v)"
unfolding dfn'SB_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SH [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SH v)"
unfolding dfn'SH_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_storeWord [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (storeWord v)"
unfolding storeWord_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_storeDoubleword [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (storeDoubleword v)"
unfolding storeDoubleword_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SW [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SW v)"
unfolding dfn'SW_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SD v)"
unfolding dfn'SD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SC v)"
unfolding dfn'SC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SCD [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SCD v)"
unfolding dfn'SCD_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SWL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SWL v)"
unfolding dfn'SWL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SWR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SWR v)"
unfolding dfn'SWR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SDL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SDL v)"
unfolding dfn'SDL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SDR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'SDR v)"
unfolding dfn'SDR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BREAK [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'BREAK"
unfolding dfn'BREAK_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'SYSCALL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'SYSCALL"
unfolding dfn'SYSCALL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MTC0 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MTC0 v)"
unfolding dfn'MTC0_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DMTC0 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DMTC0 v)"
unfolding dfn'DMTC0_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'MFC0 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'MFC0 v)"
unfolding dfn'MFC0_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'DMFC0 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'DMFC0 v)"
unfolding dfn'DMFC0_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'J [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'J v)"
unfolding dfn'J_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'JAL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'JAL v)"
unfolding dfn'JAL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'JALR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'JALR v)"
unfolding dfn'JALR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'JR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'JR v)"
unfolding dfn'JR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BEQ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BEQ v)"
unfolding dfn'BEQ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BNE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BNE v)"
unfolding dfn'BNE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLEZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLEZ v)"
unfolding dfn'BLEZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGTZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGTZ v)"
unfolding dfn'BGTZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLTZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLTZ v)"
unfolding dfn'BLTZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGEZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGEZ v)"
unfolding dfn'BGEZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLTZAL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLTZAL v)"
unfolding dfn'BLTZAL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGEZAL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGEZAL v)"
unfolding dfn'BGEZAL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BEQL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BEQL v)"
unfolding dfn'BEQL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BNEL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BNEL v)"
unfolding dfn'BNEL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLEZL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLEZL v)"
unfolding dfn'BLEZL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGTZL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGTZL v)"
unfolding dfn'BGTZL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLTZL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLTZL v)"
unfolding dfn'BLTZL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGEZL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGEZL v)"
unfolding dfn'BGEZL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BLTZALL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BLTZALL v)"
unfolding dfn'BLTZALL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'BGEZALL [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'BGEZALL v)"
unfolding dfn'BGEZALL_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'RDHWR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'RDHWR v)"
unfolding dfn'RDHWR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CACHE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CACHE v)"
unfolding dfn'CACHE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ReservedInstruction [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'ReservedInstruction"
unfolding dfn'ReservedInstruction_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'Unpredictable [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'Unpredictable"
unfolding dfn'Unpredictable_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLBP [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'TLBP"
unfolding dfn'TLBP_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLBR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'TLBR"
unfolding dfn'TLBR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLBWI [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'TLBWI"
unfolding dfn'TLBWI_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'TLBWR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'TLBWR"
unfolding dfn'TLBWR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'COP1 [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'COP1 v)"
unfolding dfn'COP1_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetBase [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetBase v)"
unfolding dfn'CGetBase_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetOffset [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetOffset v)"
unfolding dfn'CGetOffset_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetLen [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetLen v)"
unfolding dfn'CGetLen_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetTag [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetTag v)"
unfolding dfn'CGetTag_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetSealed [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetSealed v)"
unfolding dfn'CGetSealed_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetPerm [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetPerm v)"
unfolding dfn'CGetPerm_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetType [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetType v)"
unfolding dfn'CGetType_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetAddr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetAddr v)"
unfolding dfn'CGetAddr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetPCC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetPCC v)"
unfolding dfn'CGetPCC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetPCCSetOffset [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetPCCSetOffset v)"
unfolding dfn'CGetPCCSetOffset_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CGetCause [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CGetCause v)"
unfolding dfn'CGetCause_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSetCause [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSetCause v)"
unfolding dfn'CSetCause_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CIncOffset [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CIncOffset v)"
unfolding dfn'CIncOffset_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CIncOffsetImmediate [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CIncOffsetImmediate v)"
unfolding dfn'CIncOffsetImmediate_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSetBounds [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSetBounds v)"
unfolding dfn'CSetBounds_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSetBoundsExact [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSetBoundsExact v)"
unfolding dfn'CSetBoundsExact_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSetBoundsImmediate [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSetBoundsImmediate v)"
unfolding dfn'CSetBoundsImmediate_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_ClearRegs [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (ClearRegs v)"
unfolding ClearRegs_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ClearLo [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ClearLo v)"
unfolding dfn'ClearLo_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'ClearHi [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'ClearHi v)"
unfolding dfn'ClearHi_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CClearLo [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CClearLo v)"
unfolding dfn'CClearLo_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CClearHi [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CClearHi v)"
unfolding dfn'CClearHi_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CClearTag [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CClearTag v)"
unfolding dfn'CClearTag_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CAndPerm [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CAndPerm v)"
unfolding dfn'CAndPerm_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSetOffset [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSetOffset v)"
unfolding dfn'CSetOffset_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSub [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSub v)"
unfolding dfn'CSub_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CCheckPerm [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CCheckPerm v)"
unfolding dfn'CCheckPerm_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CCheckType [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CCheckType v)"
unfolding dfn'CCheckType_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CFromPtr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CFromPtr v)"
unfolding dfn'CFromPtr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CToPtr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CToPtr v)"
unfolding dfn'CToPtr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_CPtrCmp [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (CPtrCmp v)"
unfolding CPtrCmp_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CEQ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CEQ v)"
unfolding dfn'CEQ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CNE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CNE v)"
unfolding dfn'CNE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLT [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLT v)"
unfolding dfn'CLT_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLE [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLE v)"
unfolding dfn'CLE_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLTU v)"
unfolding dfn'CLTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLEU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLEU v)"
unfolding dfn'CLEU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CEXEQ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CEXEQ v)"
unfolding dfn'CEXEQ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CNEXEQ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CNEXEQ v)"
unfolding dfn'CNEXEQ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CBTU [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CBTU v)"
unfolding dfn'CBTU_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CBTS [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CBTS v)"
unfolding dfn'CBTS_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CBEZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CBEZ v)"
unfolding dfn'CBEZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CBNZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CBNZ v)"
unfolding dfn'CBNZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSC v)"
unfolding dfn'CSC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLC v)"
unfolding dfn'CLC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLoad [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLoad v)"
unfolding dfn'CLoad_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_store [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (store v)"
unfolding store_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CStore [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CStore v)"
unfolding dfn'CStore_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLLC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLLC v)"
unfolding dfn'CLLC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CLLx [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CLLx v)"
unfolding dfn'CLLx_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSCC [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSCC v)"
unfolding dfn'CSCC_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSCx [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSCx v)"
unfolding dfn'CSCx_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CMOVN [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CMOVN v)"
unfolding dfn'CMOVN_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CMOVZ [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CMOVZ v)"
unfolding dfn'CMOVZ_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CMove [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CMove v)"
unfolding dfn'CMove_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CTestSubset [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CTestSubset v)"
unfolding dfn'CTestSubset_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CBuildCap [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CBuildCap v)"
unfolding dfn'CBuildCap_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CCopyType [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CCopyType v)"
unfolding dfn'CCopyType_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CJR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CJR v)"
unfolding dfn'CJR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CJALR [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CJALR v)"
unfolding dfn'CJALR_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CSeal [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CSeal v)"
unfolding dfn'CSeal_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CUnseal [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CUnseal v)"
unfolding dfn'CUnseal_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CCall [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CCall v)"
unfolding dfn'CCall_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CCallFast [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CCallFast v)"
unfolding dfn'CCallFast_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_special_register_accessible [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (special_register_accessible v)"
unfolding special_register_accessible_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CReadHwr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CReadHwr v)"
unfolding dfn'CReadHwr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CWriteHwr [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (dfn'CWriteHwr v)"
unfolding dfn'CWriteHwr_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'CReturn [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'CReturn"
unfolding dfn'CReturn_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_dfn'UnknownCapInstruction [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) dfn'UnknownCapInstruction"
unfolding dfn'UnknownCapInstruction_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_log_instruction [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (log_instruction v)"
unfolding log_instruction_alt_def
by (Invariant intro: ExceptionSignalledI)

lemma ExceptionSignalled_Run [ExceptionSignalledI]:
  shows "IsInvariant (read_state getExceptionSignalled) (Run v)"
unfolding Run_alt_def
by (Invariant intro: ExceptionSignalledI)

(* Code generation - skip - Next *)

(* Code generation - end *)

(*<*)
end
(*>*)
