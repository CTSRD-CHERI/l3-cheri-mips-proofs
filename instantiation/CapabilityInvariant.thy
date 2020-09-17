(*<*) 

(* Author: Kyndylan Nienhuis *)

theory CapabilityInvariant

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
  "Execute"
begin

(*>*)
section \<open>Capability invariance\<close>

named_theorems CapInvariantI

method CapInvariant uses simp intro =
  (PrePost intro: intro[THEN PrePost_post_weakening]
                  CapInvariantI[THEN PrePost_post_weakening])

declare UndefinedCase_raise'exception [CapInvariantI]

definition CapInvariantPre where 
  "CapInvariantPre loc cap \<equiv> 
   bind (read_state (getCap loc))
        (\<lambda>v. return (v = cap))"

definition CapInvariantTakeBranchPre where 
  "CapInvariantTakeBranchPre loc cap \<equiv> 
   read_state getExceptionSignalled \<or>\<^sub>b
   read_state isUnpredictable \<or>\<^sub>b
   (bind TakeBranchActions
         (\<lambda>p. return (\<forall>x\<in>p. loc \<notin> CapDerivationTargets x)) \<and>\<^sub>b
    bind (read_state BranchToPCC)
         (\<lambda>branchTo. bind (read_state (getCap loc))
         (\<lambda>cap'. let v = (if loc = LocReg RegBranchDelayPCC
                          then (case branchTo of None \<Rightarrow> cap'
                                               | Some (_, x) \<Rightarrow> x)
                          else if loc = LocReg RegBranchToPCC then nullCap 
                          else cap') in
                 return (v = cap))))"

lemma CapInvariantTakeBranchPre_StatePart [simp]:
  shows "StatePart (CapInvariantTakeBranchPre loc cap) s = s"
unfolding CapInvariantTakeBranchPre_def
by simp

lemma Commute_CapInvariantTakeBranchPre [Commute_compositeI]:
  assumes "Commute (read_state getPCC) m"
      and "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state BranchToPCC) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMemCap a)) m"
      and "Commute (read_state getExceptionSignalled) m"
      and "Commute (read_state isUnpredictable) m"
  shows "Commute (CapInvariantTakeBranchPre loc cap) m"
unfolding CapInvariantTakeBranchPre_def
by (Commute intro: assms)

lemma getExceptionSignalled_CapInvariantTakeBranchPre [elim!]:
  assumes "getExceptionSignalled s"
  shows "ValuePart (CapInvariantTakeBranchPre loc cap) s"
using assms
unfolding CapInvariantTakeBranchPre_def 
by (auto simp: ValueAndStatePart_simp)

lemma isUnpredictable_CapInvariantTakeBranchPre [elim!]:
  assumes "isUnpredictable s"
  shows "ValuePart (CapInvariantTakeBranchPre loc cap) s"
using assms
unfolding CapInvariantTakeBranchPre_def 
by (auto simp: ValueAndStatePart_simp)

lemma CapInvariantTakeBranchPre_setRaise'exception [simp]:
  shows "ValuePart (CapInvariantTakeBranchPre loc cap) 
                   (setRaise'exception (UNPREDICTABLE ex) s)"
by (intro isUnpredictable_CapInvariantTakeBranchPre) auto 

definition CapInvariantPost where 
  "CapInvariantPost loc cap \<equiv> 
   read_state getExceptionSignalled \<or>\<^sub>b
   read_state isUnpredictable \<or>\<^sub>b
   bind (read_state (getCap loc)) (\<lambda>v. return (v = cap))"

lemma Commute_CapInvariantPost [Commute_compositeI]:
  assumes "Commute (read_state getPCC) m"
      and "Commute (read_state BranchDelayPCC) m"
      and "Commute (read_state BranchToPCC) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMemCap a)) m"
      and "Commute (read_state getExceptionSignalled) m"
      and "Commute (read_state isUnpredictable) m"
  shows "Commute (CapInvariantPost loc cap) m"
unfolding CapInvariantPost_def
by (Commute intro: assms)

lemma CapInvariant_BranchToPCC_update [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocReg RegBranchDelayPCC)))  
                 (update_state (BranchToPCC_update (\<lambda>_. v))) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
by PrePost (cases loc, auto split: option.splits)

(* Code generation - start - capability invariant *)

lemma CapInvariant_CheckBranch [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) CheckBranch"
unfolding CheckBranch_alt_def
by CapInvariant

lemma CapInvariant_BranchNotTaken [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) BranchNotTaken"
unfolding BranchNotTaken_alt_def
by CapInvariant

lemma CapInvariant_BranchLikelyNotTaken [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) BranchLikelyNotTaken"
unfolding BranchLikelyNotTaken_alt_def
by CapInvariant

(* Code generation - override - write'PCC *)

lemma CapInvariant_write'PCC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocReg RegPCC))) 
                 (write'PCC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
by PrePost (cases loc, auto split: option.splits)

(* Code generation - end override *)

(* Code generation - override - write'CAPR *)

lemma CapInvariant_write'CAPR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocReg (RegGeneral (snd v)) \<or> snd v = 0)))  
                 (write'CAPR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
by PrePost (cases loc, auto split: option.splits)

(* Code generation - end override *)

(* Code generation - override - write'SCAPR *)

lemma CapInvariant_write'SCAPR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocReg (RegSpecial (snd v)))))  
                 (write'SCAPR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
by PrePost (cases loc, auto split: option.splits)

(* Code generation - end override *)

(* Code generation - override - SignalException *)

lemma getExceptionSignalled_SignalException:
  shows "PrePost (return True)
                 (SignalException ex)
                 (\<lambda>_. read_state getExceptionSignalled)"
by PrePost

lemma CapInvariant_SignalException [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalException v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
by (CapInvariant intro: getExceptionSignalled_SignalException)

(* Code generation - end override *)

(* Code generation - override - SignalCP2UnusableException *)

lemma CapInvariant_SignalCP2UnusableException [CapInvariantI]:
  shows "PrePost (return True) 
                 SignalCP2UnusableException 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalCP2UnusableException_alt_def
by CapInvariant

(* Code generation - end override *)

(* Code generation - override - SignalCapException_internal *)

lemma CapInvariant_SignalCapException_internal [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalCapException_internal v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalCapException_internal_alt_def
by CapInvariant

(* Code generation - end override *)

(* Code generation - override - SignalCapException *)

lemma CapInvariant_SignalCapException [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalCapException v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalCapException_alt_def
by CapInvariant

(* Code generation - end override *)

(* Code generation - override - SignalCapException_noReg *)

lemma CapInvariant_SignalCapException_noReg [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalCapException_noReg v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalCapException_noReg_alt_def
by CapInvariant

(* Code generation - end override *)

lemma CapInvariant_dfn'ERET [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind ERETActions
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 dfn'ERET 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'ERET_alt_def ERETActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - SignalTLBException *)

lemma CapInvariant_SignalTLBException [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalTLBException v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalTLBException_alt_def
by CapInvariant

(* Code generation - end override *)

lemma CapInvariant_check_cca [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (check_cca v)"
unfolding check_cca_alt_def
by CapInvariant

lemma CapInvariant_AddressTranslation [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (AddressTranslation v)"
unfolding AddressTranslation_alt_def
by CapInvariant

(* Code generation - override - SignalTLBCapException *)

lemma CapInvariant_SignalTLBCapException [CapInvariantI]:
  shows "PrePost (return True) 
                 (SignalTLBCapException v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding SignalTLBCapException_alt_def
by CapInvariant

(* Code generation - end override *)

(* Code generation - skip - write'MEM *)

(* Code generation - skip - InitMEM *)

(* Code generation - override - WriteData *)

lemma CapInvariant_WriteData [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocMem (slice 2 (fst v)))))
                 (WriteData v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
unfolding WriteData_alt_def
by PrePost (cases loc, auto split: option.splits)

(* Code generation - end override *)

(* Code generation - override - WriteCap *)

lemma CapInvariant_WriteCap [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   return (loc \<noteq> LocMem (fst v))))
                 (WriteCap v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding CapInvariantTakeBranchPre_def
unfolding WriteCap_alt_def 
by PrePost (cases loc, auto split: option.splits)

(* Code generation - end override *)

lemma CapInvariant_AdjustEndian [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (AdjustEndian v)"
unfolding AdjustEndian_alt_def
by CapInvariant

lemma CapInvariant_LoadMemoryCap [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (LoadMemoryCap v)"
unfolding LoadMemoryCap_alt_def
by CapInvariant

lemma CapInvariant_LoadMemory [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (LoadMemory v)"
unfolding LoadMemory_alt_def
by CapInvariant

(* Code generation - override - LoadCap *)

lemma CapInvariant_LoadCap_aux_TakeBranchPre:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (LoadCap v)"
unfolding LoadCap_alt_def
by CapInvariant

lemma CapInvariant_LoadCap_aux_PhysicalAddress:
  shows "PrePost (bind (read_state (getPhysicalAddress (fst v, LOAD)))
                       (\<lambda>a. case a of None \<Rightarrow> return True 
                                     | Some _ \<Rightarrow> return (loc \<noteq> LocReg (RegGeneral cd))))
                 (LoadCap v) 
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (loc \<noteq> LocReg (RegGeneral cd)))"
proof -
  note [CapInvariantI del] = CapInvariant_AddressTranslation
  note [CapInvariantI] =
    PrePost_DefinedAddressTranslation[where p="\<lambda>x. return (loc \<noteq> LocReg (RegGeneral cd))"]
  show ?thesis
    unfolding LoadCap_alt_def
    by CapInvariant
qed

lemmas CapInvariant_LoadCap_aux_unpredictable = 
  PrePost_weakest_pre_disj
    [OF CapInvariant_LoadCap_aux_PhysicalAddress
        PrePost_weakest_pre_disj
          [OF UndefinedCase_LoadCap ExceptionSignalled_LoadCap]]

lemmas CapInvariant_LoadCap [CapInvariantI] =
  PrePost_weakest_pre_conj
      [OF CapInvariant_LoadCap_aux_unpredictable[where loc=loc]
          CapInvariant_LoadCap_aux_TakeBranchPre[where loc=loc]]
  for loc

(* Code generation - end override *)

(* Code generation - override - StoreMemoryCap *)

lemma CapInvariant_AdjustEndian_result:
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b 
                  read_state isUnpredictable \<or>\<^sub>b 
                  return (loc \<noteq> LocMem (slice 5 (snd v))))
                 (AdjustEndian v)
                 (\<lambda>x. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      return (loc \<noteq> LocMem (slice 5 x)))"
unfolding AdjustEndian_alt_def
by PrePost (auto simp: slice_xor)

lemmas CapInvariant_AdjustEndian_2 =
  PrePost_weakest_pre_conj
    [OF CapInvariant_AdjustEndian[where loc=loc] 
        CapInvariant_AdjustEndian_result[where loc=loc]]
  for loc

lemma CapInvariant_StoreMemoryCap [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   (case v of (MemType, AccessLength, MemElem, needAlign, vAddr, cond) \<Rightarrow>
                    bind (read_state (getPhysicalAddress (vAddr, STORE)))
                         (\<lambda>x. return (case x of None \<Rightarrow> True
                                              | Some a \<Rightarrow> loc \<noteq> LocMem (GetCapAddress a))))))
                 (StoreMemoryCap v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
proof -
  note [CapInvariantI del] = CapInvariant_AdjustEndian
  note [CapInvariantI] = CapInvariant_AdjustEndian_2[where loc=loc]
  note [CapInvariantI del] = CapInvariant_AddressTranslation
  note [CapInvariantI] = 
    PrePost_weakest_pre_conj
      [OF PrePost_DefinedAddressTranslation[where p="\<lambda>x. return (loc \<noteq> LocMem (slice 5 x))"]
          CapInvariant_AddressTranslation[where loc=loc]]
  show ?thesis
    unfolding StoreMemoryCap_alt_def GetCapAddress_def
    -- \<open>This takes a long time\<close>
    by CapInvariant auto?
qed

(* Code generation - end override *)

(* Code generation - override - StoreMemory *)

lemma CapInvariant_StoreMemory [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   (case v of (memType, accessLength, needAlign, memElem, vAddr, cond) \<Rightarrow>
                    bind (read_state (getPhysicalAddress (vAddr, STORE)))
                         (\<lambda>x. return (case x of None \<Rightarrow> True
                                              | Some a \<Rightarrow> loc \<noteq> LocMem (GetCapAddress a))))))
                 (StoreMemory v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding StoreMemory_alt_def
by CapInvariant auto?

(* Code generation - end override *)

(* Code generation - override - StoreCap *)

lemma CapInvariant_StoreCap [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (read_state getExceptionSignalled \<or>\<^sub>b
                   read_state isUnpredictable \<or>\<^sub>b
                   bind (read_state getLLbit)
                        (\<lambda>llbit. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>a. return (case a of None \<Rightarrow> True
                                            |  Some x \<Rightarrow> (cond \<longrightarrow> llbit = Some True) \<longrightarrow>
                                                         loc \<noteq> LocMem (GetCapAddress x))))))
                 (StoreCap (vAddr, cap', cond)) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
proof -
  note [CapInvariantI del] = CapInvariant_AddressTranslation
  note PrePost_DefinedAddressTranslation
    [where p="\<lambda>x. bind (read_state getLLbit)
                       (\<lambda>llbit. return ((cond \<longrightarrow> llbit = Some True) \<longrightarrow>
                                        loc \<noteq> LocMem (slice 5 x)))"]
  note [CapInvariantI] = 
    PrePost_weakest_pre_conj[OF this CapInvariant_AddressTranslation[where loc=loc]] 
  show ?thesis
    unfolding StoreCap_alt_def GetCapAddress_def
    by simp CapInvariant
qed

(* Code generation - end override *)

(* Code generation - skip - Fetch *)

lemma CapInvariant_write'CP0R [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (write'CP0R v)"
unfolding write'CP0R_alt_def
by CapInvariant

lemma CapInvariant_mtc [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (mtc v)"
unfolding mtc_alt_def
by CapInvariant

lemma CapInvariant_dmtc [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dmtc v)"
unfolding dmtc_alt_def
by CapInvariant

lemma CapInvariant_mfc [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (mfc v)"
unfolding mfc_alt_def
by CapInvariant

lemma CapInvariant_dmfc [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dmfc v)"
unfolding dmfc_alt_def
by CapInvariant

lemma CapInvariant_dfn'ADDI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ADDI v)"
unfolding dfn'ADDI_alt_def
by CapInvariant

lemma CapInvariant_dfn'ADDIU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ADDIU v)"
unfolding dfn'ADDIU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DADDI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DADDI v)"
unfolding dfn'DADDI_alt_def
by CapInvariant

lemma CapInvariant_dfn'DADDIU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DADDIU v)"
unfolding dfn'DADDIU_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLTI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLTI v)"
unfolding dfn'SLTI_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLTIU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLTIU v)"
unfolding dfn'SLTIU_alt_def
by CapInvariant

lemma CapInvariant_dfn'ANDI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ANDI v)"
unfolding dfn'ANDI_alt_def
by CapInvariant

lemma CapInvariant_dfn'ORI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ORI v)"
unfolding dfn'ORI_alt_def
by CapInvariant

lemma CapInvariant_dfn'XORI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'XORI v)"
unfolding dfn'XORI_alt_def
by CapInvariant

lemma CapInvariant_dfn'LUI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'LUI v)"
unfolding dfn'LUI_alt_def
by CapInvariant

lemma CapInvariant_dfn'ADD [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ADD v)"
unfolding dfn'ADD_alt_def
by CapInvariant

lemma CapInvariant_dfn'ADDU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ADDU v)"
unfolding dfn'ADDU_alt_def
by CapInvariant

lemma CapInvariant_dfn'SUB [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SUB v)"
unfolding dfn'SUB_alt_def
by CapInvariant

lemma CapInvariant_dfn'SUBU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SUBU v)"
unfolding dfn'SUBU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DADD [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DADD v)"
unfolding dfn'DADD_alt_def
by CapInvariant

lemma CapInvariant_dfn'DADDU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DADDU v)"
unfolding dfn'DADDU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSUB [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSUB v)"
unfolding dfn'DSUB_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSUBU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSUBU v)"
unfolding dfn'DSUBU_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLT [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLT v)"
unfolding dfn'SLT_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLTU v)"
unfolding dfn'SLTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'AND [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'AND v)"
unfolding dfn'AND_alt_def
by CapInvariant

lemma CapInvariant_dfn'OR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'OR v)"
unfolding dfn'OR_alt_def
by CapInvariant

lemma CapInvariant_dfn'XOR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'XOR v)"
unfolding dfn'XOR_alt_def
by CapInvariant

lemma CapInvariant_dfn'NOR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'NOR v)"
unfolding dfn'NOR_alt_def
by CapInvariant

lemma CapInvariant_dfn'MOVN [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MOVN v)"
unfolding dfn'MOVN_alt_def
by CapInvariant

lemma CapInvariant_dfn'MOVZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MOVZ v)"
unfolding dfn'MOVZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'MADD [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MADD v)"
unfolding dfn'MADD_alt_def
by CapInvariant

lemma CapInvariant_dfn'MADDU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MADDU v)"
unfolding dfn'MADDU_alt_def
by CapInvariant

lemma CapInvariant_dfn'MSUB [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MSUB v)"
unfolding dfn'MSUB_alt_def
by CapInvariant

lemma CapInvariant_dfn'MSUBU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MSUBU v)"
unfolding dfn'MSUBU_alt_def
by CapInvariant

lemma CapInvariant_dfn'MUL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MUL v)"
unfolding dfn'MUL_alt_def
by CapInvariant

lemma CapInvariant_dfn'MULT [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MULT v)"
unfolding dfn'MULT_alt_def
by CapInvariant

lemma CapInvariant_dfn'MULTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MULTU v)"
unfolding dfn'MULTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DMULT [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DMULT v)"
unfolding dfn'DMULT_alt_def
by CapInvariant

lemma CapInvariant_dfn'DMULTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DMULTU v)"
unfolding dfn'DMULTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DIV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DIV v)"
unfolding dfn'DIV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DIVU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DIVU v)"
unfolding dfn'DIVU_alt_def
by CapInvariant

lemma CapInvariant_dfn'DDIV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DDIV v)"
unfolding dfn'DDIV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DDIVU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DDIVU v)"
unfolding dfn'DDIVU_alt_def
by CapInvariant

lemma CapInvariant_dfn'MFHI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MFHI v)"
unfolding dfn'MFHI_alt_def
by CapInvariant

lemma CapInvariant_dfn'MFLO [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MFLO v)"
unfolding dfn'MFLO_alt_def
by CapInvariant

lemma CapInvariant_dfn'MTHI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MTHI v)"
unfolding dfn'MTHI_alt_def
by CapInvariant

lemma CapInvariant_dfn'MTLO [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MTLO v)"
unfolding dfn'MTLO_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLL v)"
unfolding dfn'SLL_alt_def
by CapInvariant

lemma CapInvariant_dfn'SRL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SRL v)"
unfolding dfn'SRL_alt_def
by CapInvariant

lemma CapInvariant_dfn'SRA [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SRA v)"
unfolding dfn'SRA_alt_def
by CapInvariant

lemma CapInvariant_dfn'SLLV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SLLV v)"
unfolding dfn'SLLV_alt_def
by CapInvariant

lemma CapInvariant_dfn'SRLV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SRLV v)"
unfolding dfn'SRLV_alt_def
by CapInvariant

lemma CapInvariant_dfn'SRAV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'SRAV v)"
unfolding dfn'SRAV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSLL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSLL v)"
unfolding dfn'DSLL_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRL v)"
unfolding dfn'DSRL_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRA [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRA v)"
unfolding dfn'DSRA_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSLLV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSLLV v)"
unfolding dfn'DSLLV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRLV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRLV v)"
unfolding dfn'DSRLV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRAV [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRAV v)"
unfolding dfn'DSRAV_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSLL32 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSLL32 v)"
unfolding dfn'DSLL32_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRL32 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRL32 v)"
unfolding dfn'DSRL32_alt_def
by CapInvariant

lemma CapInvariant_dfn'DSRA32 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DSRA32 v)"
unfolding dfn'DSRA32_alt_def
by CapInvariant

lemma CapInvariant_dfn'TGE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TGE v)"
unfolding dfn'TGE_alt_def
by CapInvariant

lemma CapInvariant_dfn'TGEU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TGEU v)"
unfolding dfn'TGEU_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLT [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TLT v)"
unfolding dfn'TLT_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TLTU v)"
unfolding dfn'TLTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'TEQ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TEQ v)"
unfolding dfn'TEQ_alt_def
by CapInvariant

lemma CapInvariant_dfn'TNE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TNE v)"
unfolding dfn'TNE_alt_def
by CapInvariant

lemma CapInvariant_dfn'TGEI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TGEI v)"
unfolding dfn'TGEI_alt_def
by CapInvariant

lemma CapInvariant_dfn'TGEIU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TGEIU v)"
unfolding dfn'TGEIU_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLTI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TLTI v)"
unfolding dfn'TLTI_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLTIU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TLTIU v)"
unfolding dfn'TLTIU_alt_def
by CapInvariant

lemma CapInvariant_dfn'TEQI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TEQI v)"
unfolding dfn'TEQI_alt_def
by CapInvariant

lemma CapInvariant_dfn'TNEI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'TNEI v)"
unfolding dfn'TNEI_alt_def
by CapInvariant

lemma CapInvariant_loadByte [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (loadByte v)"
unfolding loadByte_alt_def
by CapInvariant

lemma CapInvariant_loadHalf [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (loadHalf v)"
unfolding loadHalf_alt_def
by CapInvariant

lemma CapInvariant_loadWord [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (loadWord v)"
unfolding loadWord_alt_def
by CapInvariant

lemma CapInvariant_loadDoubleword [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (loadDoubleword v)"
unfolding loadDoubleword_alt_def
by CapInvariant

lemma CapInvariant_dfn'LB [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LBActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LB v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LB_alt_def LBActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LBU [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LBUActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LBU v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LBU_alt_def LBUActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LH [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LHActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LH v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LH_alt_def LHActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LHU [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LHUActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LHU v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LHU_alt_def LHUActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LW [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LWActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LW v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LW_alt_def LWActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LWU [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LWUActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LWU v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LWU_alt_def LWUActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LL [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LLActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LL v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LL_alt_def LLActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LD [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LDActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LD v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LD_alt_def LDActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LLD [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LLDActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LLD v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LLD_alt_def LLDActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LWL [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LWLActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LWL v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LWL_alt_def LWLActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LWR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LWRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LWR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LWR_alt_def LWRActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LDL [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LDLActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LDL v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LDL_alt_def LDLActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'LDR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (LDRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'LDR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'LDR_alt_def LDRActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SB [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SBActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SB v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SB_alt_def SBActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SH [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SHActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SH v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SH_alt_def SHActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - storeWord *)

lemma CapInvariant_storeWord [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (case v of (b, rt, offset, cond) \<Rightarrow>
                   bind (read_state (getGPR b))
                        (\<lambda>v. bind (read_state (getSCAPR 0))
                        (\<lambda>cap. bind (return (scast offset + v + getBase cap + getOffset cap))
                        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> return (loc \<noteq> LocMem (GetCapAddress a'))))))))
                 (storeWord v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding storeWord_alt_def 
unfolding getVirtualAddress_alt_def
by CapInvariant auto?

(* Code generation - end override *)

(* Code generation - override - storeDoubleword *)

lemma CapInvariant_storeDoubleword [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  (case v of (b, rt, offset, cond) \<Rightarrow>
                   bind (read_state (getGPR b))
                        (\<lambda>v. bind (read_state (getSCAPR 0))
                        (\<lambda>cap. bind (return (scast offset + v + getBase cap + getOffset cap))
                        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> return (loc \<noteq> LocMem (GetCapAddress a'))))))))
                 (storeDoubleword v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding storeDoubleword_alt_def 
unfolding getVirtualAddress_alt_def
by CapInvariant auto?

(* Code generation - end override *)

lemma CapInvariant_dfn'SW [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SWActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SW v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SW_alt_def SWActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SD [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SDActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SD v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SD_alt_def SDActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SCActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SC_alt_def SCActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SCD [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SCDActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SCD v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SCD_alt_def SCDActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'SWL [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SWLActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SWL v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SWL_alt_def SWLActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - dfn'SWR *)

lemma CapInvariant_dfn'SWR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SWRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SWR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
proof -
  have [simp]: "x AND - 4 = x AND NOT mask 2" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  show ?thesis
    unfolding dfn'SWR_alt_def SWRActions_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by CapInvariant auto?
qed

(* Code generation - end override *)

lemma CapInvariant_dfn'SDL [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SDLActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SDL v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'SDL_alt_def SDLActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - dfn'SDR *)

lemma CapInvariant_dfn'SDR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (SDRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'SDR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
proof -
  have [simp]: "x AND - 8 = x AND NOT mask 3" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  show ?thesis
    unfolding dfn'SDR_alt_def SDRActions_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by CapInvariant auto?
qed

(* Code generation - end override *)

lemma CapInvariant_dfn'BREAK [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'BREAK"
unfolding dfn'BREAK_alt_def
by CapInvariant

lemma CapInvariant_dfn'SYSCALL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'SYSCALL"
unfolding dfn'SYSCALL_alt_def
by CapInvariant

lemma CapInvariant_dfn'MTC0 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MTC0 v)"
unfolding dfn'MTC0_alt_def
by CapInvariant

lemma CapInvariant_dfn'DMTC0 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DMTC0 v)"
unfolding dfn'DMTC0_alt_def
by CapInvariant

lemma CapInvariant_dfn'MFC0 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'MFC0 v)"
unfolding dfn'MFC0_alt_def
by CapInvariant

lemma CapInvariant_dfn'DMFC0 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'DMFC0 v)"
unfolding dfn'DMFC0_alt_def
by CapInvariant

lemma CapInvariant_dfn'J [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'J v)"
unfolding dfn'J_alt_def
by CapInvariant

lemma CapInvariant_dfn'JAL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'JAL v)"
unfolding dfn'JAL_alt_def
by CapInvariant

lemma CapInvariant_dfn'JALR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'JALR v)"
unfolding dfn'JALR_alt_def
by CapInvariant

lemma CapInvariant_dfn'JR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'JR v)"
unfolding dfn'JR_alt_def
by CapInvariant

lemma CapInvariant_dfn'BEQ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BEQ v)"
unfolding dfn'BEQ_alt_def
by CapInvariant

lemma CapInvariant_dfn'BNE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BNE v)"
unfolding dfn'BNE_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLEZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLEZ v)"
unfolding dfn'BLEZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGTZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGTZ v)"
unfolding dfn'BGTZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLTZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLTZ v)"
unfolding dfn'BLTZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGEZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGEZ v)"
unfolding dfn'BGEZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLTZAL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLTZAL v)"
unfolding dfn'BLTZAL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGEZAL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGEZAL v)"
unfolding dfn'BGEZAL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BEQL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BEQL v)"
unfolding dfn'BEQL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BNEL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BNEL v)"
unfolding dfn'BNEL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLEZL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLEZL v)"
unfolding dfn'BLEZL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGTZL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGTZL v)"
unfolding dfn'BGTZL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLTZL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLTZL v)"
unfolding dfn'BLTZL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGEZL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGEZL v)"
unfolding dfn'BGEZL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BLTZALL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BLTZALL v)"
unfolding dfn'BLTZALL_alt_def
by CapInvariant

lemma CapInvariant_dfn'BGEZALL [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'BGEZALL v)"
unfolding dfn'BGEZALL_alt_def
by CapInvariant

lemma CapInvariant_dfn'RDHWR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'RDHWR v)"
unfolding dfn'RDHWR_alt_def
by CapInvariant

lemma CapInvariant_dfn'CACHE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CACHE v)"
unfolding dfn'CACHE_alt_def
by CapInvariant

lemma CapInvariant_dfn'ReservedInstruction [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'ReservedInstruction"
unfolding dfn'ReservedInstruction_alt_def
by CapInvariant

lemma CapInvariant_dfn'Unpredictable [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'Unpredictable"
unfolding dfn'Unpredictable_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLBP [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'TLBP"
unfolding dfn'TLBP_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLBR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'TLBR"
unfolding dfn'TLBR_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLBWI [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'TLBWI"
unfolding dfn'TLBWI_alt_def
by CapInvariant

lemma CapInvariant_dfn'TLBWR [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'TLBWR"
unfolding dfn'TLBWR_alt_def
by CapInvariant

lemma CapInvariant_dfn'COP1 [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'COP1 v)"
unfolding dfn'COP1_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetBase [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetBase v)"
unfolding dfn'CGetBase_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetOffset [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetOffset v)"
unfolding dfn'CGetOffset_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetLen [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetLen v)"
unfolding dfn'CGetLen_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetTag [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetTag v)"
unfolding dfn'CGetTag_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetSealed [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetSealed v)"
unfolding dfn'CGetSealed_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetPerm [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetPerm v)"
unfolding dfn'CGetPerm_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetType [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetType v)"
unfolding dfn'CGetType_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetAddr [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetAddr v)"
unfolding dfn'CGetAddr_alt_def
by CapInvariant

lemma CapInvariant_dfn'CGetPCC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CGetPCCActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CGetPCC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CGetPCC_alt_def CGetPCCActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CGetPCCSetOffset [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CGetPCCSetOffsetActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CGetPCCSetOffset v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CGetPCCSetOffset_alt_def CGetPCCSetOffsetActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CGetCause [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CGetCause v)"
unfolding dfn'CGetCause_alt_def
by CapInvariant

lemma CapInvariant_dfn'CSetCause [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CSetCause v)"
unfolding dfn'CSetCause_alt_def
by CapInvariant

lemma CapInvariant_dfn'CIncOffset [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CIncOffsetActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CIncOffset v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CIncOffset_alt_def CIncOffsetActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CIncOffsetImmediate [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CIncOffsetImmediateActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CIncOffsetImmediate v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CIncOffsetImmediate_alt_def CIncOffsetImmediateActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSetBounds [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSetBoundsActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSetBounds v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSetBounds_alt_def CSetBoundsActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSetBoundsExact [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSetBoundsExactActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSetBoundsExact v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSetBoundsExact_alt_def CSetBoundsExactActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSetBoundsImmediate [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSetBoundsImmediateActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSetBoundsImmediate v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSetBoundsImmediate_alt_def CSetBoundsImmediateActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - ClearRegs *)

definition ClearRegLoopPre where
  "ClearRegLoopPre cond l loc cap \<equiv>
   read_state getExceptionSignalled \<or>\<^sub>b
   read_state isUnpredictable \<or>\<^sub>b
   (bind TakeBranchActions
         (\<lambda>p. return (\<forall>x\<in>p. loc \<notin> CapDerivationTargets x)) \<and>\<^sub>b
    bind (read_state BranchToPCC)
         (\<lambda>branchTo. bind (read_state (getCap loc))
         (\<lambda>cap'. let v = (if loc = LocReg RegBranchDelayPCC
                          then (case branchTo of None \<Rightarrow> cap'
                                               | Some (_, x) \<Rightarrow> x)
                          else if loc = LocReg RegBranchToPCC then nullCap
                          else cap') in
                 return (\<not> (\<exists>i\<in>set l. loc = LocReg (RegGeneral (word_of_int (int i))) \<and> cond i) \<and>
                         v = cap))))"

lemma ClearRegLoopPre_TakeBranchPre:
  fixes v :: "16 word"
  assumes "ValuePart (CapInvariantTakeBranchPre loc cap) s"
      and "\<And>i. i \<in> set l \<Longrightarrow>
               cond i \<Longrightarrow> 
               loc = LocReg (RegGeneral (word_of_int (int i))) \<Longrightarrow> 
               False"
  shows "ValuePart (ClearRegLoopPre cond l loc cap) s"
using assms
unfolding CapInvariantTakeBranchPre_def ClearRegLoopPre_def
by (auto simp: ValueAndStatePart_simp 
         split: CapLocation.splits CapRegister.splits)

lemma SemanticsRestrict_Instruction_ClearRegsLoop_aux:
  shows "PrePost (ClearRegLoopPre cond l loc cap)
                 (foreach_loop (l, \<lambda>i. if cond i 
                                       then write'CAPR (nullCap, word_of_int (int i)) 
                                       else return ()))
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
proof (induct l)
  case Nil
  thus ?case
    unfolding PrePost_def
    unfolding ClearRegLoopPre_def
    unfolding CapInvariantTakeBranchPre_def
    by (auto simp: ValueAndStatePart_simp 
             split: CapLocation.splits CapRegister.splits)
next
  case (Cons a l)
  have [simp]: "ValuePart TakeBranchActions (setCAPR v s) =
                ValuePart TakeBranchActions s" for v s
    unfolding TakeBranchActions_def
    by (simp add: ValueAndStatePart_simp)
  show ?case
    by (auto simp: PrePost_def[where m="write'CAPR _"]
             intro!: PrePost_weakest_pre_bind[OF Cons refl]
                     PrePost_pre_strengthening[OF Cons])
       (auto simp: ValueAndStatePart_simp ClearRegLoopPre_def
             split: CapLocation.splits CapRegister.splits option.splits)   
qed

lemma CapInvariant_ClearRegs [CapInvariantI]:
  shows "PrePost (case (snd v) of CLo_rs \<Rightarrow> ClearRegLoopPre (op !! (fst v)) (seq 0 15) loc cap 
                                | CHi_rs \<Rightarrow> ClearRegLoopPre (\<lambda>i. (fst v) !! (i - 16)) (seq 16 31) loc cap
                                | _ \<Rightarrow> CapInvariantTakeBranchPre loc cap)
                 (ClearRegs v)
                 (\<lambda>x. CapInvariantTakeBranchPre loc cap)"
proof -
  note [CapInvariantI] = SemanticsRestrict_Instruction_ClearRegsLoop_aux
  show ?thesis  
    unfolding ClearRegs_alt_def
    by CapInvariant auto?
qed
   
(* Code generation - end override *)

lemma CapInvariant_dfn'ClearLo [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ClearLo v)"
unfolding dfn'ClearLo_alt_def
by CapInvariant

lemma CapInvariant_dfn'ClearHi [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'ClearHi v)"
unfolding dfn'ClearHi_alt_def
by CapInvariant

(* Code generation - override - dfn'CClearLo *)

lemma CapInvariant_dfn'CClearLo_aux:
  fixes v :: "16 word"
  assumes "ValuePart (CapInvariantTakeBranchPre loc cap) s"
      and "\<And>x. v !! unat x \<Longrightarrow> 
               loc = LocReg (RegGeneral x) \<Longrightarrow> 
               False"
  shows "ValuePart (ClearRegLoopPre (op !! v) (seq 0 15) loc cap) s"
using assms(1)
proof (elim ClearRegLoopPre_TakeBranchPre)
  fix i
  assume test_bit: "v !! i" 
  assume seq: "i \<in> set (seq 0 15)"
  assume loc: "loc = LocReg (RegGeneral (word_of_int (int i)))"
  have [simp]: "int i mod 32 = int i"
    using test_bit_size[OF test_bit]
    unfolding word_size zmod_trival_iff
    by auto
  hence "v !! unat (word_of_int (int i)::5 word)"
    unfolding unat_def word_size uint_word_of_int
    using test_bit
    by auto
  from assms(2)[OF this loc]
  show False .
qed

lemma CapInvariant_dfn'CClearLo [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CClearLoActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CClearLo v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CClearLo_alt_def CClearLoActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant (auto elim: CapInvariant_dfn'CClearLo_aux)

(* Code generation - end override *)

(* Code generation - override - dfn'CClearHi *)

lemma CapInvariant_dfn'CClearHi_aux:
  fixes v :: "16 word"
  assumes "ValuePart (CapInvariantTakeBranchPre loc cap) s"
      and "\<And>x. v !! unat (x - 16) \<Longrightarrow> 
               loc = LocReg (RegGeneral x) \<Longrightarrow> 
               False"
  shows "ValuePart (ClearRegLoopPre (\<lambda>i. v !! (i - 16)) (seq 16 31) loc cap) s"
using assms(1)
proof (elim ClearRegLoopPre_TakeBranchPre)
  fix i
  assume test_bit: "v !! (i - 16)" 
  assume seq: "i \<in> set (seq 16 31)"
  assume loc: "loc = LocReg (RegGeneral (word_of_int (int i)))"
  have range: "16 \<le> i" "i \<le> 31"
    using seq
    unfolding set_seq
    by auto
  have [simp]: "int i mod 32 = int i"
    using range
    unfolding word_size zmod_trival_iff
    by auto
  have [simp]: "(int i - 16) mod 32 = int i - 16"
    using range
    unfolding word_size zmod_trival_iff
    by auto
  have "v !! unat (word_of_int (int i) - 16::5 word)"
    using test_bit range nat_diff_distrib'
    unfolding unat_def word_size uint_word_ariths uint_word_of_int
    by auto
  from assms(2)[OF this loc]
  show False .
qed

lemma CapInvariant_dfn'CClearHi [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CClearHiActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CClearHi v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CClearHi_alt_def CClearHiActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant (auto elim: CapInvariant_dfn'CClearHi_aux)

(* Code generation - end override *)

lemma CapInvariant_dfn'CClearTag [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CClearTagActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CClearTag v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CClearTag_alt_def CClearTagActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CAndPerm [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CAndPermActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CAndPerm v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CAndPerm_alt_def CAndPermActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSetOffset [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSetOffsetActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSetOffset v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSetOffset_alt_def CSetOffsetActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSub [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CSub v)"
unfolding dfn'CSub_alt_def
by CapInvariant

lemma CapInvariant_dfn'CCheckPerm [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CCheckPerm v)"
unfolding dfn'CCheckPerm_alt_def
by CapInvariant

lemma CapInvariant_dfn'CCheckType [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CCheckType v)"
unfolding dfn'CCheckType_alt_def
by CapInvariant

lemma CapInvariant_dfn'CFromPtr [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CFromPtrActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CFromPtr v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CFromPtr_alt_def CFromPtrActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CToPtr [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CToPtr v)"
unfolding dfn'CToPtr_alt_def
by CapInvariant

lemma CapInvariant_CPtrCmp [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (CPtrCmp v)"
unfolding CPtrCmp_alt_def
by CapInvariant

lemma CapInvariant_dfn'CEQ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CEQ v)"
unfolding dfn'CEQ_alt_def
by CapInvariant

lemma CapInvariant_dfn'CNE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CNE v)"
unfolding dfn'CNE_alt_def
by CapInvariant

lemma CapInvariant_dfn'CLT [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CLT v)"
unfolding dfn'CLT_alt_def
by CapInvariant

lemma CapInvariant_dfn'CLE [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CLE v)"
unfolding dfn'CLE_alt_def
by CapInvariant

lemma CapInvariant_dfn'CLTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CLTU v)"
unfolding dfn'CLTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'CLEU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CLEU v)"
unfolding dfn'CLEU_alt_def
by CapInvariant

lemma CapInvariant_dfn'CEXEQ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CEXEQ v)"
unfolding dfn'CEXEQ_alt_def
by CapInvariant

lemma CapInvariant_dfn'CNEXEQ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CNEXEQ v)"
unfolding dfn'CNEXEQ_alt_def
by CapInvariant

lemma CapInvariant_dfn'CBTU [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CBTU v)"
unfolding dfn'CBTU_alt_def
by CapInvariant

lemma CapInvariant_dfn'CBTS [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CBTS v)"
unfolding dfn'CBTS_alt_def
by CapInvariant

lemma CapInvariant_dfn'CBEZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CBEZ v)"
unfolding dfn'CBEZ_alt_def
by CapInvariant

lemma CapInvariant_dfn'CBNZ [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CBNZ v)"
unfolding dfn'CBNZ_alt_def
by CapInvariant

(* Code generation - override - dfn'CSC *)

lemma CapInvariant_dfn'CSC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  bind (CSCActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSC_alt_def CSCActions_def
unfolding CSCPhysicalAddress_def CSCVirtualAddress_def
by CapInvariant auto?

(* Code generation - end override *)

(* Code generation - override - dfn'CLC *)

lemma CapInvariant_dfn'CLC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  bind (CLCActions v)
                        (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CLC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CLC_alt_def CLCActions_def
unfolding CLCPhysicalAddress_def CLCVirtualAddress_def
by CapInvariant (auto split: option.splits if_splits)

(* Code generation - end override *)

lemma CapInvariant_dfn'CLoad [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CLoadActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CLoad v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CLoad_alt_def CLoadActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - skip - store *)

(* Code generation - override - dfn'CStore *)

lemma CapInvariant_dfn'CStore [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CStoreActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CStore v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CStore_alt_def CStoreActions_def
unfolding CStorePhysicalAddress_def CStoreVirtualAddress_def
unfolding store_alt_def CheckBranch_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto

(* Code generation - end override *)

(* Code generation - override - dfn'CLLC *)

lemma CapInvariant_dfn'CLLC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  bind (CLLCActions v)
                        (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CLLC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CLLC_alt_def CLLCActions_def
unfolding CLLCPhysicalAddress_def CLLCVirtualAddress_def
by CapInvariant (auto split: option.splits if_splits)

(* Code generation - end override *)

lemma CapInvariant_dfn'CLLx [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CLLxActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CLLx v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CLLx_alt_def CLLxActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

(* Code generation - override - dfn'CSCC *)

lemma CapInvariant_dfn'CSCC [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  bind (CSCCActions v)
                        (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSCC v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSCC_alt_def CSCCActions_def
unfolding CSCCPhysicalAddress_def CSCCVirtualAddress_def
by CapInvariant auto?

(* Code generation - end override *)

(* Code generation - override - dfn'CSCx *)

lemma CapInvariant_dfn'CSCx [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSCxActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSCx v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSCx_alt_def CSCxActions_def
unfolding CSCxPhysicalAddress_def CSCxVirtualAddress_def
unfolding store_alt_def CheckBranch_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto

(* Code generation - end override *)

lemma CapInvariant_dfn'CMOVN [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CMOVNActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CMOVN v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CMOVN_alt_def CMOVNActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CMOVZ [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CMOVZActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CMOVZ v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CMOVZ_alt_def CMOVZActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CMove [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CMoveActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CMove v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CMove_alt_def CMoveActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CTestSubset [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CTestSubset v)"
unfolding dfn'CTestSubset_alt_def
by CapInvariant

lemma CapInvariant_dfn'CBuildCap [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CBuildCapActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CBuildCap v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CBuildCap_alt_def CBuildCapActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CCopyType [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CCopyTypeActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CCopyType v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CCopyType_alt_def CCopyTypeActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CJR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CJRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CJR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CJR_alt_def CJRActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CJALR [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CJALRActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CJALR v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CJALR_alt_def CJALRActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CSeal [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CSealActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CSeal v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CSeal_alt_def CSealActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CUnseal [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CUnsealActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CUnseal v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CUnseal_alt_def CUnsealActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CCall [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) (dfn'CCall v)"
unfolding dfn'CCall_alt_def
by CapInvariant

(* Code generation - override - dfn'CCallFast *)

lemma CapInvariant_dfn'CCallFast [CapInvariantI]:
  shows "IsInvariant (return False) (dfn'CCallFast v)"
by CapInvariant

(* Code generation - end override *)

lemma CapInvariant_dfn'CReadHwr [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CReadHwrActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CReadHwr v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CReadHwr_alt_def CReadHwrActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CWriteHwr [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (CWriteHwrActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))))
                 (dfn'CWriteHwr v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding dfn'CWriteHwr_alt_def CWriteHwrActions_def
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by CapInvariant auto?

lemma CapInvariant_dfn'CReturn [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'CReturn"
unfolding dfn'CReturn_alt_def
by CapInvariant

lemma CapInvariant_dfn'UnknownCapInstruction [CapInvariantI]:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap) dfn'UnknownCapInstruction"
unfolding dfn'UnknownCapInstruction_alt_def
by CapInvariant

(* Code generation - override - Run *)

lemma CapInvariant_Run_aux:
  shows "PrePost (CapInvariantTakeBranchPre loc cap \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  bind (RunActions v)
                       (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p))) \<and>\<^sub>b
                  return (case v of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                  | _ \<Rightarrow> True))
                 (Run v) 
                 (\<lambda>_. CapInvariantTakeBranchPre loc cap)"
unfolding Run_alt_def RunActions_def
by CapInvariant auto?

lemmas CapInvariant_Run [CapInvariantI] =
  PrePost_weakest_pre_disj[OF CapInvariant_Run_aux
                              UndefinedCase_Run]

(* Code generation - end override *)

(* Code generation - override - Next *)

lemma CapInvariant_TakeBranch [CapInvariantI]:
  shows "PrePost (CapInvariantTakeBranchPre loc cap)
                 TakeBranch 
                 (\<lambda>_. CapInvariantPost loc cap)"
unfolding CapInvariantTakeBranchPre_def
unfolding CapInvariantPost_def
unfolding TakeBranch_def TakeBranchActions_def
by PrePost (auto simp: getBranchToPccCap_def split: option.splits if_splits)

lemma CapInvariant_Fetch_aux1:
  shows "IsInvariant (CapInvariantTakeBranchPre loc cap)
                     Fetch"
unfolding Fetch_alt_def
by CapInvariant

lemma CapInvariant_Fetch_aux2:
  fixes loc
  defines "p \<equiv> \<lambda>w. read_state getCP0ConfigBE \<and>\<^sub>b 
                    \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                    return (case Decode w of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                           | _ \<Rightarrow> True) \<and>\<^sub>b 
                    bind (RunActions (Decode w))
                         (\<lambda>p. return (loc \<notin> \<Union> (CapDerivationTargets ` p)))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled
                              | Some w \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p w)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemmas CapInvariant_Fetch [CapInvariantI] =
  PrePost_weakest_pre_conj
      [OF CapInvariant_Fetch_aux1[where loc=loc] 
          CapInvariant_Fetch_aux2[where loc=loc]] for loc

lemma CapInvariant_NextWithGhostState [CapInvariantI]:
  shows "PrePost (read_state getStateIsValid \<and>\<^sub>b
                  \<not>\<^sub>b (NextInstruction =\<^sub>b return None) \<and>\<^sub>b
                  (read_state (getCap loc) =\<^sub>b return cap) \<and>\<^sub>b
                  (read_state CCallFastInstructionParam =\<^sub>b return None) \<and>\<^sub>b
                  bind DomainActions
                       (\<lambda>p. return (\<forall>x\<in>p. loc \<notin> CapDerivationTargets x)))
                 NextWithGhostState
                 (\<lambda>_. CapInvariantPost loc cap)"
unfolding NextWithGhostState_def DomainActions_def
unfolding StateIsValid_def
by CapInvariant
   (auto simp: ValueAndStatePart_simp 
               getBranchToPccCap_def 
               CapInvariantTakeBranchPre_def
         split: option.splits
         dest: EmptyGhostStateE
         elim!: CCallFastInstructionParam_None)

(* Code generation - end override *)

(* Code generation - end *)

theorem CapabilityCapInvariant:
  assumes prov: "loc \<notin> \<Union> (CapDerivationTargets ` actions)"
      and valid: "getStateIsValid s"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "getCap loc s' = getCap loc s"
using assms
using CapInvariant_NextWithGhostState
        [where loc=loc and cap="getCap loc s",
         THEN PrePostE[where s=s]]
using DefinedNextInstruction[OF suc]
unfolding CapInvariantPost_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary CapabilityInvariantInstantiation [simp]:
  shows "CapabilityInvariant NextStates"
unfolding CapabilityInvariant_def
using CapabilityCapInvariant
by auto blast?

(*<*)
end
(*>*)