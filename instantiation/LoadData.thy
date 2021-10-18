(*<*) 

(* Author: Kyndylan Nienhuis *)

theory LoadData

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const LoadDataAction}\<close>

named_theorems SemanticsLoadDataI
  
method SemanticsLoadData uses intro =
  HoareTriple intro: intro SemanticsLoadDataI[THEN HoareTriple_post_weakening]

declare nonExceptionCase_exceptions [SemanticsLoadDataI]

definition AddressIsDataReadable :: 
  "Capability \<Rightarrow> (VirtualAddress \<times> AccessType \<Rightarrow> PhysicalAddress option) \<Rightarrow> 
   PhysicalAddress \<Rightarrow> PhysicalAddress \<Rightarrow> bool" 
where
  "AddressIsDataReadable authCap addrTrans a l \<equiv>
   Permit_Load (getPerms authCap) \<and> 
   getTag authCap \<and>
   \<not> getSealed authCap \<and>
   l \<noteq> 0 \<and>
   (\<forall>a'\<in>Region a l. 
    \<exists>vAddr\<in>RegionOfCap authCap.
    addrTrans (vAddr, LOAD) = Some a')"

lemma getExceptionSignalled_AdjustEndian:
  shows "IsInvariant (read_state getExceptionSignalled) (AdjustEndian v)"
by HoareTriple

lemmas SemanticsLoadData_dfn'LoadMemoryCap_aux =
  HoareTriple_weakest_pre_disj[OF 
    getExceptionSignalled_AdjustEndian
    UndefinedCase_AdjustEndian]

lemma SemanticsLoadData_dfn'LoadMemoryCap:
  shows "HoareTriple ((return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  return ((case v of (memType, needAlign, vAddr, link) \<Rightarrow>
                           (needAlign \<and> \<not> unat vAddr mod 8 + unat memType < 8) \<or>
                            (addrTrans (vAddr, LOAD) = None))))
                 (LoadMemoryCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable)"
unfolding LoadMemoryCap_alt_def
by (HoareTriple intro: 
       SemanticsLoadData_dfn'LoadMemoryCap_aux[THEN HoareTriple_post_weakening]
       HoareTriple_DefinedAddressTranslation[where p="\<lambda>x. return False", THEN HoareTriple_post_weakening])
   (auto simp: getTranslateAddrFunc_def
         dest!: isAligned_max_length)

lemma SemanticsLoadData_dfn'LoadMemory_aux:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getSCAPR 0)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  return ((case v of (memType, accessLength, needAlign, vAddr, link) \<Rightarrow>
                           (a = the (addrTrans (vAddr, LOAD))) \<and>
                           (l = ucast accessLength + 1) \<and>
                           ((needAlign \<and> memType = accessLength) \<or> 
                            unat vAddr mod 8 + unat accessLength < 8))))
                 (LoadMemory v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l))"
proof -
  note [SemanticsLoadDataI] =
    HoareTriple_weakest_pre_disj[OF
      SemanticsLoadData_dfn'LoadMemoryCap[where addrTrans=addrTrans]
      IsInvariant_constant[where x="AddressIsDataReadable authCap addrTrans a l"]]
  have [simp]: "ucast (x::3 word) \<noteq> (max_word::40 word)" (is "?l \<noteq> ?r") for x
    using test_bit_size[where w=x and n=4]
    by (auto simp: nth_ucast word_size dest!: test_bit_cong[where x=4])
  show ?thesis
    unfolding LoadMemory_alt_def
    by SemanticsLoadData
       (auto simp: not_le not_less max_word_wrap_eq
                   getTranslateAddrFunc_def
                   AddressIsDataReadable_def
             elim: TranslateNearbyAddress_LegacyInstructions)
qed

lemmas SemanticsLoadData_dfn'LoadMemory =
  HoareTriple_weakest_pre_conj[OF SemanticsLoadData_dfn'LoadMemory_aux
                              IsInvariant_constant[where x=authAccessible]]
  for authAccessible

lemma SemanticsLoadData_dfn'LoadCap:
  shows "HoareTriple ((return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  return ((case v of (vAddr, cond) \<Rightarrow>
                           addrTrans (vAddr, LOAD) = None)))
                 (LoadCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable)"
unfolding LoadCap_alt_def
by (HoareTriple intro: 
       HoareTriple_DefinedAddressTranslation
         [where p="\<lambda>x. return False", THEN HoareTriple_post_weakening])
   (auto simp: getTranslateAddrFunc_def)

lemma SemanticsLoadData_dfn'LB [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LBActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LB v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LB_alt_def LBActions_def loadByte_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def 
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LBU [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LBUActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LBU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LBU_alt_def LBUActions_def loadByte_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def 
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LH [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LHActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LH v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LH_alt_def LHActions_def loadHalf_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LHU [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LHUActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LHU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LHU_alt_def LHUActions_def loadHalf_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LW [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LWActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LW v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LW_alt_def LWActions_def loadWord_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LWU [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LWUActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LWU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LWU_alt_def LWUActions_def loadWord_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LL [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LLActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LL_alt_def LLActions_def loadWord_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LD [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LDActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LD_alt_def LDActions_def loadDoubleword_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LLD [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LLDActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LLD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LLD_alt_def LLDActions_def loadDoubleword_alt_def
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def split: option.splits)
qed

lemma SemanticsLoadData_dfn'LWL [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LWLActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LWL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LWL_alt_def LWLActions_def 
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def 
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def
                   ucast_and ucast_not
                   unat_not unat_and_mask unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsLoadData_dfn'LWR [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LWRActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LWR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  have [simp]: "x AND - 4 = x AND NOT mask 2" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  have [simp]: "3 - (NOT x AND mask 2) = x AND mask 2" for x :: "'a::len word"
    using mask_minus_word_and_mask[where x="NOT x" and n=2]
    unfolding mask_def
    by simp
  have "(4::nat) dvd 8"
    by arith
  note [simp] = mod_mod_cancel[OF this]
  have "4 * x mod 8 \<le> 4" for x :: nat
    by arith
  from add_le_less_mono[where d=4, OF this]
  have [simp]: "4 * x mod 8 + y mod 4 < 8" for x y :: nat
    by simp
  show ?thesis
    unfolding dfn'LWR_alt_def LWRActions_def 
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def
                   ucast_and ucast_not
                   unat_not unat_and_mask unat_and_not_mask unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsLoadData_dfn'LDL [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LDLActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LDL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'LDL_alt_def LDLActions_def 
    unfolding LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def
                   unat_and_mask ucast_not unat_not unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsLoadData_dfn'LDR [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (LDRActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'LDR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_dfn'LoadMemory[where authAccessible=authAccessible]
  have [simp]: "x AND - 8 = x AND NOT mask 3" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  have [simp]: "7 - (NOT x) = x" for x :: "3 word"
    unfolding word_not_alt max_word_def
    by simp
  show ?thesis
    unfolding dfn'LDR_alt_def LDRActions_def 
    unfolding LegacyLoadActions_def LegacyLoadPhysicalAddress_def LegacyLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsLoadData
       (auto simp: getTranslateAddrFunc_def
                   unat_and_not_mask unat_and_mask mask_plus_one
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsLoadData_dfn'CLC [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLCActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'CLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] =
    HoareTriple_weakest_pre_disj[OF
      SemanticsLoadData_dfn'LoadCap[where addrTrans=addrTrans]
      IsInvariant_constant[where x="AddressIsDataReadable authCap addrTrans a l \<and> 
                                    authAccessible"]]
  show ?thesis
    unfolding dfn'CLC_alt_def CLCActions_def 
    unfolding CLCPhysicalAddress_def CLCVirtualAddress_def
    by SemanticsLoadData
       (auto simp: not_le not_less
                   getTranslateAddrFunc_def
                   AddressIsDataReadable_def
             split: if_splits
             elim!: TranslateNearbyAddress_CapAligned)
qed

lemma SemanticsLoadData_dfn'CLoad [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLoadActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'CLoad v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] =
    HoareTriple_weakest_pre_disj[OF
      SemanticsLoadData_dfn'LoadMemoryCap[where addrTrans=addrTrans]
      IsInvariant_constant[where x="AddressIsDataReadable authCap addrTrans a l \<and> 
                                    authAccessible"]]
  have "n mod 32 \<le> n mod 8 + 24" for n :: nat 
    proof -
      have "n mod 32 = (n mod 32 mod 8) + 8 * (n mod 32 div 8)"
        by simp
      also have "... \<le> (n mod 8) + 24"
        using mod_mod_cancel[where a=n and b=32 and c=8]
        by auto
      finally show ?thesis .
    qed
  hence in_eq: "n mod 32 \<le> m" if "n mod 8 + 24 \<le> m" for m n :: nat
    by (rule order.trans[OF _ that])
  show ?thesis
    unfolding dfn'CLoad_alt_def CLoadActions_def 
    unfolding CLoadPhysicalAddress_def CLoadVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    by SemanticsLoadData
       (cases rule: exhaustive_2_word[where x="case v of (_, _, _, _, _, t) \<Rightarrow> t"],
        auto simp: not_le not_less 
                   unat_mask unat_max_word
                   getTranslateAddrFunc_def
                   AddressIsDataReadable_def
             intro!: in_eq
             elim!: TranslateNearbyAddress[where accessLength=1]
                    TranslateNearbyAddress[where accessLength=2]
                    TranslateNearbyAddress[where accessLength=4]
                    TranslateNearbyAddress[where accessLength=8])
qed

lemma SemanticsLoadData_dfn'CLLC [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLLCActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'CLLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] =
    HoareTriple_weakest_pre_disj[OF
      SemanticsLoadData_dfn'LoadCap[where addrTrans=addrTrans]
      IsInvariant_constant[where x="AddressIsDataReadable authCap addrTrans a l \<and> 
                                    authAccessible"]]
  show ?thesis
    unfolding dfn'CLLC_alt_def CLLCActions_def 
    unfolding CLLCPhysicalAddress_def CLLCVirtualAddress_def
    by SemanticsLoadData
       (auto simp: not_le not_less
                   getTranslateAddrFunc_def
                   AddressIsDataReadable_def
             split: if_splits
             elim!: TranslateNearbyAddress_CapAligned)
qed

lemma SemanticsLoadData_dfn'CLLx_aux:
  fixes auth s
  fixes stt :: "3 word"
  defines "cap \<equiv> getCapReg auth s"
  defines "vAddr \<equiv> getBase cap + getOffset cap" 
      and "(accessLength::65 word) \<equiv> ucast ((2::40 word) ^ unat (stt AND mask 2))"
  assumes v_upper: "ucast vAddr + accessLength \<le> ucast (getBase cap) + ucast (getLength cap)"
      and v_lower: "getBase cap \<le> vAddr"
      and alignment: "unat vAddr mod 32 + unat accessLength \<le> 32"
      and pAddr: "getTranslateAddr (vAddr, LOAD) s = Some a"
      and length: "l = ucast accessLength"
  shows "\<forall>a'\<in>Region a l.
         \<exists>vAddr \<in> RegionOfCap cap. 
         getTranslateAddr (vAddr, LOAD) s = Some a'"
proof -
  have min: "1 \<le> accessLength"
    unfolding accessLength_def word_le_def unat_and_mask 
    by (auto simp: uint_power_two)
  have "(2::int) ^ (unat stt mod 4) \<le> 2 ^ 4"
    by (rule power_increasing_iff[THEN iffD2]) simp_all
  hence max: "accessLength \<le> 32"
    unfolding accessLength_def word_le_def unat_and_mask
    by (auto simp: uint_power_two)
  show ?thesis
    unfolding length
    using TranslateNearbyAddress[OF v_upper v_lower min max alignment pAddr]
    by metis
qed

lemma SemanticsLoadData_dfn'CLLx [SemanticsLoadDataI]:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLLxActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (dfn'CLLx v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] =
    HoareTriple_weakest_pre_disj[OF
      SemanticsLoadData_dfn'LoadMemoryCap[where addrTrans=addrTrans]
      IsInvariant_constant[where x="AddressIsDataReadable authCap addrTrans a l \<and> 
                                    authAccessible"]]
  have *: "(2::int) ^ (unat x mod 4) \<le> 2 ^ 4" for x :: "3 word"
    by (rule power_increasing_iff[THEN iffD2]) simp_all
  have [simp]: "(2::65 word) ^ (unat x mod 4) AND mask 40 = 2 ^ (unat x mod 4)"
  for x :: "3 word"
    unfolding mask_eq_iff uint_power_two unat_and_mask
    using *[where x=x]
    by simp
  have [simp]: "(2::65 word) ^ (unat x mod 4) AND mask 64 = 2 ^ (unat x mod 4)"
  for x :: "3 word"
    unfolding mask_eq_iff uint_power_two unat_and_mask
    using *[where x=x]
    by simp
  have [simp]: "(unat x mod 4) = 0" if "(ucast x::2 word) = 0" for x :: "3 word"
    using ucast_eq_imp_and_mask_eq[where y=0 and 'a=3 and 'b=2 and n=2] that
    unfolding unat_arith_simps unat_and_mask
    by simp
  have [simp]: "unat ((2::65 word) ^ (unat x mod 4)) = 2 ^ (unat x mod 4)" for x :: "3 word"
    unfolding unat_power_two 
    by simp
  have [simp]: "min (unat x mod 4) 3 = unat x mod 4" for x :: "3 word"
    by simp
  have "n mod 32 \<le> n mod 8 + 24" for n :: nat 
    proof -
      have "n mod 32 = (n mod 32 mod 8) + 8 * (n mod 32 div 8)"
        by simp
      also have "... \<le> (n mod 8) + 24"
        using mod_mod_cancel[where a=n and b=32 and c=8]
        by auto
      finally show ?thesis .
    qed
  from add_le_mono1[OF this]
  have in_eq: "n mod 32 + k \<le> m" if "n mod 8 + 24 + k \<le> m" for m n k :: nat
    by (rule order.trans[OF _ that])
  show ?thesis
    unfolding dfn'CLLx_alt_def CLLxActions_def
    unfolding CLLxPhysicalAddress_def CLLxVirtualAddress_def
    by SemanticsLoadData
       (simple_auto simp: not_le not_less 
                          unat_mask unat_max_word unat_and_mask
                          ucast_power_two nat_power_eq
                          getTranslateAddrFunc_def
                          AddressIsDataReadable_def
                    intro: in_eq
                           all_split[where P="\<lambda>x. x", THEN iffD2]
                           disjCI[THEN Meson.disj_comm]
                           SemanticsLoadData_dfn'CLLx_aux
                              [where a=a and stt="case v of (_, _, stt) \<Rightarrow> stt"])
qed

lemma SemanticsLoadData_Run_aux:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (LoadDataAction auth a l \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def 
by (HoareTriple_cases;
    rule HoareTriple_pre_strengthening,
    rule SemanticsLoadDataI
         HoareTriple_weakest_pre_any,
    solves \<open>auto simp: ValueAndStatePart_simp\<close>)

lemmas SemanticsLoadData_Run =
  HoareTriple_weakest_pre_disj[OF SemanticsLoadData_Run_aux
                              UndefinedCase_Run]

lemma SemanticsLoadData_Fetch:
  fixes auth a a' l authCap addrTrans authAccessible
  defines "p \<equiv> \<lambda>w. (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                    (read_state getCP0ConfigBE) \<and>\<^sub>b
                    (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>ac. return (LoadDataAction auth a l \<in> ac))"
  shows "HoareTriple (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro HoareTriple_Fetch) Commute+

lemma SemanticsLoadData_NextWithGhostState:
  shows "HoareTriple ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>ac. return (LoadDataAction auth a l \<in> ac)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsDataReadable authCap addrTrans a l) \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_Run[where auth=auth and a=a and l=l and
                                 authCap=authCap and 
                                 addrTrans=addrTrans and
                                 authAccessible=authAccessible]
  note [SemanticsLoadDataI] = 
    SemanticsLoadData_Fetch[where auth=auth and a=a and l=l and
                                   authCap=authCap and 
                                   addrTrans=addrTrans and
                                   authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (SemanticsLoadData intro: UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsLoadData:
  assumes prov: "LoadDataAction auth a l \<in> actions"
      and valid: "getStateIsValid s"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "Permit_Load (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "Region a l \<subseteq> getTranslateAddresses (RegionOfCap (getCapReg auth s)) LOAD s"
        "getRegisterIsAccessible auth s"
        "l \<noteq> 0"
using assms
using SemanticsLoadData_NextWithGhostState
         [where auth=auth and a=a and l=l and 
                addrTrans="getTranslateAddrFunc s" and
                authCap="getCapReg auth s" and
                authAccessible="getRegisterIsAccessible auth s",
          THEN HoareTripleE[where s=s]]
unfolding AddressIsDataReadable_def 
unfolding getTranslateAddrFunc_def getTranslateAddresses_def
unfolding StateIsValid_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary LoadDataInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "LoadDataProp s lbl s'"
unfolding LoadDataProp_def
using assms SemanticsLoadData
by metis

(*<*)
end
(*>*)
