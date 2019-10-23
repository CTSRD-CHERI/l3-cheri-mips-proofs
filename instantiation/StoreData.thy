(*<*) 

(* Author: Kyndylan Nienhuis *)

theory StoreData

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const StoreDataAction}}\<close>

named_theorems SemanticsStoreDataI
  
method SemanticsStoreData uses intro =
  PrePost intro: intro SemanticsStoreDataI[THEN PrePost_post_weakening]

declare nonExceptionCase_exceptions [SemanticsStoreDataI]

definition AddressIsDataWritable :: 
  "Capability \<Rightarrow> (VirtualAddress \<times> AccessType \<Rightarrow> PhysicalAddress option) \<Rightarrow> 
   PhysicalAddress \<Rightarrow> PhysicalAddress \<Rightarrow> bool" 
where
  "AddressIsDataWritable authCap addrTrans a l \<equiv>
   Permit_Store (getPerms authCap) \<and> 
   getTag authCap \<and>
   \<not> getSealed authCap \<and>
   l \<noteq> 0 \<and>
   (\<forall>a'\<in>MemSegment a l. 
    \<exists>vAddr\<in>MemSegmentCap authCap.
    addrTrans (vAddr, STORE) = Some a')"

definition SemanticsStoreDataPost where
  "SemanticsStoreDataPost authCap addrTrans a l cap  \<equiv> 
   bind (read_state (getMemCap (GetCapAddress a))) 
        (\<lambda>cap'. return (getTag cap' \<longrightarrow> cap' = cap)) \<and>\<^sub>b
   return (AddressIsDataWritable authCap addrTrans a l)"

lemma Commute_SemanticsStoreDataPost[Commute_compositeI]:
  assumes "Commute (read_state (getMemCap (GetCapAddress a))) m"
  shows "Commute (SemanticsStoreDataPost authCap addrTrans a l cap) m"
unfolding SemanticsStoreDataPost_def
by (Commute intro: assms)

lemma SemanticsStoreData_WriteData_aux:
  fixes a :: PhysicalAddress
  shows "PrePost (read_state (getMemCap (GetCapAddress a)) =\<^sub>b return cap)
                 (WriteData v)
                 (\<lambda>_. bind (read_state (getMemCap (GetCapAddress a))) 
                           (\<lambda>cap'. return (getTag cap' \<longrightarrow> cap' = cap)))"
unfolding WriteData_alt_def
by PrePost auto

lemma UndefinedCase_WriteData:
  shows "IsInvariant (read_state isUnpredictable) (WriteData v)"
by Invariant

lemma SemanticsStoreData_AdjustEndian_aux:
  shows "IsInvariant (read_state (getMemCap (GetCapAddress a)) =\<^sub>b return cap)
                     (AdjustEndian v)"
by PrePost

lemma SemanticsStoreData_StoreMemoryCap_unpred:
  shows "PrePost ((return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  return ((case v of (memType, accessLength, _, needAlign, vAddr, _) \<Rightarrow>
                           (needAlign \<and> memType = accessLength \<and> 
                            \<not> unat vAddr mod 8 + unat accessLength < 8) \<or>
                            (addrTrans (vAddr, STORE) = None))))
                 (StoreMemoryCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable)"
proof -
  note AdjustEndian_intro =
    PrePost_weakest_pre_disj[OF 
      ExceptionSignalled_AdjustEndian
      UndefinedCase_AdjustEndian]
  note intros = 
    AdjustEndian_intro 
    PrePost_DefinedAddressTranslation[where p="\<lambda>x. return False"]
  show ?thesis
    unfolding StoreMemoryCap_alt_def
    by (PrePost intro: intros[THEN PrePost_post_weakening])
       (auto simp: getPhysicalAddressFunc_def
             dest!: isAligned_max_length)
qed

lemma SemanticsStoreData_StoreMemoryCap_mem:
  fixes a' :: PhysicalAddress
  shows "PrePost (read_state (getMemCap (GetCapAddress a)) =\<^sub>b return cap)
                 (StoreMemoryCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b
                      bind (read_state (getMemCap (GetCapAddress a))) 
                           (\<lambda>cap'. return (getTag cap' \<longrightarrow> cap' = cap)))"
proof -
  note AdjustEndian_intro =
    PrePost_weakest_pre_disj[OF 
      SemanticsStoreData_AdjustEndian_aux[where a=a and cap=cap]
      PrePost_weakest_pre_disj[OF 
        UndefinedCase_AdjustEndian
        ExceptionSignalled_AdjustEndian]]
  note WriteData_intro =
    PrePost_weakest_pre_disj[OF 
      SemanticsStoreData_WriteData_aux[where a=a and cap=cap]
      PrePost_weakest_pre_disj[OF 
        UndefinedCase_WriteData
        ExceptionSignalled_WriteData]]
  note intros = 
    AdjustEndian_intro 
    WriteData_intro
    PrePost_DefinedAddressTranslation
      [where p="\<lambda>x. read_state (getMemCap (GetCapAddress a)) =\<^sub>b return cap"]
  show ?thesis
    unfolding StoreMemoryCap_alt_def
    by (PrePost intro: intros[THEN PrePost_post_weakening])
qed

lemmas SemanticsStoreData_StoreMemoryCap =
  PrePost_weakest_pre_disj[OF
    SemanticsStoreData_StoreMemoryCap_unpred[where addrTrans=addrTrans]
    PrePost_weakest_pre_conj[OF 
      SemanticsStoreData_StoreMemoryCap_mem[where cap=cap and a=a]
      IsInvariant_constant[where x="AddressIsDataWritable authCap addrTrans a l"]]]
  for cap authCap addrTrans a l

lemma SemanticsStoreData_StoreMemory_aux:
  shows "PrePost ((return authCap =\<^sub>b read_state getDDC) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  return ((case v of (memType, accessLength, needAlign, _, vAddr, _) \<Rightarrow>
                           (a = the (addrTrans (vAddr, STORE))) \<and>
                           (l = ucast accessLength + 1) \<and>
                           ((needAlign \<and> memType = accessLength) \<or> 
                            unat vAddr mod 8 + unat accessLength < 8))))
                 (StoreMemory v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemoryCap
      [where addrTrans=addrTrans and cap=cap and a=a and l=l and authCap=authCap]
  note TranslateNearbyAddress =
       TranslateNearbyAddress_LegacyInstructions[where pAddr=a]
  have [simp]: "ucast (x::3 word) \<noteq> (max_word::40 word)" (is "?l \<noteq> ?r") for x
    using test_bit_size[where w=x and n=4]
    by (auto simp: nth_ucast word_size dest!: test_bit_cong[where x=4])
  show ?thesis
    unfolding StoreMemory_alt_def 
    unfolding SemanticsStoreDataPost_def
    by SemanticsStoreData
       (auto simp: not_le not_less max_word_wrap_eq
                   getPhysicalAddressFunc_def
                   AddressIsDataWritable_def
             elim!: TranslateNearbyAddress)
qed

lemmas SemanticsStoreData_StoreMemory =
  PrePost_weakest_pre_conj[OF SemanticsStoreData_StoreMemory_aux
                              IsInvariant_constant[where x=authAccessible]]
  for authAccessible

lemma SemanticsStoreData_StoreCap:
  shows "PrePost ((return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  return ((case v of (vAddr, cap, cond) \<Rightarrow>
                           addrTrans (vAddr, STORE) = None)))
                 (StoreCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable)"
unfolding StoreCap_alt_def
by (PrePost intro: 
       PrePost_DefinedAddressTranslation
         [where p="\<lambda>x. return False", THEN PrePost_post_weakening])
   (auto simp: getPhysicalAddressFunc_def)

lemma SemanticsStoreAndRestrict_dfn'SB [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SBActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SB v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SB_alt_def SBActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def 
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SH [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SHActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SH v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SH_alt_def SHActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SW [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SWActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SW v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SW_alt_def SWActions_def storeWord_alt_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SD [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SDActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SD_alt_def SDActions_def storeDoubleword_alt_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SC [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SCActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SC_alt_def SCActions_def storeWord_alt_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SCD [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SCDActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SCD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SCD_alt_def SCDActions_def storeDoubleword_alt_def
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SWL [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SWLActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SWL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'SWL_alt_def SWLActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def 
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def
                   ucast_and ucast_not
                   unat_not unat_and_mask unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SWR [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SWRActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SWR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
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
    unfolding dfn'SWR_alt_def SWRActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def
                   ucast_and ucast_not
                   unat_not unat_and_mask unat_and_not_mask unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SDL [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SDLActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SDL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  have unat_mod_8_less: "unat x mod 8 < n" if "NOT ucast x = y" "unat (NOT y) < n"
  for x :: "64 word" and y :: "3 word" and n
    using arg_cong[where f=unat, OF that(1)] that(2)
    unfolding unat_not unat_ucast unat_and_mask unat_max_word
    by simp
  have unat_mod_8_zero: "unat x mod 8 = 0" if "NOT ucast x = y" "unat (NOT y) = 0"
  for x :: "64 word" and y :: "3 word"
    using unat_mod_8_less[where n=1] that
    by simp
  have not_ucast_mask_3: "(NOT ucast x::'a::len word) AND mask 3 = ucast y" if "NOT ucast x = y"
  for x :: "64 word" and y :: "3 word"
    using arg_cong[where f="ucast::3 word \<Rightarrow> 'a word", OF that]
    by (simp add: ucast_not word_bool_alg.conj_disj_distrib2)
  have word_3_exhaustive: "x = 7"
  if "x \<noteq> 6" "x \<noteq> 5" "x \<noteq> 4" "x \<noteq> 3" "x \<noteq> 2" "x \<noteq> 1" "x \<noteq> 0"
  for x :: "3 word"
    using exhaustive_3_word that by auto
  show ?thesis
    unfolding dfn'SDL_alt_def SDLActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def
                   unat_and_mask not_ucast_mask_3 numeral_2_eq_2
                   word_bool_alg.conj_disj_distrib2
             dest!: word_3_exhaustive
             elim!: unat_mod_8_less unat_mod_8_zero
             split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'SDR [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (SDRActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'SDR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_StoreMemory[where authAccessible=authAccessible]
  have [simp]: "x AND - 8 = x AND NOT mask 3" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  have [simp]: "7 - (NOT x) = x" for x :: "3 word"
    unfolding word_not_alt max_word_def
    by simp
  have ucast_mask_3: "(ucast x::40 word) AND mask 3 = ucast (NOT y)" if "NOT ucast x = y"
  for x :: "64 word" and y :: "3 word"
    using arg_cong[where f="\<lambda>x. ucast (NOT x)::40 word", OF that]
    by (simp add: word_bool_alg.conj_disj_distrib2 ucast_not)
  have [simp]: "(-1::3 word) = 7" "(-2::3 word) = 6" "(-3::3 word) = 5" "(-4::3 word) = 4"
               "(-5::3 word) = 3" "(-6::3 word) = 2" "(-7::3 word) = 1" "(-8::3 word) = 0" 
    by simp_all
  have [intro!]: "mask 3 = 7" 
    unfolding mask_def
    by auto
  show ?thesis
    unfolding dfn'SDR_alt_def SDRActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by SemanticsStoreData
       (auto simp: getPhysicalAddressFunc_def
                   unat_and_not_mask unat_and_mask mask_plus_one
                   word_bool_alg.conj_disj_distrib2
             dest!: ucast_mask_3
             split: option.splits)
qed

lemma SemanticsStoreAndRestrict_dfn'CStore [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CStoreActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'CStore v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] =
    PrePost_weakest_pre_disj[OF
      SemanticsStoreData_StoreMemoryCap_unpred[where addrTrans=addrTrans]
      PrePost_weakest_pre_conj[OF 
        SemanticsStoreData_StoreMemoryCap_mem[where cap=cap and a=a]
        IsInvariant_constant[where x="AddressIsDataWritable authCap addrTrans a l \<and> 
                                      authAccessible"]]]
  have "n mod 32 \<le> n mod 8 + 24" for n :: nat 
    proof -
      have "n mod 32 = (n mod 32 mod 8) + 8 * (n mod 32 div 8)"
        by simp
      also have "... \<le> (n mod 8) + 24"
        using mod_mod_cancel[where a=n and b=32 and c=8]
        by auto
      finally show ?thesis .
    qed
  hence *: "n mod 32 \<le> m" if "n mod 8 + 24 \<le> m" for m n :: nat
    by (rule order.trans[OF _ that])
  show ?thesis
    unfolding dfn'CStore_alt_def CStoreActions_def store_alt_def
    unfolding CStorePhysicalAddress_def CStoreVirtualAddress_def
    unfolding SemanticsStoreDataPost_def
    by SemanticsStoreData
       (cases rule: exhaustive_2_word[where x="case v of (_, _, _, _, t) \<Rightarrow> t"],
        auto simp: not_le not_less 
                   unat_mask unat_max_word
                   getPhysicalAddressFunc_def
                   AddressIsDataWritable_def
             intro!: *
             elim!: TranslateNearbyAddress[where accessLength=1]
                    TranslateNearbyAddress[where accessLength=2]
                    TranslateNearbyAddress[where accessLength=4]
                    TranslateNearbyAddress[where accessLength=8])
qed

lemma SemanticsStoreAndRestrict_dfn'CSCx [SemanticsStoreDataI]:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CSCxActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (dfn'CSCx v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] =
    PrePost_weakest_pre_disj[OF
      SemanticsStoreData_StoreMemoryCap_unpred[where addrTrans=addrTrans]
      PrePost_weakest_pre_conj[OF 
        SemanticsStoreData_StoreMemoryCap_mem[where cap=cap and a=a]
        IsInvariant_constant[where x="AddressIsDataWritable authCap addrTrans a l \<and> 
                                    authAccessible"]]]
  have "n mod 32 \<le> n mod 8 + 24" for n :: nat 
    proof -
      have "n mod 32 = (n mod 32 mod 8) + 8 * (n mod 32 div 8)"
        by simp
      also have "... \<le> (n mod 8) + 24"
        using mod_mod_cancel[where a=n and b=32 and c=8]
        by auto
      finally show ?thesis .
    qed
  hence *: "n mod 32 \<le> m" if "n mod 8 + 24 \<le> m" for m n :: nat
    by (rule order.trans[OF _ that])
  show ?thesis
    unfolding dfn'CSCx_alt_def CSCxActions_def store_alt_def
    unfolding CSCxPhysicalAddress_def CSCxVirtualAddress_def
    unfolding SemanticsStoreDataPost_def
    by SemanticsStoreData
       (cases rule: exhaustive_2_word[where x="case v of (_, _, _, t) \<Rightarrow> t"],
        auto simp: not_le not_less 
                   unat_mask unat_max_word
                   getPhysicalAddressFunc_def
                   AddressIsDataWritable_def
             intro!: *
             elim!: TranslateNearbyAddress[where accessLength=1]
                    TranslateNearbyAddress[where accessLength=2]
                    TranslateNearbyAddress[where accessLength=4]
                    TranslateNearbyAddress[where accessLength=8])
qed

lemma SemanticsStoreData_Run_aux:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (StoreDataAction auth a l \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def
by (PrePost_cases;
    rule PrePost_pre_strengthening,
    rule SemanticsStoreDataI
         PrePost_weakest_pre_any,
    solves \<open>auto simp: ValueAndStatePart_simp\<close>)

lemmas SemanticsStoreData_Run =
  PrePost_weakest_pre_disj[OF SemanticsStoreData_Run_aux
                              UndefinedCase_Run]

lemma SemanticsStoreData_Fetch:
  fixes auth a a' l authCap cap addrTrans authAccessible
  defines "p \<equiv> \<lambda>w. (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                    (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                    (read_state getCP0ConfigBE) \<and>\<^sub>b
                    (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>ac. return (StoreDataAction auth a l \<in> ac))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemma SemanticsStoreData_NextWithGhostState:
  shows "PrePost ((return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return cap =\<^sub>b read_state (getMemCap (GetCapAddress a))) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>ac. return (StoreDataAction auth a l \<in> ac)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreDataPost authCap addrTrans a l cap \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_Run[where auth=auth and a=a and l=l and
                                 authCap=authCap and cap=cap and
                                 addrTrans=addrTrans and
                                 authAccessible=authAccessible]
  note [SemanticsStoreDataI] = 
    SemanticsStoreData_Fetch[where auth=auth and a=a and l=l and
                                   authCap=authCap and cap=cap and
                                   addrTrans=addrTrans and
                                   authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (SemanticsStoreData intro: UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsStoreData:
  assumes prov: "StoreDataAction auth a l \<in> actions"
      and suc: "(KeepDomain actions, s') \<in> NextStates s"
      and valid: "getStateIsValid s"
  shows "Permit_Store (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "getRegisterIsAccessible auth s"
        "MemSegment a l \<subseteq> getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s"
        "getTag (getMemCap (GetCapAddress a) s') \<Longrightarrow>
         getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s"
        "l \<noteq> 0"
using assms
using SemanticsStoreData_NextWithGhostState
         [where auth=auth and a=a and l=l and 
                addrTrans="\<lambda>v. getPhysicalAddress v s" and
                authCap="getCapReg auth s" and
                cap="getMemCap (GetCapAddress a) s" and
                authAccessible="getRegisterIsAccessible auth s",
          THEN PrePostE[where s=s]]
unfolding SemanticsStoreDataPost_def AddressIsDataWritable_def 
unfolding getPhysicalAddressFunc_def getPhysicalAddresses_def
unfolding StateIsValid_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary StoreDataInstantiation [simp]:
  shows "StoreDataProp NextStates"
unfolding StoreDataProp_def
using SemanticsStoreData
by metis

(*<*)
end
(*>*)
