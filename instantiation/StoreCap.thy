(*<*) 

(* Author: Kyndylan Nienhuis *)

theory StoreCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const StoreCapAction}}\<close>

named_theorems SemanticsStoreCapI
  
method SemanticsStoreCap uses intro =
  PrePost intro: intro SemanticsStoreCapI[THEN PrePost_post_weakening]

declare nonExceptionCase_exceptions [SemanticsStoreCapI]

definition AddressIsCapWritable :: 
  "Capability \<Rightarrow> Capability \<Rightarrow> PhysicalCapAddress \<Rightarrow> 
   (VirtualAddress \<times> AccessType \<Rightarrow> PhysicalAddress option) \<Rightarrow> bool" 
where
  "AddressIsCapWritable authCap cap a addrTrans \<equiv>
   Permit_Store (getPerms authCap) \<and> 
   Permit_Store_Capability (getPerms authCap) \<and> 
   getTag authCap \<and>
   \<not> getSealed authCap \<and>
   (getTag cap \<longrightarrow> \<not> Global (getPerms cap) \<longrightarrow> 
    Permit_Store_Local_Capability (getPerms authCap)) \<and>
   (\<forall>a'\<in>MemSegment (ExtendCapAddress a) 32. 
    \<exists>vAddr\<in>MemSegmentCap authCap.
    addrTrans (vAddr, STORE) = Some a')"

lemma AddressIsCapWritableI:
  assumes v_upper: "ucast vAddr + (32::65 word) \<le> 
                    ucast (getBase authCap) + ucast (getLength authCap)"
      and v_lower: "getBase authCap \<le> vAddr"
      and alignment: "isCapAligned vAddr"
      and pAddr: "getPhysicalAddress (vAddr, STORE) s = Some pAddr"
      and a: "a = GetCapAddress pAddr"
      and trans: "addrTrans = getPhysicalAddressFunc s"
      and "Permit_Store (getPerms authCap)"
      and "Permit_Store_Capability (getPerms authCap)"
      and "getTag authCap"
      and "\<not> getSealed authCap"
      and "getTag cap \<Longrightarrow>
           \<not> Global (getPerms cap) \<Longrightarrow>
           Permit_Store_Local_Capability (getPerms authCap)"
  shows "AddressIsCapWritable authCap cap a addrTrans"
proof -
  have "(ucast vAddr::5 word) = 0"
    using alignment
    unfolding isCapAligned_def
    by simp
  have "(ucast pAddr::5 word) = 0"
    using arg_cong[where f="\<lambda>x. (ucast x::5 word)", 
                   OF getPhysicalAddress_ucast12[OF pAddr]]
    using `(ucast vAddr::5 word) = 0`
    by simp
  hence [simp]: "pAddr AND mask 5 = 0"
    using eq_ucast_eq_and_mask[where x=pAddr and y=0 and n=5 and 'b=5]
    by simp    
  have [simp]: "pAddr AND NOT mask 5 = pAddr"
    unfolding word_minus_word_and_mask[THEN sym]
    by (simp del: word_minus_word_and_mask)
  note TranslateNearbyAddress_CapAligned2 = 
       TranslateNearbyAddress_CapAligned
            [where cap=authCap and vAddr=vAddr and 
                   pAddr=pAddr and s=s and accessType=STORE]
  show ?thesis
    using assms
    unfolding AddressIsCapWritable_def 
    unfolding getPhysicalAddressFunc_def
    unfolding ExtendCapAddress_def GetCapAddress_def
    by (auto elim!: TranslateNearbyAddress_CapAligned2)
qed

definition SemanticsStoreCapPost where
  "SemanticsStoreCapPost authCap cap a addrTrans \<equiv> 
   return (AddressIsCapWritable authCap cap a addrTrans) \<and>\<^sub>b
   (read_state (getMemCap a) =\<^sub>b return cap)"

lemma Commute_SemanticsStoreCapPost [Commute_compositeI]:
  assumes "Commute (read_state (getMemCap a)) m"
  shows "Commute (SemanticsStoreCapPost authCap cap a addrTrans) m"
unfolding SemanticsStoreCapPost_def
by (Commute intro: assms)

lemma SemanticsStoreCapability_WriteCap [SemanticsStoreCapI]:
  shows "PrePost (if fst v = a then return (snd v = cap)
                  else read_state (getMemCap a) =\<^sub>b return cap)
                 (WriteCap v) 
                 (\<lambda>_. read_state (getMemCap a) =\<^sub>b return cap)"
unfolding PrePost_def
by (cases v) (simp add: ValueAndStatePart_simp)

lemmas SemanticsStoreCapability_AddressTranslation =
  PrePost_DefinedAddressTranslation
    [where p="\<lambda>x. return (AddressIsCapWritable authCap cap a' addrTrans) \<and>\<^sub>b 
                  (bind (read_state getLLbit)
                   (\<lambda>y. if (slice 5 x = a) \<and> (cond \<longrightarrow> y = Some True)
                        then return (cap' = cap) 
                        else read_state (getMemCap a) =\<^sub>b return cap)) \<and>\<^sub>b
                  return extra"]
  for a a' cap cap' authCap addrTrans cond extra

lemma SemanticsStoreCapability_StoreCap:
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b 
                  read_state isUnpredictable \<or>\<^sub>b 
                  bind (read_state (getPhysicalAddress (vAddr', STORE)))
                       (\<lambda>x. case x of None \<Rightarrow> return True 
                                    | Some y \<Rightarrow> 
                                      return (AddressIsCapWritable authCap cap a addrTrans) \<and>\<^sub>b 
                                      (bind (read_state getLLbit)
                                            (\<lambda>z. if (slice 5 y = a) \<and> 
                                                     (cond \<longrightarrow> z = Some True)
                                                 then return (cap' = cap) 
                                                 else read_state (getMemCap a) =\<^sub>b return cap))) \<and>\<^sub>b
                  return authAccessible)
                 (StoreCap (vAddr', cap', cond))
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreCapPost authCap cap a addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreCapI] = 
     SemanticsStoreCapability_AddressTranslation
       [where cond=cond and cap'=cap' and a=a and extra=authAccessible]
  show ?thesis
    unfolding StoreCap_alt_def
    unfolding SemanticsStoreCapPost_def
    by (simp, SemanticsStoreCap) auto
qed

lemma SemanticsStoreCapability_CSC [SemanticsStoreCapI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CSCActions v) (\<lambda>prov. return (StoreCapAction auth cd a \<in> prov)))
                 (dfn'CSC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreCapPost authCap cap a addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreCapI] =
    SemanticsStoreCapability_StoreCap[where authAccessible=authAccessible]
  note TranslateNearbyAddress_CapAligned2 = 
    TranslateNearbyAddress_CapAligned
      [where pAddr="ExtendCapAddress a" and accessType=STORE]
  show ?thesis
    unfolding dfn'CSC_alt_def CSCActions_def
    unfolding CSCPhysicalAddress_def CSCVirtualAddress_def
    by SemanticsStoreCap
       (auto simp: not_le not_less 
                   GetCapAddress_def ExtendCapAddress_def
                   getPhysicalAddressFunc_def
             split: option.splits
             intro!: AddressIsCapWritableI)
qed

lemma SemanticsStoreCapability_CSCC [SemanticsStoreCapI]:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CSCCActions v) (\<lambda>prov. return (StoreCapAction auth cd a \<in> prov)))
                 (dfn'CSCC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreCapPost authCap cap a addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreCapI] =
    SemanticsStoreCapability_StoreCap[where authAccessible=authAccessible]
  show ?thesis
    unfolding dfn'CSCC_alt_def CSCCActions_def  
    unfolding CSCCPhysicalAddress_def CSCCVirtualAddress_def
    by SemanticsStoreCap
       (auto simp: not_le not_less if_distrib[where f="\<lambda>x. _ \<in> x"]
                   GetCapAddress_def ExtendCapAddress_def
                   getPhysicalAddressFunc_def
             split: option.splits if_splits
             intro!: AddressIsCapWritableI)
qed

lemma SemanticsStoreCapability_Run_aux:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (StoreCapAction auth cd a \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreCapPost authCap cap a addrTrans \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def 
by (PrePost_cases;
    rule PrePost_pre_strengthening,
    rule SemanticsStoreCapability_CSC
         SemanticsStoreCapability_CSCC
         PrePost_weakest_pre_any,
    solves \<open>auto simp: ValueAndStatePart_simp\<close>)

lemmas SemanticsStoreCapability_Run =
  PrePost_weakest_pre_disj[OF SemanticsStoreCapability_Run_aux
                              UndefinedCase_Run]

lemma SemanticsStoreCapability_Fetch:
  fixes auth a a' cd authCap cap addrTrans cdAccessible authAccessible
  defines "p \<equiv> \<lambda>w. (return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                    (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>ac. return (StoreCapAction auth cd a \<in> ac))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemma SemanticsStoreCapability_NextWithGhostState:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getPhysicalAddressFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>ac. return (StoreCapAction auth cd a \<in> ac)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsStoreCapPost authCap cap a addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsStoreCapI] = 
    SemanticsStoreCapability_Run[where auth=auth and
                                       authAccessible=authAccessible]
  note [SemanticsStoreCapI] = 
    SemanticsStoreCapability_Fetch[where auth=auth and a=a and cd=cd and
                                         cap=cap and authCap=authCap and 
                                         addrTrans=addrTrans and
                                         authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (SemanticsStoreCap intro: UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsStoreCap:
  assumes prov: "StoreCapAction auth cd a \<in> actions"
      and suc: "(KeepDomain actions, s') \<in> NextStates s"
  shows "Permit_Store (getPerms (getCapReg auth s))"
        "Permit_Store_Capability (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "getTag (getCAPR cd s) \<and> \<not> Global (getPerms (getCAPR cd s)) \<longrightarrow>
         Permit_Store_Local_Capability (getPerms (getCapReg auth s))"
        "MemSegment (ExtendCapAddress a) 32 \<subseteq> 
         getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s"
        "getRegisterIsAccessible auth s"
        "getMemCap a s' = getCAPR cd s"
using assms
using SemanticsStoreCapability_NextWithGhostState
         [where cap="getCAPR cd s" and cd=cd and a=a and auth=auth and
                authCap="getCapReg auth s" and 
                addrTrans="getPhysicalAddressFunc s" and
                authAccessible="getRegisterIsAccessible auth s",
          THEN PrePostE[where s=s]]
unfolding SemanticsStoreCapPost_def 
unfolding AddressIsCapWritable_def 
unfolding getPhysicalAddressFunc_def getPhysicalAddresses_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary StoreCapInstantiation [simp]:
  shows "StoreCapProp NextStates"
unfolding StoreCapProp_def
using SemanticsStoreCap
by metis

corollary StoreLocalCapInstantiation [simp]:
  shows "StoreLocalCapProp NextStates"
unfolding StoreLocalCapProp_def
using SemanticsStoreCap
by metis

(*<*)
end
(*>*)