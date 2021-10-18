(*<*) 

(* Author: Kyndylan Nienhuis *)

theory LoadCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const LoadCapAction}\<close>

named_theorems SemanticsLoadCapI
  
method SemanticsLoadCap uses intro =
  HoareTriple intro: intro SemanticsLoadCapI[THEN HoareTriple_post_weakening]

declare nonExceptionCase_exceptions [SemanticsLoadCapI]

definition AddressIsCapReadable :: 
  "Capability \<Rightarrow> PhysicalCapAddress \<Rightarrow> 
   (VirtualAddress \<times> AccessType \<Rightarrow> PhysicalAddress option) \<Rightarrow> bool" 
where
  "AddressIsCapReadable authCap a addrTrans \<equiv>
   Permit_Load (getPerms authCap) \<and> 
   getTag authCap \<and>
   \<not> getSealed authCap \<and>
   (\<forall>a'\<in>Region (ExtendCapAddress a) 32. 
    \<exists>vAddr\<in>RegionOfCap authCap.
    addrTrans (vAddr, LOAD) = Some a')"

lemma AddressIsCapReadableI:
  assumes v_upper: "ucast vAddr + (32::65 word) \<le> 
                    ucast (getBase authCap) + ucast (getLength authCap)"
      and v_lower: "getBase authCap \<le> vAddr"
      and alignment: "isCapAligned vAddr"
      and pAddr: "getTranslateAddr (vAddr, LOAD) s = Some pAddr"
      and a: "a = GetCapAddress pAddr"
      and trans: "addrTrans = getTranslateAddrFunc s"
      and "Permit_Load (getPerms authCap)"
      and "getTag authCap"
      and "\<not> getSealed authCap"
  shows "AddressIsCapReadable authCap a addrTrans"
proof -
  have "(ucast vAddr::5 word) = 0"
    using alignment
    unfolding isCapAligned_def
    by simp
  have "(ucast pAddr::5 word) = 0"
    using arg_cong[where f="\<lambda>x. (ucast x::5 word)", 
                   OF getTranslateAddr_ucast12[OF pAddr]]
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
                   pAddr=pAddr and s=s and accessType=LOAD]
  show ?thesis
    using assms
    unfolding AddressIsCapReadable_def 
    unfolding getTranslateAddrFunc_def
    unfolding ExtendCapAddress_def GetCapAddress_def
    by (auto elim!: TranslateNearbyAddress_CapAligned2)
qed

definition SemanticsLoadCapPost where
  "SemanticsLoadCapPost authCap cap a cd addrTrans \<equiv> 
   return (AddressIsCapReadable authCap a addrTrans) \<and>\<^sub>b
   bind (read_state (getCAPR cd)) 
        (\<lambda>x. return (Permit_Load_Capability (getPerms authCap) \<and> x \<le> cap))"

lemma Commute_SemanticsLoadCapPost [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cd)) m"
  shows "Commute (SemanticsLoadCapPost authCap cap a cd addrTrans) m"
unfolding SemanticsLoadCapPost_def
by (Commute intro: assms)

lemma SemanticsLoadCapability_write'CAPR:
  shows "HoareTriple (return (cb = cd) \<and>\<^sub>b 
                  return (if cd = 0 then f nullCap else f cap))
                 (write'CAPR (cap, cb))
                 (\<lambda>_. bind (read_state (getCAPR cd)) (\<lambda>x. return (f x)))"
unfolding HoareTriple_def
by (auto simp: ValueAndStatePart_simp)

lemmas SemanticsLoadCapability_AddressTranslation =
  HoareTriple_DefinedAddressTranslation
    [where p="\<lambda>x. return (AddressIsCapReadable authCap a addrTrans \<and> extra) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCAPR cb)) \<and>\<^sub>b
                  bind (read_state (getMemCap (slice 5 x)))
                       (\<lambda>y. return (y \<le> cap))"]
  for a authCap cap addrTrans extra cb

lemma SemanticsLoadCapability_LoadCap:
  shows "HoareTriple (read_state getExceptionSignalled \<or>\<^sub>b
                  read_state isUnpredictable \<or>\<^sub>b
                  bind (read_state (getTranslateAddr (fst v, LOAD))) 
                       (\<lambda>z. case z of None \<Rightarrow> return True 
                                    | Some x \<Rightarrow> 
                             return (AddressIsCapReadable authCap a addrTrans \<and> extra) \<and>\<^sub>b 
                             (return authCap =\<^sub>b read_state (getCAPR cb)) \<and>\<^sub>b
                             bind (read_state (getMemCap (GetCapAddress x))) 
                                  (\<lambda>y. return (y \<le> cap))))
                 (LoadCap v)
                 (\<lambda>x. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      return (AddressIsCapReadable authCap a addrTrans \<and> extra) \<and>\<^sub>b
                      (return authCap =\<^sub>b read_state (getCAPR cb)) \<and>\<^sub>b
                      return (x \<le> cap))"
proof -
  note [SemanticsLoadCapI] = 
     SemanticsLoadCapability_AddressTranslation[where extra=extra]
  show ?thesis
    unfolding LoadCap_alt_def GetCapAddress_def
    by SemanticsLoadCap
qed

lemma SemanticsLoadCapability_CLC [SemanticsLoadCapI]:
  shows "HoareTriple ((return cap =\<^sub>b read_state (getMemCap a)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLCActions v) (\<lambda>prov. return (LoadCapAction auth a cd \<in> prov)))
                 (dfn'CLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsLoadCapPost authCap cap a cd addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadCapI] =
    SemanticsLoadCapability_LoadCap
      [where extra="(_ = cd) \<and> authAccessible \<and> 
                    Permit_Load_Capability (getPerms authCap)"]
  show ?thesis
    unfolding dfn'CLC_alt_def CLCActions_def
    unfolding CLCPhysicalAddress_def CLCVirtualAddress_def
    unfolding SemanticsLoadCapPost_def
    by (SemanticsLoadCap intro: SemanticsLoadCapability_write'CAPR)
       (auto simp: not_le not_less 
                   GetCapAddress_def ExtendCapAddress_def
             split: if_splits
             intro!: AddressIsCapReadableI)
qed

lemma SemanticsLoadCapability_CLLC [SemanticsLoadCapI]:
  shows "HoareTriple ((return cap =\<^sub>b read_state (getMemCap a)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CLLCActions v) (\<lambda>prov. return (LoadCapAction auth a cd \<in> prov)))
                 (dfn'CLLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsLoadCapPost authCap cap a cd addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadCapI] =
    SemanticsLoadCapability_LoadCap
      [where extra="(_ = cd) \<and> authAccessible \<and> 
                    Permit_Load_Capability (getPerms authCap)"]
  show ?thesis
    unfolding dfn'CLLC_alt_def CLLCActions_def
    unfolding CLLCPhysicalAddress_def CLLCVirtualAddress_def
    unfolding SemanticsLoadCapPost_def
    by (SemanticsLoadCap intro: SemanticsLoadCapability_write'CAPR)
       (auto simp: not_le not_less 
                   GetCapAddress_def ExtendCapAddress_def
             split: if_splits
             intro!: AddressIsCapReadableI)
qed

lemma SemanticsLoadCapability_Run_aux:
  shows "HoareTriple ((return cap =\<^sub>b read_state (getMemCap a)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (LoadCapAction auth a cd \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsLoadCapPost authCap cap a cd addrTrans \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def 
by (HoareTriple_cases;
    rule HoareTriple_pre_strengthening,
    rule SemanticsLoadCapability_CLC
         SemanticsLoadCapability_CLLC
         HoareTriple_weakest_pre_any,
    solves \<open>auto simp: ValueAndStatePart_simp\<close>)

lemmas SemanticsLoadCapability_Run =
  HoareTriple_weakest_pre_disj[OF SemanticsLoadCapability_Run_aux
                              UndefinedCase_Run]

lemma SemanticsLoadCapability_Fetch:
  fixes auth a a' cd authCap cap addrTrans cdAccessible authAccessible
  defines "p \<equiv> \<lambda>w. (return cap =\<^sub>b read_state (getMemCap a)) \<and>\<^sub>b
                    (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>prov. return (LoadCapAction auth a cd \<in> prov))"
  shows "HoareTriple (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro HoareTriple_Fetch) Commute+

lemma SemanticsLoadCapability_NextWithGhostState:
  shows "HoareTriple ((return cap =\<^sub>b read_state (getMemCap a)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return addrTrans =\<^sub>b read_state getTranslateAddrFunc) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>ac. return (LoadCapAction auth a cd \<in> ac)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsLoadCapPost authCap cap a cd addrTrans \<and>\<^sub>b
                      return authAccessible)"
proof -
  note [SemanticsLoadCapI] = 
    SemanticsLoadCapability_Run[where auth=auth and
                                      authAccessible=authAccessible]
  note [SemanticsLoadCapI] = 
    SemanticsLoadCapability_Fetch[where auth=auth and a=a and cd=cd and
                                        cap=cap and authCap=authCap and 
                                        addrTrans=addrTrans and
                                        authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (SemanticsLoadCap intro: UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsLoadCap:
  assumes prov: "LoadCapAction auth a cd \<in> actions"
      and suc: "(PreserveDomain actions, s') \<in> SemanticsCheriMips s"
  shows "Permit_Load (getPerms (getCapReg auth s))"
        "Permit_Load_Capability (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "Region (ExtendCapAddress a) 32 \<subseteq> 
         getTranslateAddresses (RegionOfCap (getCapReg auth s)) LOAD s"
        "getRegisterIsAccessible auth s"
        "getCAPR cd s' \<le> getMemCap a s"
using assms
using SemanticsLoadCapability_NextWithGhostState
         [where cap="getMemCap a s" and cd=cd and a=a and auth=auth and
                authCap="getCapReg auth s" and addrTrans="getTranslateAddrFunc s" and
                authAccessible="getRegisterIsAccessible auth s",
          THEN HoareTripleE[where s=s]]
unfolding SemanticsLoadCapPost_def
unfolding AddressIsCapReadable_def 
unfolding getTranslateAddrFunc_def getTranslateAddresses_def
unfolding SemanticsCheriMips_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary LoadCapInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "LoadCapProp s lbl s'"
unfolding LoadCapProp_def
using assms SemanticsLoadCap
by metis

(*<*)
end
(*>*)