(*<*) 

(* Author: Kyndylan Nienhuis *)

theory TraceProperties

imports 
  "CHERI-abstraction.CheriAbstraction"
  "GeneralisedPermissions"
begin

(*>*)
section \<open>Trace based security properties\<close>

subsection \<open>Traces\<close>

type_synonym Trace = "AbstractStep list"

primrec IntraDomainTrace :: "Trace \<Rightarrow> bool" where
  "IntraDomainTrace [] = True" |
  "IntraDomainTrace (h # t) = (PreservesDomain h \<and> IntraDomainTrace t)"

lemma IntraDomainTraceE:
  assumes "IntraDomainTrace trace"
      and "step \<in> set trace"
  shows "PreservesDomain step"
using assms
by (induct trace) auto

primrec IsTrace :: "Semantics \<Rightarrow> state \<Rightarrow> Trace \<Rightarrow> state \<Rightarrow> bool" where
  "IsTrace sem s [] s' = (s = s')" 
| "IsTrace sem s (h # t) s' = (\<exists>x. IsTrace sem s t x \<and> (h, s') \<in> sem x)"

definition Traces :: "Semantics \<Rightarrow> state \<Rightarrow> (Trace \<times> state) set" where
  "Traces sem s = {(trace, s')| trace s'. IsTrace sem s trace s'}" 

lemma Traces_member_simp [simp]:
shows "(trace, s') \<in> Traces sem s = IsTrace sem s trace s'"
unfolding Traces_def 
by simp

subsection \<open>Transitively valid state\<close>

lemma TraceInvarianceStateIsValid:
  assumes abstraction: "CanBeSimulated sem"
      and valid: "getStateIsValid s"
      and trace: "(trace, s') \<in> Traces sem s"
  shows "getStateIsValid s'"
using trace
proof (induct trace arbitrary: s')
  case Nil
  thus ?case
    using valid by simp
next
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  show ?case
    using Cons(1)[OF r\<^sub>1]
    using CanBeSimulatedE_ValidState[OF abstraction r\<^sub>2]
    by auto
qed

subsection \<open>Transitively reachable capabilities\<close>

inductive_set
  ReachableCaps :: "state \<Rightarrow> Capability set" for s where

Reg:
  "\<lbrakk>RegisterIsAlwaysAccessible r;
    getTag (getCapReg r s)\<rbrakk> \<Longrightarrow> 
    getCapReg r s \<in> ReachableCaps s"

| Memory:
  "\<lbrakk>cap \<in> ReachableCaps s;
    \<not> getSealed cap;
    Permit_Load_Capability (getPerms cap);
    addr \<in> getPhysicalCapAddresses (RegionOfCap cap) LOAD s;
    getTag (getMemCap addr s)\<rbrakk> \<Longrightarrow> 
    getMemCap addr s \<in> ReachableCaps s"

| Restrict:
  "\<lbrakk>cap \<in> ReachableCaps s;
    cap' \<le> cap;
    getTag cap'\<rbrakk> \<Longrightarrow> 
    cap' \<in> ReachableCaps s"

| Seal:
  "\<lbrakk>cap \<in> ReachableCaps s;
    \<not> getSealed cap;
    sealer \<in> ReachableCaps s;
    \<not> getSealed sealer;
    Permit_Seal (getPerms sealer);
    ucast t \<in> RegionOfCap sealer\<rbrakk> \<Longrightarrow> 
    setType (setSealed (cap, True), t) \<in> ReachableCaps s"

| Unseal:
  "\<lbrakk>cap \<in> ReachableCaps s; 
    getSealed cap;
    unsealer \<in> ReachableCaps s;
    \<not> getSealed unsealer;
    Permit_Unseal (getPerms unsealer);
    ucast (getType cap) \<in> RegionOfCap unsealer\<rbrakk> \<Longrightarrow> 
    setType (setSealed (cap, False), 0) \<in> ReachableCaps s"

lemma ReachableCaps_getTag [elim!]:
  assumes "cap \<in> ReachableCaps s"
  shows "getTag cap"
using assms 
by (rule ReachableCaps.induct) auto

lemma ReachableCaps_PCC [intro!]:
  assumes "getTag (getPCC s)"
  shows "getPCC s \<in> ReachableCaps s"
using Reg[where r=RegPCC] assms
by auto

lemma ReachableCaps_BranchToPCC [intro!]:
  assumes "getTag (getBranchToPccCap s)"
  shows "getBranchToPccCap s \<in> ReachableCaps s"
using Reg[where r=RegBranchToPCC] assms
by auto

lemma ReachableCaps_BranchDelayPCC [intro!]:
  assumes tag: "getTag (getBranchDelayPccCap s)"
  shows "getBranchDelayPccCap s \<in> ReachableCaps s"
using Reg[where r=RegBranchDelayPCC]
using assms
by auto

lemma ReachableCaps_Capr [intro!]:
  assumes "getTag (getCAPR cd s)"
  shows "getCAPR cd s \<in> ReachableCaps s"
using Reg[where r="RegGeneral cd"]
using assms
by auto

lemma ReachableCaps_DDC [intro!]:
  assumes "getTag (getDDC s)"
  shows "getDDC s \<in> ReachableCaps s"
using Reg[where r="RegSpecial 0"]
using assms
by auto

lemma ReachableCaps_TLSC [intro!]:
  assumes "getTag (getTLSC s)"
  shows "getTLSC s \<in> ReachableCaps s"
using Reg[where r="RegSpecial 1"]
using assms
by auto

lemma ReachableCaps_SCapr [elim]:
  assumes abstraction: "CanBeSimulated sem"
      and suc: "(PreserveDomain actions, s') \<in> sem s"
      and action: "action \<in> actions"
      and reg: "cd \<in> CapDerivationRegisters action"
      and no_sys: "\<not> Access_System_Registers (getPerms (getPCC s))"
      and valid: "getStateIsValid s"
      and tag: "getTag (getSCAPR cd s)"
  shows "getSCAPR cd s \<in> ReachableCaps s"
proof -
  have "RegisterIsAlwaysAccessible (RegSpecial cd)"
    unfolding RegisterIsAlwaysAccessible_def
    using CanBeSimulatedE_SystemRegister[OF abstraction suc _ _ _ _ valid]
    using reg action no_sys
    by auto
  from Reg[OF this]
  show ?thesis
    using tag by auto
qed

lemma ReachableCaps_CapReg [elim]:
  assumes abstraction: "CanBeSimulated sem"
      and suc: "(PreserveDomain actions, s') \<in> sem s"
      and action: "action \<in> actions"
      and reg: "case r of RegSpecial cd \<Rightarrow> cd \<in> CapDerivationRegisters action | _ \<Rightarrow> True"
      and no_sys: "\<not> Access_System_Registers (getPerms (getPCC s))"
      and valid: "getStateIsValid s"
      and tag: "getTag (getCapReg r s)"
  shows "getCapReg r s \<in> ReachableCaps s"
using assms ReachableCaps_SCapr
by (cases r) auto

subsection \<open>Transitively usable capabilities\<close>

definition TransUsableCaps where
  "TransUsableCaps s \<equiv> {cap. cap \<in> ReachableCaps s \<and> \<not> getSealed cap}"

lemma TransUsableCapsI [intro]:
  assumes "cap \<in> ReachableCaps s"
      and "\<not> getSealed cap"
  shows "cap \<in> TransUsableCaps s"
using assms
unfolding TransUsableCaps_def
by simp

lemma TransUsableCapsE [elim!]:
  assumes "cap \<in> TransUsableCaps s"
  shows "getTag cap"
    and "\<not> getSealed cap"
    and "cap \<in> ReachableCaps s"
using assms
unfolding TransUsableCaps_def
by auto

lemma TransUsableCapsPcc [intro!]:
  assumes "getTag (getPCC s)"
      and "\<not> getSealed (getPCC s)"
  shows "getPCC s \<in> TransUsableCaps s"
using assms
by auto

subsection \<open>Transitively reachable permissions\<close>

definition ReachablePermissions :: "state \<Rightarrow> GeneralisedPerm" where
  "ReachablePermissions s \<equiv> GeneraliseOfCaps (TransUsableCaps s)"

lemma Generalise_ReachablePermissions_le [elim!]:
  assumes "cap \<in> TransUsableCaps s"
  shows "Generalise cap \<le> ReachablePermissions s"
unfolding ReachablePermissions_def GeneraliseOfCaps_def
using assms
by (intro Sup_upper) auto

lemma getPCC_ReachablePermissions_le [intro]:
  assumes "getTag (getPCC s)"
      and "\<not> getSealed (getPCC s)"
  shows "Generalise (getPCC s) \<le> ReachablePermissions s"
proof -
  have "getPCC s \<in> TransUsableCaps s"
    using assms
    by auto
  thus ?thesis by auto
qed

lemma ReachableCaps_ReachablePermissions_le [elim!]:
  assumes "ReachableCaps s \<subseteq> ReachableCaps s'"
  shows "ReachablePermissions s \<le> ReachablePermissions s'"
unfolding ReachablePermissions_def
using assms
by (intro GeneraliseOfCaps_subset) auto

lemma SystemRegisterAccess_PCC:
  assumes abstraction: "CanBeSimulated sem"
      and suc: "(label, s') \<in> sem s"
      and no_ex: "label \<noteq> SwitchDomain RaiseException" 
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "\<not> Access_System_Registers (getPerms (getPCC s))"
proof -
  have valid_pcc: "getTag (getPCC s)"  "\<not> getSealed (getPCC s)"
    using CanBeSimulatedE_Execute[OF abstraction suc no_ex valid]
    by auto
  hence "Generalise (getPCC s) \<le> ReachablePermissions s" 
    by auto
  from SystemRegisterAccess_le[OF this]
  show "\<not> Access_System_Registers (getPerms (getPCC s))"
    using no_sys valid_pcc
    by (auto simp: Generalise_accessors)
qed

lemma ReachablePermissions_AddressTranslation:
  assumes abstraction: "CanBeSimulated sem"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
      and suc: "(step, s') \<in> sem s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
  shows "getTranslateAddr a s' = getTranslateAddr a s"
proof -
  have valid_pcc: "getTag (getPCC s)"  "\<not> getSealed (getPCC s)"
    using CanBeSimulatedE_Execute[OF abstraction suc no_ex valid]
    by auto
  hence "Generalise (getPCC s) \<le> ReachablePermissions s" 
    by auto
  from SystemRegisterAccess_le[OF this]
  have "\<not> Access_System_Registers (getPerms (getPCC s))"
    using no_sys valid_pcc
    by (auto simp: Generalise_accessors)
  thus ?thesis
    using CanBeSimulatedE_AddressTranslation[OF abstraction suc no_ex _ valid]
    by auto
qed

subsection \<open>Readable capabilities\<close>

lemma ReadableCapsAreReachable [elim!]:
  assumes readable: "cap \<in> ReadableCaps (ReachablePermissions s) s"
  shows "cap \<in> ReachableCaps s"
proof -
  obtain loc where [simp]: "cap = getCap loc s"
               and loc: "loc \<in> ReadableLocations (ReachablePermissions s) s"
    using readable by auto
  have tag: "getTag cap"
    using readable by auto
  show ?thesis
    proof (cases loc)
      case (LocReg r)
      hence "RegisterIsAlwaysAccessible r"
        using loc by auto
      from Reg[OF this]
      show ?thesis
        using tag LocReg
        by auto
    next
      case (LocMem a)
      thus ?thesis
        using Memory[where addr=a and s=s]
        using LocMem tag loc
        unfolding ReachablePermissions_def TransUsableCaps_def
        by (auto simp: getPhysicalCapAddresses_distrib_Union Generalise_accessors
                 split: if_splits)
    qed
qed

definition InvokableCapsNotUnsealable :: "GeneralisedPerm \<Rightarrow> state \<Rightarrow> bool" where
  "InvokableCapsNotUnsealable perm s \<equiv>
   \<forall>cap\<in>ReadableCaps perm s.
   Permit_CCall (getPerms cap) \<longrightarrow>
   getSealed cap \<and>
   getType cap \<notin> UnsealableTypes perm"

lemma InvokableCapsNotUnsealableE [elim]:
  assumes "InvokableCapsNotUnsealable perm s"
      and "cap \<in> ReadableCaps perm s"
      and "Permit_CCall (getPerms cap)"
  shows "getSealed cap"
    and "getType cap \<notin> UnsealableTypes perm"
using assms
unfolding InvokableCapsNotUnsealable_def
by auto

lemma InvokableCapsNotUnsealable_le:
  assumes "p \<le> q"
      and "InvokableCapsNotUnsealable q s"
  shows "InvokableCapsNotUnsealable p s"
using assms(2) 
using ReadableCaps_le[OF assms(1)]
using UnsealableTypes_le[OF assms(1)]
unfolding InvokableCapsNotUnsealable_def
by auto

lemma ReachableInvokableCapsAreReadable:
  assumes reachable: "cap \<in> ReachableCaps s"
      and ccall: "Permit_CCall (getPerms cap)"
      and base: "InvokableCapsNotUnsealable (ReachablePermissions s) s"
  shows "cap \<in> ReadableCaps (ReachablePermissions s) s"
proof -
  have "cap \<in> ReadableCaps (ReachablePermissions s) s \<and>
        getSealed cap \<and> 
        getType cap \<notin> UnsealableTypes (ReachablePermissions s)"
    using reachable ccall
    proof induct
      case (Reg r)
      hence "getCapReg r s \<in> ReadableCaps (ReachablePermissions s) s"
        using Reg
        by (auto intro: ReadableCapsI[where loc="LocReg r"])
      thus ?case
        using Reg
        using InvokableCapsNotUnsealableE[OF base, where cap="getCapReg r s"]
        by auto
    next
      case (Memory cap addr)
      hence "cap \<in> TransUsableCaps s"
        by auto
      note gperm = Generalise_ReachablePermissions_le[OF this]
      have "addr \<in> getPhysicalCapAddresses (CapLoadableAddresses (Generalise cap)) LOAD s"
        using Memory ReachableCaps_getTag
        by (auto simp: Generalise_accessors)
      hence "addr \<in> getPhysicalCapAddresses (CapLoadableAddresses (ReachablePermissions s)) LOAD s"
        using getPhysicalCapAddresses_le[OF CapLoadableAddresses_le[OF gperm]]
        by auto
      hence "getMemCap addr s \<in> ReadableCaps (ReachablePermissions s) s"
        using Memory
        by (auto intro: ReadableCapsI[where loc="LocMem addr"])
      thus ?case
        using Memory
        using InvokableCapsNotUnsealableE[OF base, where cap="getMemCap addr s"]
        by auto
    next
      case (Restrict cap cap')
      hence "getPerms cap' \<le> getPerms cap"
        using less_eq_CapabilityE_getPerms
        by auto
      hence "Permit_CCall (getPerms cap)"
        unfolding less_eq_Perms_ext_alt
        using Restrict
        by auto
      hence "getSealed cap"
        using Restrict by auto
      hence "getSealed cap'"
        using less_eq_CapabilityE_getSealed
        using Restrict by auto
      hence "cap' = cap"
        using less_eq_CapabilityE_IsSealed
        using Restrict by auto
      thus ?case 
        using Restrict
        by auto
    next
      case (Seal cap sealer t)
      thus ?case by auto
    next
      case (Unseal cap unsealer)
      hence "unsealer \<in> TransUsableCaps s"
        by auto
      note gperm = Generalise_ReachablePermissions_le[OF this]
      have "getType cap \<in> UnsealableTypes (Generalise unsealer)"
        using Unseal
        by (auto simp: Generalise_accessors)
      hence False
        using UnsealableTypes_le[OF gperm]
        using Unseal
        by auto
      thus ?case by simp
    qed
  thus ?thesis
    by auto
qed

subsection \<open>Closed permissions\<close>

definition PermIsClosed where
  "PermIsClosed perm s \<equiv>
   \<forall>cap\<in>ReadableCaps perm s.
   (\<not> getSealed cap \<or> getType cap \<in> UnsealableTypes perm) \<longrightarrow>
   Generalise cap \<le> perm"

lemma PermIsClosedE [elim]:
  assumes "PermIsClosed perm s"
      and "cap \<in> ReadableCaps perm s"
      and "getSealed cap \<Longrightarrow> getType cap \<in> UnsealableTypes perm"
  shows "Generalise cap \<le> perm"
using assms
unfolding PermIsClosed_def
by auto

lemma TransUsableCapsInClosedPerm:
  assumes closed: "PermIsClosed perm s"
      and usable: "cap \<in> TransUsableCaps s"
  shows "Generalise cap \<le> perm"
proof -
  have reachable: "cap \<in> ReachableCaps s" and
       type: "getSealed cap \<longrightarrow> getType cap \<in> UnsealableTypes perm"
    using usable
    unfolding TransUsableCaps_def
    by auto
  thus ?thesis
    proof induct
      case (Reg r)
      hence "LocReg r \<in> ReadableLocations perm s" 
        by auto
      thus ?case
        using Reg 
        using PermIsClosedE[OF closed, OF ReadableCapsI[where loc="LocReg r"]]
        by auto
    next
      case (Memory cap addr)
      hence "Generalise cap \<le> perm"
        by auto
      from CapLoadableAddresses_le[OF this]
      have "CapLoadableAddresses (Generalise cap) \<subseteq> CapLoadableAddresses perm"
        by auto
      from getPhysicalCapAddresses_le[OF this]
      have "addr \<in> getPhysicalCapAddresses (CapLoadableAddresses perm) LOAD s"
        using Memory ReachableCaps_getTag
        by (auto simp: Generalise_accessors)
      hence "LocMem addr \<in> ReadableLocations perm s" 
        by auto
      thus ?case
        using Memory 
        using PermIsClosedE[OF closed, OF ReadableCapsI[where loc="LocMem addr"]]
        by auto
    next
      case (Restrict cap cap')
      hence "Generalise cap' \<le> Generalise cap"
        by auto
      thus ?case 
        using less_eq_CapabilityE_getSealed[OF `cap' \<le> cap`]
        using less_eq_CapabilityE_getType[OF `cap' \<le> cap`]
        using Restrict 
        by auto
    next
      case (Seal cap sealer t)
      thus ?case by simp
    next
      case (Unseal cap unsealer)
      hence "Generalise unsealer \<le> perm" 
        by auto
      from UnsealableTypes_le[OF this]
      have "getType cap \<in> UnsealableTypes perm"
        using Unseal 
        by (auto simp: Generalise_accessors)
      thus ?case 
        using Unseal by auto
    qed
qed

lemma ReachablePermissionsInClosedPerm:
  assumes "PermIsClosed perm s"
  shows "ReachablePermissions s \<le> perm"
using TransUsableCapsInClosedPerm[OF assms]
unfolding ReachablePermissions_def GeneraliseOfCaps_def TransUsableCaps_def
unfolding Sup_le_iff
by auto

subsection \<open>Monotonicity of reachable capabilities\<close>

lemma NewCapsAreReachable:
  assumes abstraction: "CanBeSimulated sem"
      and suc: "(PreserveDomain actions, s') \<in> sem s"
      and no_sys: "\<not> Access_System_Registers (getPerms (getPCC s))"
      and valid: "getStateIsValid s"
      and tag: "getTag (getCap loc s')"
  shows "getCap loc s' \<in> ReachableCaps s \<or>
         getCap loc s' = getCap loc s"
proof -
  obtain parentLoc where "parentLoc \<in> ProvenanceParents actions loc"
    using ProvenanceParentExists by auto
  thus ?thesis
    proof (cases rule: ProvenanceCases)
      case Unchanged
      hence "getCap loc s' = getCap loc s"
        using CanBeSimulatedE_CapabilityInvariant[OF abstraction suc _ _ valid]
        by simp
      thus ?thesis by auto
    next
      case (StoreData auth a l)
      hence "getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s"
        using CanBeSimulatedE_StoreData[OF abstraction suc _ StoreData(1) valid]
        using tag
        by auto
      thus ?thesis
        using StoreData
        by auto
    next
      case (RestrictedReg r r')
      have le: "getCapReg r' s' \<le> getCapReg r s"
        using RestrictedReg
        using CanBeSimulatedE_RestrictRegCap[OF abstraction suc _ RestrictedReg(1) valid]
        by auto
      have tag_original: "getTag (getCapReg r s)"
        using le tag RestrictedReg by auto
      have "getCapReg r s \<in> ReachableCaps s"
        using ReachableCaps_CapReg[OF abstraction suc RestrictedReg(1) _ no_sys valid tag_original]
        by (cases r) auto
      from ReachableCaps.Restrict[OF this le]
      show ?thesis
        using RestrictedReg tag
        by auto
    next
      case (Loaded auth a cd)
      have "LoadCapProp s (PreserveDomain actions) s'"
        using CanBeSimulatedE[OF abstraction suc]
        by auto
      from LoadCapPropE_mem[OF this _ Loaded(1) valid, where a'="ExtendCapAddress a"]
      obtain vAddr where "vAddr \<in> RegionOfCap (getCapReg auth s)" 
                         "getTranslateAddr (vAddr, LOAD) s = Some (ExtendCapAddress a)"
        by auto
      hence le: "getCAPR cd s' \<le> getMemCap a s"
      and tag_auth: "getTag (getCapReg auth s)"
      and segment: "a \<in> getPhysicalCapAddresses (RegionOfCap (getCapReg auth s)) LOAD s"
      and unsealed: "\<not> getSealed (getCapReg auth s)"
      and perm: "Permit_Load_Capability (getPerms (getCapReg auth s))"
        using CanBeSimulatedE_LoadCap[OF abstraction suc _ Loaded(1) valid]
        by auto
      have auth: "getCapReg auth s \<in> ReachableCaps s"
        using ReachableCaps_CapReg[OF abstraction suc Loaded(1) _ no_sys valid tag_auth]
        by (cases auth) auto
      hence "getTag (getMemCap a s)"
        using le tag Loaded by auto
      hence "getMemCap a s \<in> ReachableCaps s"
        using Memory[OF auth unsealed perm segment]
        by auto
      from ReachableCaps.Restrict[OF this le]
      show ?thesis 
        using Loaded tag
        by auto
    next
      case (Stored auth cd a)
      have le: "getMemCap a s' \<le> getCAPR cd s"
        using CanBeSimulatedE_StoreCap[OF abstraction suc _ Stored(1) valid]
        by auto
      hence "getTag (getCAPR cd s)"
        using tag Stored by auto
      note ReachableCaps_Capr[OF this]
      from ReachableCaps.Restrict[OF this le]
      show ?thesis 
        using Stored tag
        by auto
    next
      case (Sealed auth cd cd')
      define t :: ObjectType where 
        "t \<equiv> ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s))"
      have tag_cd: "getTag (getCAPR cd s)" 
      and tag_auth: "getTag (getCapReg auth s)"
        using CanBeSimulatedE_SealCap[OF abstraction suc _ Sealed(1) valid]
        using tag Sealed
        by auto
      have "getCapReg auth s \<in> ReachableCaps s"
        using ReachableCaps_CapReg[OF abstraction suc Sealed(1) _ no_sys valid tag_auth]
        by (cases auth) auto
      hence "setType (setSealed (getCAPR cd s, True), t) \<in> ReachableCaps s"
        using CanBeSimulatedE_SealCap[OF abstraction suc _ Sealed(1) valid]
        using tag_cd
        unfolding t_def
        by (intro ReachableCaps.Seal[where sealer="getCapReg auth s"]) auto
      thus ?thesis
        using CanBeSimulatedE_SealCap[OF abstraction suc _ Sealed(1) valid]
        using Sealed 
        unfolding t_def
        by auto
    next
      case (Unsealed auth cd cd')
      have tag_cd: "getTag (getCAPR cd s)"
      and tag_auth: "getTag (getCapReg auth s)"
        using TagOfGreaterCap[OF _ tag, where cap'="setType (setSealed (getCAPR cd s, False), 0)"]
        using CanBeSimulatedE_UnsealCap[OF abstraction suc _ Unsealed(1) valid]
        using Unsealed
        by auto
      have "getCapReg auth s \<in> ReachableCaps s"
        using ReachableCaps_CapReg[OF abstraction suc Unsealed(1) _ no_sys valid tag_auth]
        by (cases auth) auto
      hence "setType (setSealed (getCAPR cd s, False), 0) \<in> ReachableCaps s"
        using CanBeSimulatedE_UnsealCap[OF abstraction suc _ Unsealed(1) valid]
        using tag_cd
        by (intro ReachableCaps.Unseal[where unsealer="getCapReg auth s"]) auto
      from ReachableCaps.Restrict[OF this _ tag]
      show ?thesis
        using CanBeSimulatedE_UnsealCap[OF abstraction suc _ Unsealed(1) valid]
        using Unsealed
        by auto
    qed
qed

lemma MonotonicityReachableCaps_Step:
  assumes abstraction: "CanBeSimulated sem"
      and suc: "(PreserveDomain actions, s') \<in> sem s"
      and no_sys: "\<not> Access_System_Registers (getPerms (getPCC s))"
      and valid: "getStateIsValid s"
  shows "ReachableCaps s' \<subseteq> ReachableCaps s"
proof 
  fix cap
  assume "cap \<in> ReachableCaps s'"
  thus "cap \<in> ReachableCaps s"
    proof (induct rule: ReachableCaps.inducts)
      case (Reg r)
      thus ?case
        using NewCapsAreReachable[OF abstraction suc no_sys valid, where loc="LocReg r"]
        using Reg ReachableCaps.Reg
        by auto
    next
      case (Memory cap' a)
      have "getTranslateAddr (v, LOAD) s' = getTranslateAddr (v, LOAD) s" for v
        using CanBeSimulatedE_AddressTranslation[OF abstraction suc _ no_sys valid]
        by auto
      hence "getPhysicalCapAddresses addrs LOAD s' = getPhysicalCapAddresses addrs LOAD s" for addrs
        unfolding getPhysicalCapAddresses_def
        unfolding getTranslateAddresses_def
        by simp
      thus ?case 
        using NewCapsAreReachable[OF abstraction suc no_sys valid, where loc="LocMem a"]
        using Memory ReachableCaps.Memory
        by auto
    next
      case Restrict
      thus ?case
        using ReachableCaps.Restrict
        by auto
    next
      case Seal
      thus ?case
        using ReachableCaps.Seal
        by auto
    next
      case Unseal
      thus ?case 
        using ReachableCaps.Unseal
        by auto
    qed
qed

theorem MonotonicityReachableCaps:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "ReachableCaps s' \<subseteq> ReachableCaps s"
using trace intra
proof (induct trace arbitrary: s')
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  have ih: "ReachableCaps r \<subseteq> ReachableCaps s" 
    using Cons(1)[OF r\<^sub>1]
    using Cons(3)
    by simp
  have intra: "PreservesDomain step"
    using Cons(3) by auto
  hence no_ex: "step \<noteq> SwitchDomain RaiseException" 
    by auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have no_sys2: "\<not> SystemRegisterAccess (ReachablePermissions r)"
    using ReachableCaps_ReachablePermissions_le[OF ih]
    using SystemRegisterAccess_le no_sys 
    by auto
  have "\<not> Access_System_Registers (getPerms (getPCC r))"
    using SystemRegisterAccess_PCC[OF abstraction r\<^sub>2 no_ex no_sys2 valid2]
    by auto
  hence "ReachableCaps s' \<subseteq> ReachableCaps r"
    using MonotonicityReachableCaps_Step[OF abstraction _ _ valid2, where s'=s']
    using r\<^sub>2 intra
    by (cases step) auto
  thus ?case
    using ih by simp
qed simp

corollary MonotonicityTransUsableCaps:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "TransUsableCaps s' \<subseteq> TransUsableCaps s"
using MonotonicityReachableCaps[OF abstraction trace intra no_sys valid]
by auto

corollary MonotonicityReachablePermissions:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "ReachablePermissions s' \<le> ReachablePermissions s"
using MonotonicityTransUsableCaps[OF abstraction trace intra no_sys valid]
unfolding ReachablePermissions_def
by auto

subsection \<open>Invariance of address translation\<close>

lemma TraceInvarianceAddressTranslation:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "getTranslateAddr addr s' = getTranslateAddr addr s"
using trace intra
proof (induct trace arbitrary: s')
  case Nil
  thus ?case by simp
next
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  have intra2: "IntraDomainTrace trace"
    using Cons by auto
  hence ih: "getTranslateAddr addr r = getTranslateAddr addr s"
    using Cons(1)[OF r\<^sub>1] 
    by auto
  have no_ex: "step \<noteq> SwitchDomain RaiseException"
    using Cons by auto
  note MonotonicityReachablePermissions[OF abstraction r\<^sub>1 intra2 no_sys valid]
  from SystemRegisterAccess_le[OF this]
  have no_sys2: "\<not> SystemRegisterAccess (ReachablePermissions r)"
    using no_sys
    by auto
  thus ?case
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    using ReachablePermissions_AddressTranslation[OF abstraction _ _ r\<^sub>2 no_ex]
    using ih
    by auto
qed

subsection \<open>Invariance of system registers\<close>

lemma SystemRegisterInvariant_aux:
  assumes abstraction: "CanBeSimulated sem"
      and no_access: "\<not> Access_System_Registers (getPerms (getPCC s))"
      and system: "cd \<noteq> 0" "cd \<noteq> 1"
      and valid: "getStateIsValid s"
      and suc: "(step, s') \<in> sem s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
  shows "getSCAPR cd s' = getSCAPR cd s"
proof (cases "PreservesDomain step")
  case False
  then obtain crossing where "step = SwitchDomain crossing"
    by (cases step) auto
  then obtain cd cd' where "step = SwitchDomain (InvokeCapability cd cd')"
    using no_ex
    by (cases crossing) auto
  hence "(SwitchDomain (InvokeCapability cd cd'), s') \<in> sem s"
    using suc by auto
  from CanBeSimulatedE_InvokeCap[OF abstraction this _ valid]
  show ?thesis
    by auto
next
  case True
  then obtain actions where "step = PreserveDomain actions"
    by (cases step) auto
  hence intra_suc: "(PreserveDomain actions, s') \<in> sem s"
    using suc
    by auto
  have "cd \<notin> \<Union> (CapDerivationRegisters ` actions)"
    using CanBeSimulatedE_SystemRegister[OF abstraction intra_suc _ _ system  valid]
    using no_access
    by auto
  hence "\<And>prov. prov \<in> actions \<Longrightarrow> LocReg (RegSpecial cd) \<notin> CapDerivationTargets prov"
    unfolding CapDerivationRegisters_def
    by auto
  from CanBeSimulatedE_CapabilityInvariant
       [OF abstraction intra_suc _ this valid]
  show ?thesis by auto
qed

lemma SystemRegisterInvariant_intra:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_access: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and system: "cd \<noteq> 0" "cd \<noteq> 1"
      and valid: "getStateIsValid s"
  shows "getSCAPR cd s' = getSCAPR cd s"
using trace intra
proof (induct trace arbitrary: s')
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  have ih: "getSCAPR cd r = getSCAPR cd s"
    using Cons(1)[OF r\<^sub>1] Cons(3)
    by auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have no_ex2: "step \<noteq> SwitchDomain RaiseException"
    using Cons(3)
    by auto
  have "ReachablePermissions r \<le> ReachablePermissions s"
    using MonotonicityReachablePermissions[OF abstraction r\<^sub>1 _ no_access valid]
    using Cons(3)
    by auto
  from SystemRegisterAccess_le[OF this]
  have no_access2: "\<not> SystemRegisterAccess (ReachablePermissions r)"
    using no_access by auto
  note pcc = CanBeSimulatedE_Execute[OF abstraction r\<^sub>2 no_ex2 valid2]
  hence "getPCC r \<in> TransUsableCaps r"
    by auto
  hence "Generalise (getPCC r) \<le> ReachablePermissions r"
    by auto
  from SystemRegisterAccess_le[OF this]
  have "\<not> SystemRegisterAccess (Generalise (getPCC r))"
    using no_access2 by auto
  hence "\<not> Access_System_Registers (getPerms (getPCC r))"
    using pcc
    by (auto simp: Generalise_accessors)
  hence "getSCAPR cd s' = getSCAPR cd r" 
    using SystemRegisterInvariant_aux[OF abstraction _ system valid2 r\<^sub>2 no_ex2]
    by auto
  thus ?case
    using ih by auto
qed simp

theorem SystemRegisterInvariant:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(step # trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and inter: "\<not> PreservesDomain step"
      and no_access: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and system: "cd \<noteq> 0" "cd \<noteq> 1" 
      and non_eppc: "cd \<noteq> 31"
      and valid: "getStateIsValid s"
  shows "getSCAPR cd s' = getSCAPR cd s"
proof -
  obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
             and r\<^sub>2: "(step, s') \<in> sem r"
    using trace by auto
  obtain crossing where step: "step = SwitchDomain crossing"
    using inter by (cases step) auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have "getSCAPR cd s' = getSCAPR cd r"
    proof (cases crossing)
      case RaiseException
      hence "(SwitchDomain RaiseException, s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_Exception[OF abstraction this _ valid2]
      have "getSCAPR cd s' = SignalExceptionSCAPR cd r"
        by auto
      thus ?thesis
        unfolding SignalExceptionSCAPR_def
        using non_eppc
        by auto
    next
      case (InvokeCapability cd cd')
      hence "(SwitchDomain (InvokeCapability cd cd'), s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_InvokeCap[OF abstraction this _ valid2]
      show ?thesis by auto
    qed
  have "getSCAPR cd r = getSCAPR cd s"
    using SystemRegisterInvariant_intra[OF abstraction r\<^sub>1 intra no_access system valid]
    by simp
  thus ?thesis
    using `getSCAPR cd s' = getSCAPR cd r`
    by auto
qed

subsection \<open>Invariance of capabilities in memory\<close>

lemma MemCapInvariant_intra:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_access: "a \<notin> StorablePhysCapAddresses (ReachablePermissions s) s"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "getMemCap a s' = getMemCap a s"
using trace intra
proof (induct trace arbitrary: s')
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  have intra2: "IntraDomainTrace trace"
    using Cons by auto
  have ih: "getMemCap a r = getMemCap a s"
    using Cons(1)[OF r\<^sub>1] intra2
    by auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have no_ex2: "step \<noteq> SwitchDomain RaiseException"
    using Cons(3)
    by auto
  have perms: "ReachablePermissions r \<le> ReachablePermissions s"
    using MonotonicityReachablePermissions[OF abstraction r\<^sub>1 intra2 no_sys valid]
    by auto
  from SystemRegisterAccess_le[OF this]
  have no_sys2: "\<not> SystemRegisterAccess (ReachablePermissions r)"
    using no_sys by auto
  have no_sys_pcc: "\<not> Access_System_Registers (getPerms (getPCC r))"
    using SystemRegisterAccess_PCC[OF abstraction r\<^sub>2 no_ex2 no_sys2 valid2]
    by auto
  have addrTrans: "getTranslateAddr a r = getTranslateAddr a s" for a
    using TraceInvarianceAddressTranslation[OF abstraction r\<^sub>1 intra2 no_sys valid]
    by auto
  from StorablePhysCapAddresses_le[OF perms]
  have no_access2: "a \<notin> StorablePhysCapAddresses (ReachablePermissions r) r"
    using getPhysicalCapAddresses_eqI_getTranslateAddr[OF addrTrans]
    using no_access
    unfolding StorablePhysCapAddresses_def
    by auto
  hence "getMemCap a s' = getMemCap a r"
    proof -
      obtain actions where "step = PreserveDomain actions"
        using Cons(3)
        by (cases step) auto
      hence intra_suc: "(PreserveDomain actions, s') \<in> sem r"
        using r\<^sub>2
        by auto
      have "\<not> (\<exists>action. action \<in> actions \<and>
                        LocMem a \<in> CapDerivationTargets action)" 
        proof (clarify)
          fix action
          assume action: "action \<in> actions" 
             and target: "LocMem a \<in> CapDerivationTargets action"
          thus False
            proof (cases action)
              case (StoreDataAction auth a' l)
              hence "StoreDataAction auth a' l \<in> actions"
                using action 
                by auto
              note restrict = 
                   CanBeSimulatedE_StoreData[OF abstraction intra_suc _ this valid2]
              have a: "a = GetCapAddress a'"
                using target StoreDataAction
                by auto
              have "getCapReg auth r \<in> ReachableCaps r"
                using ReachableCaps_CapReg
                      [OF abstraction intra_suc action _ no_sys_pcc valid2, where r=auth]
                using restrict StoreDataAction
                by (cases auth) auto
              hence "getCapReg auth r \<in> TransUsableCaps r"
                using restrict 
                by auto
              hence gperm: "Generalise (getCapReg auth r) \<le> ReachablePermissions r"
                by auto
              have "StoreDataProp r (PreserveDomain actions) s'"
                using CanBeSimulatedE[OF abstraction intra_suc]
                by auto
              from StoreDataPropE_mem
                   [OF this _ _ valid2, 
                    where a=a' and a'=a' and auth=auth and l=l and actions=actions]
              obtain vAddr where "vAddr \<in> RegionOfCap (getCapReg auth r)" 
                                 "getTranslateAddr (vAddr, STORE) r = Some a'"
                using action StoreDataAction target restrict
                by auto
              hence "a \<in> getPhysicalCapAddresses (StorableAddresses (Generalise (getCapReg auth r))) STORE r"
                using a restrict
                by (auto simp: Generalise_accessors 
                         intro: getPhysicalCapAddressesI)
              hence "a \<in> getPhysicalCapAddresses (StorableAddresses (ReachablePermissions r)) STORE r"
                using getPhysicalCapAddresses_le[OF StorableAddresses_le[OF gperm]]
                by auto
              thus False
                using no_access2
                unfolding StorablePhysCapAddresses_def Let_def
                unfolding getPhysicalCapAddresses_distrib_union
                by simp
            next
              case (StoreCapAction auth cd a')
              hence "StoreCapAction auth cd a \<in> actions"
                using action target
                by auto
              note store = CanBeSimulatedE_StoreCap[OF abstraction intra_suc _ this valid2]
              have "getCapReg auth r \<in> ReachableCaps r"
                using ReachableCaps_CapReg
                      [OF abstraction intra_suc action _ no_sys_pcc valid2, where r=auth]
                using store StoreCapAction
                by (cases auth) auto
              hence "getCapReg auth r \<in> TransUsableCaps r"
                using store 
                by auto
              hence gperm: "Generalise (getCapReg auth r) \<le> ReachablePermissions r"
                by auto
              have "StoreCapProp r (PreserveDomain actions) s'"
                using CanBeSimulatedE[OF abstraction intra_suc]
                by auto
              from StoreCapPropE_mem
                   [OF this _ _ valid2, 
                    where a=a and a'="ExtendCapAddress a" and actions=actions]
              obtain vAddr where "vAddr \<in> RegionOfCap (getCapReg auth r)" 
                                 "getTranslateAddr (vAddr, STORE) r = Some (ExtendCapAddress a)"
                using action StoreCapAction target
                by auto
              from getPhysicalCapAddressesI_word_cat[OF this(2) this(1)]
              have "a \<in> getPhysicalCapAddresses (StorableAddresses (Generalise (getCapReg auth r))) STORE r"
                using store
                unfolding word_size
                by (auto simp: Generalise_accessors
                         intro: getPhysicalCapAddressesI)
              hence "a \<in> getPhysicalCapAddresses (StorableAddresses (ReachablePermissions r)) STORE r"
                using getPhysicalCapAddresses_le[OF StorableAddresses_le[OF gperm]]
                by auto
              thus False
                using no_access2
                unfolding StorablePhysCapAddresses_def Let_def
                unfolding getPhysicalCapAddresses_distrib_union
                by simp
            qed simp_all
        qed
      hence "\<And>prov. prov \<in> actions \<Longrightarrow> LocMem a \<notin> CapDerivationTargets prov"
        by auto
      from CanBeSimulatedE_CapabilityInvariant[OF abstraction intra_suc _ this valid2]
      show ?thesis by auto
    qed
  thus ?case using ih by auto
qed simp

theorem MemCapInvariant:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(step # trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and inter: "\<not> PreservesDomain step"
      and no_access: "a \<notin> StorablePhysCapAddresses (ReachablePermissions s) s"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "getMemCap a s' = getMemCap a s"
proof -
  obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
             and r\<^sub>2: "(step, s') \<in> sem r"
    using trace by auto
  obtain crossing where step: "step = SwitchDomain crossing"
    using inter by (cases step) auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have "getMemCap a s' = getMemCap a r"
    proof (cases crossing)
      case RaiseException
      hence "(SwitchDomain RaiseException, s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_Exception[OF abstraction this _ valid2]
      show ?thesis
        unfolding getMemCap_def
        by auto
    next
      case (InvokeCapability cd cd')
      hence "(SwitchDomain (InvokeCapability cd cd'), s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_InvokeCap[OF abstraction this _ valid2]
      show ?thesis
        unfolding getMemCap_def
        by auto
    qed
  have "getMemCap a r = getMemCap a s"
    using MemCapInvariant_intra[OF abstraction r\<^sub>1 intra no_access no_sys valid]
    by simp
  thus ?thesis
    using `getMemCap a s' = getMemCap a r`
    by auto
qed

subsection \<open>Invariance of data\<close>

lemma MemoryInvariant_intra:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and no_access: "a \<notin> StorablePhysAddresses (ReachablePermissions s) s"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "getMemByte a s' = getMemByte a s"
using trace intra
proof (induct trace arbitrary: s')
  case (Cons step trace)
  then obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
                  and r\<^sub>2: "(step, s') \<in> sem r"
    by auto
  have intra2: "IntraDomainTrace trace"
    using Cons by auto
  have ih: "getMemByte a r = getMemByte a s"
    using Cons(1)[OF r\<^sub>1] Cons(3)
    by auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have no_ex2: "step \<noteq> SwitchDomain RaiseException"
    using Cons(3)
    by auto
  have perms: "ReachablePermissions r \<le> ReachablePermissions s"
    using MonotonicityReachablePermissions[OF abstraction r\<^sub>1 intra2 no_sys valid]
    by auto
  from SystemRegisterAccess_le[OF this]
  have no_sys2: "\<not> SystemRegisterAccess (ReachablePermissions r)"
    using no_sys by auto
  have no_sys_pcc: "\<not> Access_System_Registers (getPerms (getPCC r))"
    using SystemRegisterAccess_PCC[OF abstraction r\<^sub>2 no_ex2 no_sys2 valid2]
    by auto
  have addrTrans: "getTranslateAddr a r = getTranslateAddr a s" for a
    using TraceInvarianceAddressTranslation[OF abstraction r\<^sub>1 intra2 no_sys valid]
    by auto
  from StorablePhysAddresses_le[OF perms]
  have no_access2: "a \<notin> StorablePhysAddresses (ReachablePermissions r) r"
    using getTranslateAddresses_eqI_getTranslateAddr[OF addrTrans]
    using no_access
    unfolding StorablePhysAddresses_def
    by auto
  hence "getMemByte a s' = getMemByte a r"
    proof -
      obtain actions where "step = PreserveDomain actions"
        using Cons(3)
        by (cases step) auto
      hence intra_suc: "(PreserveDomain actions, s') \<in> sem r"
        using r\<^sub>2
        by auto
      have no_store_data: 
        "\<not> (\<exists>auth a' l. StoreDataAction auth a' l \<in> actions \<and> a \<in> Region a' l)" 
        proof (clarify)
          fix auth a' l
          assume prov: "StoreDataAction auth a' l \<in> actions" 
             and addr: "a \<in> Region a' l "
          hence "l \<noteq> 0"
            by auto
          note store = CanBeSimulatedE_StoreData[OF abstraction intra_suc _ prov valid2]
          have *: "a \<in> getTranslateAddresses (StorableAddresses (Generalise (getCapReg auth r))) STORE r"
            using store addr
            by (auto simp: Generalise_accessors intro: getTranslateAddressesI)
          have "getCapReg auth r \<in> ReachableCaps r"
            using ReachableCaps_CapReg
                  [OF abstraction intra_suc prov _ no_sys_pcc valid2, where r=auth]
            using store `l \<noteq> 0`
            by (cases auth) auto
          hence "getCapReg auth r \<in> TransUsableCaps r"
            using store 
            by auto
          hence "Generalise (getCapReg auth r) \<le> ReachablePermissions r"
            by auto
          note StorableAddresses_le[OF this]
          from getTranslateAddresses_le[OF this]
          show False
            using no_access2 *
            unfolding StorablePhysAddresses_def
            by auto
        qed
      have no_store_cap: 
        "\<not> (\<exists>auth cd a'. StoreCapAction auth cd a' \<in> actions \<and> 
                         a \<in> Region (ExtendCapAddress a') 32)" 
        proof (clarify)
          fix auth cd a'
          assume prov: "StoreCapAction auth cd a' \<in> actions" 
             and addr: "a \<in> Region (ExtendCapAddress a') 32"
          note store = CanBeSimulatedE_StoreCap[OF abstraction intra_suc _ prov valid2]
          have *: "a \<in> getTranslateAddresses (StorableAddresses (Generalise (getCapReg auth r))) STORE r"
            using store addr
            by (auto simp: Generalise_accessors intro: getTranslateAddressesI)
          have "getCapReg auth r \<in> ReachableCaps r"
            using ReachableCaps_CapReg
                  [OF abstraction intra_suc prov _ no_sys_pcc valid2, where r=auth]
            using store
            by (cases auth) auto
          hence "getCapReg auth r \<in> TransUsableCaps r"
            using store 
            by auto
          hence "Generalise (getCapReg auth r) \<le> ReachablePermissions r"
            by auto
          note StorableAddresses_le[OF this]
          from getTranslateAddresses_le[OF this]
          show False
            using no_access2 *
            unfolding StorablePhysAddresses_def
            by auto
        qed
      have "\<And>prov. prov \<in> actions \<Longrightarrow> a \<notin> WrittenAddresses prov"
        unfolding WrittenAddresses_def
        using no_store_data no_store_cap
        by (auto split: DomainAction.splits)
      from CanBeSimulatedE_MemoryInvariant[OF abstraction intra_suc _ this valid2]
      show ?thesis 
        by auto
    qed
  thus ?case
    using ih by auto
qed simp

theorem MemoryInvariant:
  assumes abstraction: "CanBeSimulated sem"
      and trace: "(step # trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and inter: "\<not> PreservesDomain step"
      and no_access: "a \<notin> StorablePhysAddresses (ReachablePermissions s) s"
      and no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
      and valid: "getStateIsValid s"
  shows "getMemByte a s' = getMemByte a s"
proof -
  obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
             and r\<^sub>2: "(step, s') \<in> sem r"
    using trace by auto
  obtain crossing where step: "step = SwitchDomain crossing"
    using inter by (cases step) auto
  have valid2: "getStateIsValid r"
    using TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
    by auto
  have "getMemByte a s' = getMemByte a r"
    proof (cases crossing)
      case RaiseException
      hence "(SwitchDomain RaiseException, s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_Exception[OF abstraction this _ valid2]
      show ?thesis
        unfolding getMemByte_def
        by auto
    next
      case (InvokeCapability cd cd')
      hence "(SwitchDomain (InvokeCapability cd cd'), s') \<in> sem r"
        using r\<^sub>2 step by auto
      from CanBeSimulatedE_InvokeCap[OF abstraction this _ valid2]
      show ?thesis
        unfolding getMemByte_def
        by auto
    qed
  have "getMemByte a r = getMemByte a s"
    using MemoryInvariant_intra[OF abstraction r\<^sub>1 intra no_access no_sys valid]
    by metis
  thus ?thesis
    using `getMemByte a s' = getMemByte a r`
    by auto
qed

(*<*)
end
(*>*)