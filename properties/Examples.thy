(*<*)

(* Author: Kyndylan Nienhuis *)

theory Examples

imports 
  "CHERI-instantiation.CheriInstantiation"
  "TraceProperties"
begin
(*>*)

section \<open>Reference monitor\<close>

definition CapabilityAligned :: "('a::len) word set \<Rightarrow> bool" where
  "CapabilityAligned addresses \<equiv>
   \<forall>a b. (a AND NOT mask 5 = b AND NOT mask 5) \<longrightarrow>
         a \<in> addresses \<longrightarrow>
         b \<in> addresses"

lemma CapabilityAlignedE:
  fixes addresses :: "('a::len) word set"
  assumes "CapabilityAligned addresses"
      and "a AND NOT mask 5 = b AND NOT mask 5"
      and "a \<in> addresses"
  shows "b \<in> addresses"
using assms
unfolding CapabilityAligned_def
by blast

lemma CapabilityAligned_CapAddressE:
  fixes addresses :: "40 word set"
  assumes "CapabilityAligned addresses"
      and "GetCapAddress a = GetCapAddress b"
      and "a \<in> addresses"
  shows "b \<in> addresses"
proof -
  have "a AND NOT mask 5 = b AND NOT mask 5"
    using `GetCapAddress a = GetCapAddress b`
    unfolding GetCapAddress_def
    using slice_eq_imp_and_not_mask_eq[where x=a and y=b and n=5 and 'b=35]
    by auto
  thus ?thesis
    using assms CapabilityAlignedE
    by metis
qed

lemma TranslationCapabilityAligned:
  assumes "CapabilityAligned segment"
  shows "CapabilityAligned (getTranslateAddresses segment t s)"
unfolding CapabilityAligned_def
proof clarify
  fix a b :: PhysicalAddress
  assume aligned: "a AND NOT mask 5 = b AND NOT mask 5"
     and "a \<in> getTranslateAddresses segment t s"
  then obtain virtA where "virtA \<in> segment" 
                      and a: "getTranslateAddr (virtA, t) s = Some a"
    by auto
  define virtB where "virtB \<equiv> (virtA AND NOT mask 12) OR ((ucast b) AND mask 12)"
  have virtB_upper: "virtB AND NOT mask 12 = virtA AND NOT mask 12"
    unfolding virtB_def
    by (simp add: word_ao_dist word_bool_alg.conj_assoc)
  have virtB_lower: "ucast virtB AND mask 12 = b AND mask 12"
    unfolding virtB_def
    by (auto simp: word_ao_dist word_bool_alg.conj_assoc ucast_and ucast_or ucast_not)
  have "getTranslateAddr (virtA AND NOT mask 12, t) s = Some (a AND NOT mask 12)"
    using a
    unfolding getTranslateAddr_and_not_mask
    by simp
  hence "getTranslateAddr (virtB AND NOT mask 12, t) s = Some (b AND NOT mask 12)"
    using arg_cong[OF aligned, where f="\<lambda>x. x AND NOT mask 12"]
    by (simp add: virtB_upper)
  hence b: "getTranslateAddr (virtB, t) s = Some b"
    unfolding getTranslateAddr_split[where vAddr=virtB]
    by (auto simp: virtB_lower)
  have "virtA AND NOT mask 5 = virtB AND NOT mask 5"
    proof (intro word_eqI, simp add: word_size, intro impI)
      fix n :: nat
      assume "n < 64"
      thus "(virtA AND NOT mask 5) !! n = (virtB AND NOT mask 5) !! n"
        using word_eqD[OF aligned, where x=n]
        using word_eqD[OF virtB_upper, where x=n]
        using word_eqD[OF getTranslateAddr_ucast12[OF a], where x=n]
        using word_eqD[OF getTranslateAddr_ucast12[OF b], where x=n]
        by (cases "n < 12") (simp_all add: nth_ucast word_ops_nth_size word_size)
     qed        
  from CapabilityAlignedE[OF assms this]
  have "virtB \<in> segment"
    using `virtA \<in> segment` 
    by auto
  thus "b \<in> getTranslateAddresses segment t s"
    using b
    unfolding getTranslateAddresses_def
    by auto
qed

definition AuthorityOfSegment where
  "AuthorityOfSegment segment types \<equiv>
   \<lparr>SystemRegisterAccess = False,
    ExecutableAddresses = segment,
    LoadableAddresses = segment,
    CapLoadableAddresses = segment,
    StorableAddresses = segment,
    CapStorableAddresses = segment,
    LocalCapStorableAddresses = segment,
    SealableTypes = types,
    UnsealableTypes = types\<rparr>"

lemma AuthorityOfSegment_simp [simp]:
  shows "SystemRegisterAccess (AuthorityOfSegment segment types) = False"
    and "ExecutableAddresses (AuthorityOfSegment segment types) = segment"
    and "LoadableAddresses (AuthorityOfSegment segment types) = segment"
    and "CapLoadableAddresses (AuthorityOfSegment segment types) = segment"
    and "StorableAddresses (AuthorityOfSegment segment types) = segment"
    and "CapStorableAddresses (AuthorityOfSegment segment types) = segment"
    and "LocalCapStorableAddresses (AuthorityOfSegment segment types) = segment"
    and "SealableTypes (AuthorityOfSegment segment types) = types"
    and "UnsealableTypes (AuthorityOfSegment segment types) = types"
unfolding AuthorityOfSegment_def
by simp_all

definition GrantedCaps where 
  "GrantedCaps segment s \<equiv>
   {getCapReg r s |r. RegisterIsAlwaysAccessible r} \<union>
   {getMemCap (GetCapAddress a) s |a. a \<in> getTranslateAddresses segment LOAD s}"

lemma ReadableCaps_AuthorityOfSegment:
  shows "ReadableCaps (AuthorityOfSegment segment types) s = 
         {cap. cap \<in> GrantedCaps segment s \<and> getTag cap}"
proof (intro equalityI; clarify, (intro conjI)?)
  fix cap
  assume "cap \<in> GrantedCaps segment s"
     and "getTag cap"
  thus "cap \<in> ReadableCaps (AuthorityOfSegment segment types) s"
    unfolding GrantedCaps_def
    proof (elim UnE; clarify)
      fix r
      assume "RegisterIsAlwaysAccessible r"
         and "getTag (getCapReg r s)"
      thus "getCapReg r s \<in> ReadableCaps (AuthorityOfSegment segment types) s"
        by (auto intro!: ReadableCapsI[where loc="LocReg r"])
    next
      fix a
      assume "a \<in> getTranslateAddresses segment LOAD s"
         and "getTag (getMemCap (GetCapAddress a) s)"
      thus "getMemCap (GetCapAddress a) s \<in> ReadableCaps (AuthorityOfSegment segment types) s"
        by (auto intro!: ReadableCapsI[where loc="LocMem (GetCapAddress a)"]
                 simp: getTranslateCapAddresses_def)
    qed
next
  fix cap
  assume readable: "cap \<in> ReadableCaps (AuthorityOfSegment segment types) s"
  thus "getTag cap" by auto
  show "cap \<in> GrantedCaps segment s"
    using readable
    unfolding ReadableCaps_def
    proof clarify
      fix loc
      assume loc: "loc \<in> ReadableLocations (AuthorityOfSegment segment types) s"
         and tag: "getTag (getCap loc s)"
      show "getCap loc s \<in> GrantedCaps segment s"
        proof (cases loc)
          case (LocReg r)
          hence "RegisterIsAlwaysAccessible r"
            using loc
            by auto
          thus ?thesis
            using loc tag LocReg
            unfolding GrantedCaps_def
            by auto
        next
          case (LocMem a)
          then obtain a' where "a = GetCapAddress a'" "a' \<in> getTranslateAddresses segment LOAD s"
            using loc
            by (auto simp: getTranslateCapAddresses_def)
          thus ?thesis
            using loc tag LocMem
            unfolding GrantedCaps_def
            by auto
        qed
    qed
qed

definition UsableCaps where 
  "UsableCaps segment types s \<equiv>
   {cap\<in>GrantedCaps segment s. 
    getTag cap \<and>
    (\<not> getSealed cap \<or> getType cap \<in> types)}"

definition InvokableCaps where 
  "InvokableCaps segment s \<equiv>
   {cap\<in>GrantedCaps segment s. 
    getTag cap \<and> Permit_CCall (getPerms cap)}"

lemma Authority_le_AuthorityOfSegment:
  shows "(GetAuthority cap \<le> AuthorityOfSegment segment types) =
         (\<not> getTag cap \<or>
          ((Permit_Seal (getPerms cap) \<or>
            Permit_Unseal (getPerms cap)) \<longrightarrow>
           (\<forall>t. ucast t \<in> RegionOfCap cap \<longrightarrow> t \<in> types)) \<and>
          ((Permit_Execute (getPerms cap) \<or>
            Permit_Load (getPerms cap) \<or>
            Permit_Load_Capability (getPerms cap) \<or>
            Permit_Store (getPerms cap) \<or>
            Permit_Store_Capability (getPerms cap) \<or>
            Permit_Store_Local_Capability (getPerms cap)) \<longrightarrow>
           RegionOfCap cap \<subseteq> segment) \<and>
          \<not> Access_System_Registers (getPerms cap))"
unfolding less_eq_CompartmentAuthority_ext_def
unfolding GetAuthority_accessors
by auto

definition NoSystemRegisterAccess where
  "NoSystemRegisterAccess segment types s \<equiv>
   \<forall>cap. cap \<in> UsableCaps segment types s \<longrightarrow> 
    \<not> Access_System_Registers (getPerms cap)"

definition ContainedCapBounds where
  "ContainedCapBounds segment types s \<equiv>
   \<forall>cap. (cap \<in> UsableCaps segment types s \<and>
          (Permit_Execute (getPerms cap) \<or>
           Permit_Load (getPerms cap) \<or>
           Permit_Load_Capability (getPerms cap) \<or>
           Permit_Store (getPerms cap) \<or>
           Permit_Store_Capability (getPerms cap) \<or>
           Permit_Store_Local_Capability (getPerms cap))) \<longrightarrow>
          RegionOfCap cap \<subseteq> segment"

definition ContainedObjectTypes where 
  "ContainedObjectTypes segment types s \<equiv>
   \<forall>cap. (cap \<in> UsableCaps segment types s \<and>
          (Permit_Seal (getPerms cap) \<or>
           Permit_Unseal (getPerms cap))) \<longrightarrow>
         (\<forall>t. ucast t \<in> RegionOfCap cap \<longrightarrow> t \<in> types)"

definition InvokableCapsSetup where 
  "InvokableCapsSetup segment types exit s ==  
   \<forall>cap. cap \<in> InvokableCaps segment s \<longrightarrow> 
         getSealed cap \<and> getType cap \<notin> types \<and> getBase cap + getOffset cap \<in> exit"

definition CapabilitySetup where
  "CapabilitySetup segment types exit s \<equiv>
   NoSystemRegisterAccess segment types s \<and>
   ContainedCapBounds segment types s \<and>
   ContainedObjectTypes segment types s \<and>
   InvokableCapsSetup segment types exit s"

definition IsolationGuarantees where
  "IsolationGuarantees segment exit s s' \<equiv>
   (getBase (getPCC s') + getPC s' \<in> exit) \<and>
   (\<forall>a. a \<notin> getTranslateAddresses segment STORE s \<longrightarrow> 
        (getMemByte a s' = getMemByte a s \<and>
         getMemTag (GetCapAddress a) s' = getMemTag (GetCapAddress a) s)) \<and>
   (\<forall>cd. (cd \<noteq> 0 \<and> cd \<noteq> 1 \<and> cd \<noteq> 31) \<longrightarrow> 
         getSCAPR cd s' = getSCAPR cd s)"

lemma CompartmentIsolation:
  assumes abstraction: "CanBeSimulated sem"
      and valid: "getStateIsValid s"
      and aligned: "CapabilityAligned segment"
      and ex: "ExceptionPCs \<subseteq> exit"
      and caps: "CapabilitySetup segment types exit s"
      and trace: "(step # trace, s') \<in> Traces sem s"
      and intra: "IntraDomainTrace trace"
      and inter: "\<not> PreservesDomain step"
  shows "IsolationGuarantees segment exit s s'"
unfolding IsolationGuarantees_def
proof (intro conjI allI impI)
  have systemreg: "\<forall>cap. cap \<in> UsableCaps segment types s \<longrightarrow> 
                   \<not> Access_System_Registers (getPerms cap)"
    using caps
    unfolding CapabilitySetup_def NoSystemRegisterAccess_def
    by simp
  have segment: "\<forall>cap. (cap \<in> UsableCaps segment types s \<and>
                 (Permit_Execute (getPerms cap) \<or>
                  Permit_Load (getPerms cap) \<or>
                  Permit_Load_Capability (getPerms cap) \<or>
                  Permit_Store (getPerms cap) \<or>
                  Permit_Store_Capability (getPerms cap) \<or>
                  Permit_Store_Local_Capability (getPerms cap))) \<longrightarrow>
                 RegionOfCap cap \<subseteq> segment"
    using caps
    unfolding CapabilitySetup_def ContainedCapBounds_def
    by simp
  have types: "\<forall>cap. (cap \<in> UsableCaps segment types s \<and>
              (Permit_Seal (getPerms cap) \<or>
               Permit_Unseal (getPerms cap))) \<longrightarrow>
              (\<forall>t. ucast t \<in> RegionOfCap cap \<longrightarrow> t \<in> types)"
    using caps
    unfolding CapabilitySetup_def ContainedObjectTypes_def
    by simp
  have invokable: "\<forall>cap. cap \<in> InvokableCaps segment s \<longrightarrow> 
                         getSealed cap \<and> getType cap \<notin> types \<and> getBase cap + getOffset cap \<in> exit"
    using caps
    unfolding CapabilitySetup_def InvokableCapsSetup_def
    by simp
  define gPerm where "gPerm = AuthorityOfSegment segment types"
  note [simp] = ReadableCaps_AuthorityOfSegment
  have closed: "PermIsClosed gPerm s"
    unfolding gPerm_def PermIsClosed_def ReadableCaps_AuthorityOfSegment
    proof clarsimp
      fix cap
      assume "cap \<in> GrantedCaps segment s"
             "getTag cap"
             "getSealed cap \<longrightarrow> getType cap \<in> types"
      hence "cap \<in> UsableCaps segment types s"
        unfolding UsableCaps_def
        by auto
      thus "GetAuthority cap \<le> AuthorityOfSegment segment types"
        using systemreg[THEN spec[where x=cap]]
        using segment[THEN spec[where x=cap]]
        using types[THEN spec[where x=cap]]
        unfolding Authority_le_AuthorityOfSegment
        by simp
     qed
  note gPerm_def [simp]
  note gperm = ReachablePermissionsInClosedPerm[OF closed]
  have no_sys: "\<not> SystemRegisterAccess (ReachablePermissions s)"
    using SystemRegisterAccess_le[OF gperm]
    by auto
  obtain r where r\<^sub>1: "(trace, r) \<in> Traces sem s"
             and r\<^sub>2: "(step, s') \<in> sem r"
    using trace by auto
  note r_valid = TraceInvarianceStateIsValid[OF abstraction valid r\<^sub>1]
  obtain crossing where [simp]: "step = SwitchDomain crossing"
    using inter by (cases step) auto
  show "getMemByte a s' = getMemByte a s"
  if "a \<notin> getTranslateAddresses segment STORE s" for a
    proof -
      have "a \<notin> StorablePhysAddresses gPerm s"
        using that
        unfolding StorablePhysAddresses_def
        by auto
      hence "a \<notin> StorablePhysAddresses (ReachablePermissions s) s"
        using StorablePhysAddresses_le[OF gperm]
        by auto
      thus ?thesis
        using MemoryInvariant[OF abstraction trace intra inter _ no_sys valid]
        by metis
    qed
  show "getMemTag (GetCapAddress a) s' = getMemTag (GetCapAddress a) s" 
  if "a \<notin> getTranslateAddresses segment STORE s" for a
    proof -
      have "GetCapAddress a \<notin> StorablePhysCapAddresses gPerm s"
        proof
          assume "GetCapAddress a \<in> StorablePhysCapAddresses gPerm s"
          then obtain b where "b \<in> getTranslateAddresses segment STORE s"
                          and "GetCapAddress b = GetCapAddress a"
            unfolding StorablePhysCapAddresses_def
            unfolding getTranslateCapAddresses_def
            by auto
          hence "a \<in> getTranslateAddresses segment STORE s"
            using TranslationCapabilityAligned[OF aligned, where s=s and t=STORE]
            using CapabilityAligned_CapAddressE[where a=b and b=a]
            by auto
          thus False
            using that
            by auto
        qed
      hence "GetCapAddress a \<notin> StorablePhysCapAddresses (ReachablePermissions s) s"
        using StorablePhysCapAddresses_le[OF gperm]
        by auto
      hence "getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s"  
        using MemCapInvariant[OF abstraction trace intra inter _ no_sys valid]
        by metis
      thus ?thesis
        unfolding getMemTag_def
        by auto
    qed
  show "getSCAPR cd s' = getSCAPR cd s" if "cd \<noteq> 0 \<and> cd \<noteq> 1 \<and> cd \<noteq> 31" for cd
    using SystemRegisterInvariant[OF abstraction trace intra inter no_sys _ _ _ valid]
    using that
    by metis   
  show "getBase (getPCC s') + getPC s' \<in> exit"
    proof (cases crossing)
      case RaiseException
      hence "(SwitchDomain RaiseException, s') \<in> sem r"
        using r\<^sub>2 by auto
      from CanBeSimulatedE_Exception[OF abstraction this _ r_valid]
      have "getBase (getPCC s') + getPC s' \<in> ExceptionPCs"
        by auto
      thus ?thesis
        using ex
        by auto
    next
      case (InvokeCapability cd cd')
      hence "(SwitchDomain (InvokeCapability cd cd'), s') \<in> sem r"
        using r\<^sub>2 by auto
      note invoke = CanBeSimulatedE_InvokeCap[OF abstraction this _ r_valid, 
                                              where cd=cd and cd'=cd']
      have "getCAPR cd r \<in> AvailableCaps r"
        using invoke by auto
      hence reachable: "getCAPR cd r \<in> AvailableCaps s"
        using MonotonicityAvailableCaps[OF abstraction r\<^sub>1 intra no_sys valid]
        by auto
      have "InvokableCapsNotUnsealable gPerm s"
        using invokable
        unfolding gPerm_def InvokableCapsNotUnsealable_def
        unfolding InvokableCaps_def
        by auto
      from InvokableCapsNotUnsealable_le[OF gperm this]
      have "getCAPR cd r \<in> ReadableCaps (ReachablePermissions s) s"
        using ReachableInvokableCapsAreReadable[OF reachable]
        using invoke
        by metis
      hence "getCAPR cd r \<in> InvokableCaps segment s"
        using ReadableCaps_le[OF gperm] invoke
        unfolding InvokableCaps_def
        by auto
      hence "getBase (getCAPR cd r ) + getOffset (getCAPR cd r ) \<in> exit"
        using invokable
        by auto
      hence "getBase (getPCC s') + getPC s' \<in> exit"
        using invoke
        by auto
      thus ?thesis
        by simp
    qed
qed

(*<*)
end
(*>*)
