(*<*) 

(* Author: Kyndylan Nienhuis *)

theory CheriAbstraction

imports 
  "CHERI-core.CheriLemmas"
begin
 
(*>*)
section \<open>Execution steps\<close>

subsection \<open>Domain actions\<close>

datatype DomainAction =
  LoadDataAction CapRegister PhysicalAddress PhysicalAddress |
  StoreDataAction CapRegister PhysicalAddress PhysicalAddress |
  RestrictCapAction CapRegister CapRegister |
  LoadCapAction CapRegister PhysicalCapAddress RegisterAddress |
  StoreCapAction CapRegister RegisterAddress PhysicalCapAddress |
  SealCapAction CapRegister RegisterAddress RegisterAddress |
  UnsealCapAction CapRegister RegisterAddress RegisterAddress

definition ActionAuthority :: "DomainAction \<Rightarrow> CapRegister option" where
  "ActionAuthority p \<equiv>
   case p of LoadDataAction auth _ l \<Rightarrow> Some auth
           | StoreDataAction auth _ l \<Rightarrow> Some auth
           | LoadCapAction auth _ _ \<Rightarrow> Some auth
           | StoreCapAction auth _ _ \<Rightarrow> Some auth
           | SealCapAction auth _ _ \<Rightarrow> Some auth
           | UnsealCapAction auth _ _ \<Rightarrow> Some auth
           | _ \<Rightarrow> None"

lemma ActionAuthority_simps [simp]:
  shows "ActionAuthority (LoadDataAction auth a' l) = Some auth"
    and "ActionAuthority (StoreDataAction auth a' l) = Some auth"
    and "ActionAuthority (RestrictCapAction r r') = None"
    and "ActionAuthority (LoadCapAction auth a cd) = Some auth"
    and "ActionAuthority (StoreCapAction auth cd a) = Some auth"
    and "ActionAuthority (SealCapAction auth cd cd') = Some auth"
    and "ActionAuthority (UnsealCapAction auth cd cd') = Some auth"
unfolding ActionAuthority_def
by simp_all

definition CapDerivations :: "DomainAction \<Rightarrow> (CapLocation \<times> CapLocation) set" where
  "CapDerivations p \<equiv>
   case p of StoreDataAction _ a l \<Rightarrow> {(LocMem (GetCapAddress a), LocMem (GetCapAddress a))}
           | RestrictCapAction r r' \<Rightarrow> {(LocReg r, LocReg r')}
           | LoadCapAction _ a cd \<Rightarrow> {(LocMem a, LocReg (RegGeneral cd))}
           | StoreCapAction _ cd a \<Rightarrow> {(LocReg (RegGeneral cd), LocMem a)}
           | SealCapAction _ cd cd' \<Rightarrow> {(LocReg (RegGeneral cd), LocReg (RegGeneral cd'))}
           | UnsealCapAction _ cd cd' \<Rightarrow> {(LocReg (RegGeneral cd), LocReg (RegGeneral cd'))}
           | _ \<Rightarrow> {}"

lemma CapDerivations_simps [simp]:
  shows "CapDerivations (LoadDataAction auth a' l) = {}"
    and "CapDerivations (StoreDataAction auth a' l) = 
         {(LocMem (GetCapAddress a'), LocMem (GetCapAddress a'))}"
    and "CapDerivations (RestrictCapAction r r') = 
         {(LocReg r, LocReg r')}"
    and "CapDerivations (LoadCapAction auth a cd) = 
         {(LocMem a, LocReg (RegGeneral cd))}"
    and "CapDerivations (StoreCapAction auth cd a) = 
         {(LocReg (RegGeneral cd), LocMem a)}"
    and "CapDerivations (SealCapAction auth cd cd') = 
         {(LocReg (RegGeneral cd), LocReg (RegGeneral cd'))}"
    and "CapDerivations (UnsealCapAction auth cd cd') = 
         {(LocReg (RegGeneral cd), LocReg (RegGeneral cd'))}"
unfolding CapDerivations_def
by simp_all

definition CapDerivationSources :: "DomainAction \<Rightarrow> CapLocation set" where
  "CapDerivationSources p \<equiv> fst ` (CapDerivations p)"

lemma CapDerivationSources_simps [simp]:
  shows "CapDerivationSources (LoadDataAction auth a' l) = {}"
    and "CapDerivationSources (StoreDataAction auth a' l) = {LocMem (GetCapAddress a')}"
    and "CapDerivationSources (RestrictCapAction r r') = {LocReg r}"
    and "CapDerivationSources (LoadCapAction auth a cd) = {LocMem a}"
    and "CapDerivationSources (StoreCapAction auth cd a) = {LocReg (RegGeneral cd)}"
    and "CapDerivationSources (SealCapAction auth cd cd') = {LocReg (RegGeneral cd)}"
    and "CapDerivationSources (UnsealCapAction auth cd cd') = {LocReg (RegGeneral cd)}"
unfolding CapDerivationSources_def
by simp_all

definition CapDerivationTargets :: "DomainAction \<Rightarrow> CapLocation set" where
  "CapDerivationTargets p \<equiv> snd ` (CapDerivations p)"

lemma CapDerivationTargets_simps [simp]:
  shows "CapDerivationTargets (LoadDataAction auth a' l) = {}"
    and "CapDerivationTargets (StoreDataAction auth a' l) = {LocMem (GetCapAddress a')}"
    and "CapDerivationTargets (RestrictCapAction r r') = {LocReg r'}"
    and "CapDerivationTargets (LoadCapAction auth a cd) = {LocReg (RegGeneral cd)}"
    and "CapDerivationTargets (StoreCapAction auth cd a) = {LocMem a}"
    and "CapDerivationTargets (SealCapAction auth cd cd') = {LocReg (RegGeneral cd')}"
    and "CapDerivationTargets (UnsealCapAction auth cd cd') = {LocReg (RegGeneral cd')}"
unfolding CapDerivationTargets_def
by simp_all

definition CapDerivationRegisters :: "DomainAction \<Rightarrow> RegisterAddress set" where
  "CapDerivationRegisters p \<equiv>
   (case ActionAuthority p of Some (RegSpecial i) \<Rightarrow> {i}
                            | _ \<Rightarrow> {}) \<union>
   {i |i. LocReg (RegSpecial i) \<in> CapDerivationSources p} \<union>
   {i |i. LocReg (RegSpecial i) \<in> CapDerivationTargets p}"

lemma CapDerivationRegisters_simps [simp]:
  shows "CapDerivationRegisters (LoadDataAction auth a' l) = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (StoreDataAction auth a' l) = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (RestrictCapAction r r') = 
         (case r of RegSpecial i \<Rightarrow> {i} | _ \<Rightarrow> {}) \<union>
         (case r' of RegSpecial i \<Rightarrow> {i} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (LoadCapAction auth a cd) = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (StoreCapAction auth cd a) = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (SealCapAction auth cd cd') = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
    and "CapDerivationRegisters (UnsealCapAction auth cd cd') = 
         (case auth of RegSpecial cd \<Rightarrow> {cd} | _ \<Rightarrow> {})"
unfolding CapDerivationRegisters_def
by (auto split: CapRegister.splits)

definition WrittenAddresses where
  "WrittenAddresses p \<equiv>
   case p of StoreDataAction _ a l \<Rightarrow> MemSegment a l
           | StoreCapAction _ _ a \<Rightarrow> MemSegment (ExtendCapAddress a) 32
           | _ \<Rightarrow> {}"

lemma WrittenAddresses_simps [simp]:
  shows "WrittenAddresses (LoadDataAction auth a' l) = {}"
    and "WrittenAddresses (StoreDataAction auth a' l) = MemSegment a' l"
    and "WrittenAddresses (RestrictCapAction loc loc') = {}"
    and "WrittenAddresses (LoadCapAction auth a cd) = {}"
    and "WrittenAddresses (StoreCapAction auth cd a) = MemSegment (ExtendCapAddress a) 32"
    and "WrittenAddresses (SealCapAction auth cd cd') = {}"
    and "WrittenAddresses (UnsealCapAction auth cd cd') = {}"
unfolding WrittenAddresses_def
by simp_all

subsection \<open>Domain switches\<close>

datatype DomainSwitch =
  RaiseException |
  InvokeCapability RegisterAddress RegisterAddress

subsection \<open>Instruction intention\<close>

datatype InstructionIntention = 
  KeepDomain "DomainAction set" |
  SwitchDomain DomainSwitch

primrec KeepsDomain where
  "KeepsDomain (KeepDomain actions) = True" |
  "KeepsDomain (SwitchDomain crossing) = False"

abbreviation "SwitchesDomain step \<equiv> \<not> KeepsDomain step"

section \<open>Properties\<close>

type_synonym Semantics = "state \<Rightarrow> (InstructionIntention \<times> state) set"

definition ExecuteProp :: "Semantics \<Rightarrow> bool" where
  "ExecuteProp semantics \<equiv>
   \<forall>s s' step.
   (getStateIsValid s \<and> 
    (step, s') \<in> semantics s \<and>
    step \<noteq> SwitchDomain RaiseException) \<longrightarrow>
   (getTag (getPCC s) \<and>
    \<not> getSealed (getPCC s) \<and>
    Permit_Execute (getPerms (getPCC s)) \<and>
    getBase (getPCC s) + getPC s \<in> MemSegmentCap (getPCC s))"

lemma ExecutePropE [elim]:
  assumes "ExecuteProp semantics"
      and "(step, s') \<in> semantics s"
      and "step \<noteq> SwitchDomain RaiseException"
      and "getStateIsValid s"
  shows "getTag (getPCC s)"
    and "\<not> getSealed (getPCC s)"
    and "Permit_Execute (getPerms (getPCC s))"
    and "getBase (getPCC s) + getPC s \<in> MemSegmentCap (getPCC s)"
using assms
unfolding ExecuteProp_def
by fast+

definition LoadDataProp :: "Semantics \<Rightarrow> bool" where
  "LoadDataProp semantics \<equiv>
   \<forall>s s' actions auth a l.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    LoadDataAction auth a l \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Load (getPerms (getCapReg auth s)) \<and>
    l \<noteq> 0 \<and>
    MemSegment a l \<subseteq> getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) LOAD s)"

lemma LoadDataPropE [elim]:
  assumes "LoadDataProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "LoadDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Load (getPerms (getCapReg auth s))"
    and "l \<noteq> 0"
    and "MemSegment a l \<subseteq> getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) LOAD s"
using assms
unfolding LoadDataProp_def
by fast+

lemma LoadDataPropE_mem:
  assumes "LoadDataProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "LoadDataAction auth a l \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> MemSegment a l"
  obtains vAddr 
  where "vAddr \<in> MemSegmentCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, LOAD) s = Some a'"
using LoadDataPropE[OF assms(1-4)] assms(5)
by fast

definition StoreDataProp :: "Semantics \<Rightarrow> bool" where
  "StoreDataProp semantics \<equiv>
   \<forall>s s' actions auth a l.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    StoreDataAction auth a l \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Store (getPerms (getCapReg auth s)) \<and>
    l \<noteq> 0 \<and> 
    MemSegment a l \<subseteq> getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s \<and>
    (\<not> getTag (getMemCap (GetCapAddress a) s') \<or> 
     getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s))"

lemma StoreDataPropE [elim]:
  assumes "StoreDataProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Store (getPerms (getCapReg auth s))"
    and "l \<noteq> 0"
    and "MemSegment a l \<subseteq> getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s"
    and "getTag (getMemCap (GetCapAddress a) s') \<Longrightarrow>
         getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s"
using assms
unfolding StoreDataProp_def
by fast+

lemma StoreDataPropE_mem:
  assumes "StoreDataProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> MemSegment a l"
  obtains vAddr 
  where "vAddr \<in> MemSegmentCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, STORE) s = Some a'"
using StoreDataPropE[OF assms(1-4)] assms(5)
by fast

lemma StoreDataPropE_cap [elim]:
  assumes "StoreDataProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getMemCap (GetCapAddress a) s' \<le> getMemCap (GetCapAddress a) s"
using StoreDataPropE[OF assms] 
by (cases "getTag (getMemCap (GetCapAddress a) s')") auto

definition RestrictCapProp :: "Semantics \<Rightarrow> bool" where
  "RestrictCapProp semantics \<equiv>
   \<forall>s s' actions r r'.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    RestrictCapAction r r' \<in> actions) \<longrightarrow>
   getCapReg r' s' \<le> getCapReg r s"

lemma RestrictCapPropE [elim]:
  assumes "RestrictCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "RestrictCapAction r r' \<in> actions"
      and "getStateIsValid s"
  shows "getCapReg r' s' \<le> getCapReg r s"
using assms
unfolding RestrictCapProp_def
by fast+

definition LoadCapProp :: "Semantics \<Rightarrow> bool" where
  "LoadCapProp semantics \<equiv>
   \<forall>s s' actions auth cd a.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    LoadCapAction auth a cd \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Load (getPerms (getCapReg auth s)) \<and>
    Permit_Load_Capability (getPerms (getCapReg auth s)) \<and>
    (MemSegment (ExtendCapAddress a) 32 \<subseteq> 
     getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) LOAD s) \<and>
    getCAPR cd s' \<le> getMemCap a s)"

lemma LoadCapPropE [elim]:
  assumes "LoadCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "LoadCapAction auth a cd \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Load (getPerms (getCapReg auth s))"
    and "Permit_Load_Capability (getPerms (getCapReg auth s))"
    and "MemSegment (ExtendCapAddress a) 32 \<subseteq> 
         getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) LOAD s"
    and "getCAPR cd s' \<le> getMemCap a s"
using assms
unfolding LoadCapProp_def
by fast+

lemma LoadCapPropE_mem:
  assumes "LoadCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "LoadCapAction auth a cd \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> MemSegment (ExtendCapAddress a) 32"
  obtains vAddr 
  where "vAddr \<in> MemSegmentCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, LOAD) s = Some a'"
using LoadCapPropE[OF assms(1-4)] assms(5)
by fast

definition StoreCapProp :: "Semantics \<Rightarrow> bool" where
  "StoreCapProp semantics \<equiv>
   \<forall>s s' actions auth cd a.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    StoreCapAction auth cd a \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Store (getPerms (getCapReg auth s)) \<and>
    Permit_Store_Capability (getPerms (getCapReg auth s)) \<and>
    (MemSegment (ExtendCapAddress a) 32 \<subseteq> 
     getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s) \<and>
    getMemCap a s' = getCAPR cd s)"

lemma StoreCapPropE [elim]:
  assumes "StoreCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreCapAction auth cd a \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Store (getPerms (getCapReg auth s))"
    and "Permit_Store_Capability (getPerms (getCapReg auth s))"
    and "MemSegment (ExtendCapAddress a) 32 \<subseteq> 
         getPhysicalAddresses (MemSegmentCap (getCapReg auth s)) STORE s"
    and "getMemCap a s' = getCAPR cd s"
using assms
unfolding StoreCapProp_def
by fast+

lemma StoreCapPropE_mem:
  assumes "StoreCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreCapAction auth cd a \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> MemSegment (ExtendCapAddress a) 32"
  obtains vAddr 
  where "vAddr \<in> MemSegmentCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, STORE) s = Some a'"
using StoreCapPropE[OF assms(1-4)] assms(5)
by fast

definition StoreLocalCapProp :: "Semantics \<Rightarrow> bool" where
  "StoreLocalCapProp semantics \<equiv>
   \<forall>s s' actions auth cd a.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    StoreCapAction auth cd a \<in> actions \<and>
    getTag (getCAPR cd s) \<and>
    \<not> Global (getPerms (getCAPR cd s))) \<longrightarrow>
   Permit_Store_Local_Capability (getPerms (getCapReg auth s))"

lemma StoreLocalCapPropE [elim]:
  assumes "StoreLocalCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "StoreCapAction auth cd a \<in> actions"
      and "getTag (getCAPR cd s)"
      and "\<not> Global (getPerms (getCAPR cd s))"
      and "getStateIsValid s"
  shows "Permit_Store_Local_Capability (getPerms (getCapReg auth s))"
using assms
unfolding StoreLocalCapProp_def
by fast+

definition SealCapProp :: "Semantics \<Rightarrow> bool" where
  "SealCapProp semantics \<equiv>
   \<forall>s s' actions auth cd cd'.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    SealCapAction auth cd cd' \<in> actions) \<longrightarrow>
   (let t = ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s)) in
    getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Seal (getPerms (getCapReg auth s)) \<and>
    ucast t \<in> MemSegmentCap (getCapReg auth s) \<and>
    \<not> getSealed (getCAPR cd s) \<and>
    getCAPR cd' s' = setType (setSealed ((getCAPR cd s), True), t))"

lemma SealCapPropE [elim]:
  fixes s auth
  defines "t \<equiv> ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s))"
  assumes "SealCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "SealCapAction auth cd cd' \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Seal (getPerms (getCapReg auth s))"
    and "ucast t \<in> MemSegmentCap (getCapReg auth s)"
    and  "\<not> getSealed (getCAPR cd s)"
    and "getCAPR cd' s' = setType (setSealed ((getCAPR cd s), True), t)"
using assms
unfolding SealCapProp_def Let_def
by fast+

definition UnsealCapProp :: "Semantics \<Rightarrow> bool" where
  "UnsealCapProp semantics \<equiv>
   \<forall>s s' actions auth cd cd'.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    UnsealCapAction auth cd cd' \<in> actions) \<longrightarrow>
   (Permit_Unseal (getPerms (getCapReg auth s)) \<and>
    getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    ucast (getType (getCAPR cd s)) \<in> MemSegmentCap (getCapReg auth s) \<and>
    getSealed (getCAPR cd s) \<and>
    getCAPR cd' s' \<le> setType (setSealed ((getCAPR cd s), False), 0))"

lemma UnsealCapPropE [elim]:
  assumes "UnsealCapProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "UnsealCapAction auth cd cd' \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Unseal (getPerms (getCapReg auth s))"
    and "ucast (getType (getCAPR cd s)) \<in> MemSegmentCap (getCapReg auth s)"
    and "getSealed (getCAPR cd s)"
    and "getCAPR cd' s' \<le> setType (setSealed ((getCAPR cd s), False), 0)"
using assms
unfolding UnsealCapProp_def
by fast+

definition SystemRegisterProp :: "Semantics \<Rightarrow> bool" where
  "SystemRegisterProp semantics \<equiv>
   \<forall>s s' actions cd.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>
    (cd \<noteq> 0 \<and> cd \<noteq> 1) \<and>
    cd \<in> \<Union> (CapDerivationRegisters ` actions)) \<longrightarrow>
   Access_System_Registers (getPerms (getPCC s))"

lemma SystemRegisterPropE [elim]:
  assumes "SystemRegisterProp semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "cd \<in> \<Union> (CapDerivationRegisters ` actions)"
      and "cd \<noteq> 0" "cd \<noteq> 1"
      and "getStateIsValid s"
  shows "Access_System_Registers (getPerms (getPCC s))"
using assms
unfolding SystemRegisterProp_def
by fast+

definition InvokeCapProp :: "Semantics \<Rightarrow> bool" where
  "InvokeCapProp semantics \<equiv>
   \<forall>s s' cd cd'. 
   (getStateIsValid s \<and>
    (SwitchDomain (InvokeCapability cd cd'), s') \<in> semantics s) \<longrightarrow>
   (let codeCap = getCAPR cd s in
    let dataCap = getCAPR cd' s in
    getTag codeCap \<and>
    getTag dataCap \<and>
    getSealed codeCap \<and>
    getSealed dataCap \<and>
    Permit_CCall (getPerms codeCap) \<and>
    Permit_CCall (getPerms dataCap) \<and> 
    Permit_Execute (getPerms codeCap) \<and>
    \<not> Permit_Execute (getPerms dataCap) \<and>
    getType codeCap = getType dataCap \<and>
    getPC s' = getOffset codeCap \<and>
    getPCC s' = setType (setSealed (codeCap, False), 0) \<and>
    getBranchDelay s' = None \<and>
    BranchDelayPCC s' = None \<and>
    (\<forall>x. getCAPR x s' = (if x = 26 then setType (setSealed (dataCap, False), 0)
                         else getCAPR x s)) \<and>
    (\<forall>x. getSCAPR x s' = getSCAPR x s) \<and>
    (\<forall>x. getMEM x s' = getMEM x s))"

lemma InvokeCapPropE [elim]:
  fixes cd cd' s cb cb' a
  defines "codeCap \<equiv> getCAPR cd s"
      and "dataCap \<equiv> getCAPR cd' s"
  assumes "InvokeCapProp semantics"
      and "(SwitchDomain (InvokeCapability cd cd'), s') \<in> semantics s"
      and "getStateIsValid s"
  shows "getTag codeCap"
    and "getTag dataCap"
    and "getSealed codeCap"
    and "getSealed dataCap"
    and "Permit_CCall (getPerms codeCap)"
    and "Permit_CCall (getPerms dataCap)"
    and "Permit_Execute (getPerms codeCap)"
    and "\<not> Permit_Execute (getPerms dataCap)"
    and "getType codeCap = getType dataCap"
    and "getPC s' = getOffset codeCap"
    and "getPCC s' = setType (setSealed (codeCap, False), 0)"
    and "getBranchDelay s' = None"
    and "BranchDelayPCC s' = None"
    and "getCAPR cb s' = (if cb = 26 then setType (setSealed (dataCap, False), 0)
                          else getCAPR cb s)"
    and "getSCAPR cb' s' = getSCAPR cb' s"
    and "getMEM a s' = getMEM a s"
using assms
unfolding InvokeCapProp_def Let_def
by fast+

definition ExceptionProp :: "Semantics \<Rightarrow> bool" where
  "ExceptionProp semantics \<equiv>
   \<forall>s s'.
   (getStateIsValid s \<and>
    (SwitchDomain RaiseException, s') \<in> semantics s) \<longrightarrow>
   (getCP0StatusEXL s' \<and>
    getBase (getPCC s') + getPC s' \<in> ExceptionPCs \<and>
    getPCC s' = getKCC s \<and>
    (\<forall>cd. getCAPR cd s' = getCAPR cd s) \<and>
    (\<forall>cd. getSCAPR cd s' = SignalExceptionSCAPR cd s) \<and>
    (\<forall>a. getMEM a s' = getMEM a s) \<and>
    getBranchDelay s' = None \<and>
    BranchDelayPCC s' = None)"

lemma ExceptionPropE [elim]:
  assumes "ExceptionProp semantics"
      and "(SwitchDomain RaiseException, s') \<in> semantics s"
      and "getStateIsValid s"
  shows "getCP0StatusEXL s'"
    and "getBase (getPCC s') + getPC s' \<in> ExceptionPCs"
    and "getPCC s' = getKCC s"
    and "getCAPR cd s' = getCAPR cd s"
    and "getSCAPR cd' s' = SignalExceptionSCAPR cd' s"
    and "getMEM a s' = getMEM a s"
    and "getBranchDelay s' = None"
    and "BranchDelayPCC s' = None"
using assms
unfolding ExceptionProp_def
by fast+

definition MemoryInvariant :: "Semantics \<Rightarrow> bool" where
  "MemoryInvariant semantics \<equiv>
   \<forall>s s' actions a.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>   
    (\<nexists>prov. prov \<in> actions \<and> a \<in> WrittenAddresses prov)) \<longrightarrow>
   (getMemData a s' = getMemData a s)"

lemma MemoryInvariantE [elim]:
  assumes "MemoryInvariant semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "\<And>prov. prov \<in> actions \<Longrightarrow> a \<notin> WrittenAddresses prov"
      and "getStateIsValid s"
  shows "getMemData a s' = getMemData a s"
using assms
unfolding MemoryInvariant_def
by fast+

definition CapabilityInvariant :: "Semantics \<Rightarrow> bool" where
  "CapabilityInvariant semantics \<equiv>
   \<forall>s s' actions loc.
   (getStateIsValid s \<and>
    (KeepDomain actions, s') \<in> semantics s \<and>   
    (\<nexists>prov. prov \<in> actions \<and> loc \<in> CapDerivationTargets prov)) \<longrightarrow> 
   (getCap loc s' = getCap loc s)"

lemma CapabilityInvariantE [elim]:
  assumes "CapabilityInvariant semantics"
      and "(KeepDomain actions, s') \<in> semantics s"
      and "\<And>prov. prov \<in> actions \<Longrightarrow> loc \<notin> CapDerivationTargets prov"
      and "getStateIsValid s"
  shows "getCap loc s' = getCap loc s"
using assms
unfolding CapabilityInvariant_def
by fast+

definition ValidStateProp :: "Semantics \<Rightarrow> bool" where
  "ValidStateProp semantics \<equiv>
   \<forall>s s' step.
   (getStateIsValid s \<and> (step, s') \<in> semantics s) \<longrightarrow>
   getStateIsValid s'"

lemma ValidStatePropE [elim]:
  assumes "ValidStateProp semantics"
      and "(step, s') \<in> semantics s"
      and "getStateIsValid s"
  shows "getStateIsValid s'"
using assms
unfolding ValidStateProp_def
by fast+

(* definition CU0AccessProp :: "Semantics \<Rightarrow> bool" where
  "CU0AccessProp semantics \<equiv>
   \<forall>s s' step.
   (getStateIsValid s \<and>
    \<not> getCP0StatusCU0 s \<and>
    \<not> getKernelMode s \<and>
    (step, s') \<in> semantics s) \<longrightarrow>
   \<not> getCP0StatusCU0 s'"

lemma CU0AccessPropE [elim]:
  assumes "CU0AccessProp semantics"
      and "(step, s') \<in> semantics s"
      and "\<not> getCP0StatusCU0 s"
      and "\<not> getKernelMode s"
      and "getStateIsValid s"
  shows "\<not> getCP0StatusCU0 s'"
using assms
unfolding CU0AccessProp_def
by fast+

definition KernelModeProp :: "Semantics \<Rightarrow> bool" where
  "KernelModeProp semantics \<equiv>
   \<forall>s s' step.
   (getStateIsValid s \<and>
    \<not> getCP0StatusCU0 s \<and>
    \<not> getKernelMode s \<and>
    (step, s') \<in> semantics s \<and>
    step \<noteq> SwitchDomain RaiseException) \<longrightarrow>
   \<not> getKernelMode s'"

lemma KernelModePropE [elim]:
  assumes "KernelModeProp semantics"
      and "(step, s') \<in> semantics s"
      and "step \<noteq> SwitchDomain RaiseException"
      and "\<not> getCP0StatusCU0 s"
      and "\<not> getKernelMode s"
      and "getStateIsValid s"
  shows "\<not> getKernelMode s'"
using assms
unfolding KernelModeProp_def
by fast+ *)

definition AddressTranslationProp :: "Semantics \<Rightarrow> bool" where
  "AddressTranslationProp semantics \<equiv>
   \<forall>s s' step a.
   (getStateIsValid s \<and>
    \<not> Access_System_Registers (getPerms (getPCC s)) \<and>
    (step, s') \<in> semantics s \<and>
    step \<noteq> SwitchDomain RaiseException) \<longrightarrow>
   getPhysicalAddress a s' = getPhysicalAddress a s"

lemma AddressTranslationPropE [elim]:
  assumes "AddressTranslationProp semantics"
      and "(step, s') \<in> semantics s"
      and "step \<noteq> SwitchDomain RaiseException"
      and "\<not> Access_System_Registers (getPerms (getPCC s))"
      and "getStateIsValid s"
  shows "getPhysicalAddress a s' = getPhysicalAddress a s"
using assms
unfolding AddressTranslationProp_def
by fast+

definition CheriAbstraction :: "Semantics \<Rightarrow> bool" where
  "CheriAbstraction semantics \<equiv>
   ExecuteProp semantics \<and>
   LoadDataProp semantics \<and>
   StoreDataProp semantics \<and>
   RestrictCapProp semantics \<and>
   LoadCapProp semantics \<and>
   StoreCapProp semantics \<and>
   StoreLocalCapProp semantics \<and>
   SealCapProp semantics \<and>
   UnsealCapProp semantics \<and>
   SystemRegisterProp semantics \<and> 
   InvokeCapProp semantics \<and>
   ExceptionProp semantics \<and>
   MemoryInvariant semantics \<and>
   CapabilityInvariant semantics \<and>
   ValidStateProp semantics \<and>
   AddressTranslationProp semantics"

lemma CheriAbstractionE [elim!]:
  assumes "CheriAbstraction semantics"
  shows "ExecuteProp semantics"
    and "LoadDataProp semantics"
    and "StoreDataProp semantics"
    and "RestrictCapProp semantics"
    and "LoadCapProp semantics"
    and "StoreCapProp semantics"
    and "StoreLocalCapProp semantics"
    and "SealCapProp semantics"
    and "UnsealCapProp semantics"
    and "SystemRegisterProp semantics"
    and "InvokeCapProp semantics"
    and "ExceptionProp semantics"
    and "MemoryInvariant semantics"
    and "CapabilityInvariant semantics"
    and "ValidStateProp semantics"
    and "AddressTranslationProp semantics"
using assms
unfolding CheriAbstraction_def
by auto

lemmas CheriAbstractionE_Execute = ExecutePropE[OF CheriAbstractionE(1)]
lemmas CheriAbstractionE_LoadData = LoadDataPropE[OF CheriAbstractionE(2)]
lemmas CheriAbstractionE_StoreData = StoreDataPropE[OF CheriAbstractionE(3)]
lemmas CheriAbstractionE_RestrictRegCap = RestrictCapPropE[OF CheriAbstractionE(4)]
lemmas CheriAbstractionE_LoadCap = LoadCapPropE[OF CheriAbstractionE(5)]
lemmas CheriAbstractionE_StoreCap = StoreCapPropE[OF CheriAbstractionE(6)]
lemmas CheriAbstractionE_StoreLocalCap = StoreLocalCapPropE[OF CheriAbstractionE(7)]
lemmas CheriAbstractionE_SealCap = SealCapPropE[OF CheriAbstractionE(8)]
lemmas CheriAbstractionE_UnsealCap = UnsealCapPropE[OF CheriAbstractionE(9)]
lemmas CheriAbstractionE_SystemRegister = SystemRegisterPropE[OF CheriAbstractionE(10)]
lemmas CheriAbstractionE_InvokeCap = InvokeCapPropE[OF CheriAbstractionE(11)]
lemmas CheriAbstractionE_Exception = ExceptionPropE[OF CheriAbstractionE(12)]
lemmas CheriAbstractionE_MemoryInvariant = MemoryInvariantE[OF CheriAbstractionE(13)]
lemmas CheriAbstractionE_CapabilityInvariant = CapabilityInvariantE[OF CheriAbstractionE(14)]
lemmas CheriAbstractionE_ValidState = ValidStatePropE[OF CheriAbstractionE(15)]
lemmas CheriAbstractionE_AddressTranslation = AddressTranslationPropE[OF CheriAbstractionE(16)]

section \<open>Derived properties\<close>

subsection \<open>Provenance\<close>

definition CapDerivationSourcesOfLoc :: "DomainAction set \<Rightarrow> CapLocation \<Rightarrow> CapLocation set" where
  "CapDerivationSourcesOfLoc actions loc \<equiv>
   {fst h |h d. d \<in> actions \<and> h \<in> CapDerivations d \<and> snd h = loc}"

definition ProvenanceParents :: "DomainAction set \<Rightarrow> CapLocation \<Rightarrow> CapLocation set" where
  "ProvenanceParents actions loc \<equiv>
   let derivationSources = CapDerivationSourcesOfLoc actions loc in
   if derivationSources = {} then {loc}
   else derivationSources"

lemma ProvenanceParentExists:
  obtains loc where "loc \<in> ProvenanceParents actions loc'"
unfolding ProvenanceParents_def Let_def
by (cases "CapDerivationSourcesOfLoc actions loc' = {}") auto

lemma ProvenanceCases:
  assumes parent: "loc \<in> ProvenanceParents actions loc'"
  obtains (StoreData) auth a l where
    "StoreDataAction auth a l \<in> actions"
    "loc = LocMem (GetCapAddress a)"
    "loc' = LocMem (GetCapAddress a)"
  | (RestrictedReg) r r' where
    "RestrictCapAction r r' \<in> actions"
    "loc = LocReg r"
    "loc' = LocReg r'"
  | (Loaded) auth a cd where
    "LoadCapAction auth a cd \<in> actions"
    "loc = LocMem a"
    "loc' = LocReg (RegGeneral cd)"
  | (Stored) auth cd a where
    "StoreCapAction auth cd a \<in> actions"
    "loc = LocReg (RegGeneral cd)"
    "loc' = LocMem a"
  | (Sealed) auth cd cd' where
    "SealCapAction auth cd cd' \<in> actions"
    "loc = LocReg (RegGeneral cd)"
    "loc' = LocReg (RegGeneral cd')"
  | (Unsealed) auth cd cd' where
    "UnsealCapAction auth cd cd' \<in> actions"
    "loc = LocReg (RegGeneral cd)"
    "loc' = LocReg (RegGeneral cd')"
  | (Unchanged)
    "loc' \<notin> \<Union> (CapDerivationTargets ` actions)"
    "loc = loc'"
proof (cases "CapDerivationSourcesOfLoc (actions) loc' = {}")
  case True
  hence "loc = loc'"
    using parent
    unfolding ProvenanceParents_def
    by simp
  have "loc' \<notin> \<Union> (CapDerivationTargets ` actions)"
    using True
    unfolding CapDerivationSourcesOfLoc_def CapDerivationTargets_def
    by auto
  thus ?thesis
    using `loc = loc'` that by simp
next
  case False
  hence "loc \<in> CapDerivationSourcesOfLoc (actions) loc'"
    using parent 
    unfolding ProvenanceParents_def
    by simp
  then obtain der
  where "der \<in> actions" 
  and "(loc, loc') \<in> CapDerivations der"
    unfolding CapDerivationSourcesOfLoc_def
    by auto
  thus ?thesis 
    using that
    by (cases der) (auto split: if_splits)
qed

(*<*)
end
(*>*)