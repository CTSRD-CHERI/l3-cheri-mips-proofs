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
   case p of StoreDataAction _ a l \<Rightarrow> Region a l
           | StoreCapAction _ _ a \<Rightarrow> Region (ExtendCapAddress a) 32
           | _ \<Rightarrow> {}"

lemma WrittenAddresses_simps [simp]:
  shows "WrittenAddresses (LoadDataAction auth a' l) = {}"
    and "WrittenAddresses (StoreDataAction auth a' l) = Region a' l"
    and "WrittenAddresses (RestrictCapAction loc loc') = {}"
    and "WrittenAddresses (LoadCapAction auth a cd) = {}"
    and "WrittenAddresses (StoreCapAction auth cd a) = Region (ExtendCapAddress a) 32"
    and "WrittenAddresses (SealCapAction auth cd cd') = {}"
    and "WrittenAddresses (UnsealCapAction auth cd cd') = {}"
unfolding WrittenAddresses_def
by simp_all

subsection \<open>Domain switches\<close>

datatype DomainSwitch =
  RaiseException |
  InvokeCapability RegisterAddress RegisterAddress

subsection \<open>Instruction intention\<close>

datatype AbstractStep = 
  PreserveDomain "DomainAction set" |
  SwitchDomain DomainSwitch

primrec PreservesDomain where
  "PreservesDomain (PreserveDomain actions) = True" |
  "PreservesDomain (SwitchDomain crossing) = False"

section \<open>Properties\<close>

type_synonym Semantics = "state \<Rightarrow> (AbstractStep \<times> state) set"

definition ExecuteProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "ExecuteProp s lbl s' \<equiv>
   (getStateIsValid s \<and> 
    lbl \<noteq> SwitchDomain RaiseException) \<longrightarrow>
   (getTag (getPCC s) \<and>
    \<not> getSealed (getPCC s) \<and>
    Permit_Execute (getPerms (getPCC s)) \<and>
    getBase (getPCC s) + getPC s \<in> RegionOfCap (getPCC s))"

lemma ExecutePropE [elim]:
  assumes "ExecuteProp s lbl s'"
      and "lbl \<noteq> SwitchDomain RaiseException"
      and "getStateIsValid s"
  shows "getTag (getPCC s)"
    and "\<not> getSealed (getPCC s)"
    and "Permit_Execute (getPerms (getPCC s))"
    and "getBase (getPCC s) + getPC s \<in> RegionOfCap (getPCC s)"
using assms
unfolding ExecuteProp_def
by auto

definition LoadDataProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "LoadDataProp s lbl s' \<equiv>
   \<forall>actions auth a l.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    LoadDataAction auth a l \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Load (getPerms (getCapReg auth s)) \<and>
    l \<noteq> 0 \<and>
    Region a l \<subseteq> getPhysicalAddresses (RegionOfCap (getCapReg auth s)) LOAD s)"

lemma LoadDataPropE [elim]:
  assumes "LoadDataProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "LoadDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Load (getPerms (getCapReg auth s))"
    and "l \<noteq> 0"
    and "Region a l \<subseteq> getPhysicalAddresses (RegionOfCap (getCapReg auth s)) LOAD s"
using assms
unfolding LoadDataProp_def
by auto

lemma LoadDataPropE_mem:
  assumes "LoadDataProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "LoadDataAction auth a l \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> Region a l"
  obtains vAddr 
  where "vAddr \<in> RegionOfCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, LOAD) s = Some a'"
using LoadDataPropE[OF assms(1-4)] assms(5)
by auto

definition StoreDataProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "StoreDataProp s lbl s' \<equiv>
   \<forall>actions auth a l.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    StoreDataAction auth a l \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Store (getPerms (getCapReg auth s)) \<and>
    l \<noteq> 0 \<and> 
    Region a l \<subseteq> getPhysicalAddresses (RegionOfCap (getCapReg auth s)) STORE s \<and>
    (\<not> getTag (getMemCap (GetCapAddress a) s') \<or> 
     getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s))"

lemma StoreDataPropE [elim]:
  assumes "StoreDataProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Store (getPerms (getCapReg auth s))"
    and "l \<noteq> 0"
    and "Region a l \<subseteq> getPhysicalAddresses (RegionOfCap (getCapReg auth s)) STORE s"
    and "getTag (getMemCap (GetCapAddress a) s') \<Longrightarrow>
         getMemCap (GetCapAddress a) s' = getMemCap (GetCapAddress a) s"
using assms
unfolding StoreDataProp_def
by auto

lemma StoreDataPropE_mem:
  assumes "StoreDataProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> Region a l"
  obtains vAddr 
  where "vAddr \<in> RegionOfCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, STORE) s = Some a'"
using StoreDataPropE[OF assms(1-4)] assms(5)
by auto

lemma StoreDataPropE_cap [elim]:
  assumes "StoreDataProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreDataAction auth a l \<in> actions"
      and "getStateIsValid s"
  shows "getMemCap (GetCapAddress a) s' \<le> getMemCap (GetCapAddress a) s"
using StoreDataPropE[OF assms] 
by (cases "getTag (getMemCap (GetCapAddress a) s')") auto

definition RestrictCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "RestrictCapProp s lbl s' \<equiv>
   \<forall>actions r r'.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    RestrictCapAction r r' \<in> actions) \<longrightarrow>
   getCapReg r' s' \<le> getCapReg r s"

lemma RestrictCapPropE [elim]:
  assumes "RestrictCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "RestrictCapAction r r' \<in> actions"
      and "getStateIsValid s"
  shows "getCapReg r' s' \<le> getCapReg r s"
using assms
unfolding RestrictCapProp_def
by auto

definition LoadCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "LoadCapProp s lbl s' \<equiv>
   \<forall>actions auth cd a.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    LoadCapAction auth a cd \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Load (getPerms (getCapReg auth s)) \<and>
    Permit_Load_Capability (getPerms (getCapReg auth s)) \<and>
    (Region (ExtendCapAddress a) 32 \<subseteq> 
     getPhysicalAddresses (RegionOfCap (getCapReg auth s)) LOAD s) \<and>
    getCAPR cd s' \<le> getMemCap a s)"

lemma LoadCapPropE [elim]:
  assumes "LoadCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "LoadCapAction auth a cd \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Load (getPerms (getCapReg auth s))"
    and "Permit_Load_Capability (getPerms (getCapReg auth s))"
    and "Region (ExtendCapAddress a) 32 \<subseteq> 
         getPhysicalAddresses (RegionOfCap (getCapReg auth s)) LOAD s"
    and "getCAPR cd s' \<le> getMemCap a s"
using assms
unfolding LoadCapProp_def
by auto

lemma LoadCapPropE_mem:
  assumes "LoadCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "LoadCapAction auth a cd \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> Region (ExtendCapAddress a) 32"
  obtains vAddr 
  where "vAddr \<in> RegionOfCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, LOAD) s = Some a'"
using LoadCapPropE[OF assms(1-4)] assms(5)
by auto

definition StoreCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "StoreCapProp s lbl s' \<equiv>
   \<forall>actions auth cd a.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    StoreCapAction auth cd a \<in> actions) \<longrightarrow>
   (getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Store (getPerms (getCapReg auth s)) \<and>
    Permit_Store_Capability (getPerms (getCapReg auth s)) \<and>
    (Region (ExtendCapAddress a) 32 \<subseteq> 
     getPhysicalAddresses (RegionOfCap (getCapReg auth s)) STORE s) \<and>
    getMemCap a s' = getCAPR cd s)"

lemma StoreCapPropE [elim]:
  assumes "StoreCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreCapAction auth cd a \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Store (getPerms (getCapReg auth s))"
    and "Permit_Store_Capability (getPerms (getCapReg auth s))"
    and "Region (ExtendCapAddress a) 32 \<subseteq> 
         getPhysicalAddresses (RegionOfCap (getCapReg auth s)) STORE s"
    and "getMemCap a s' = getCAPR cd s"
using assms
unfolding StoreCapProp_def
by auto

lemma StoreCapPropE_mem:
  assumes "StoreCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreCapAction auth cd a \<in> actions"
      and "getStateIsValid s"
      and "a' \<in> Region (ExtendCapAddress a) 32"
  obtains vAddr 
  where "vAddr \<in> RegionOfCap (getCapReg auth s)"
    and "getPhysicalAddress (vAddr, STORE) s = Some a'"
using StoreCapPropE[OF assms(1-4)] assms(5)
by auto

definition StoreLocalCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "StoreLocalCapProp s lbl s' \<equiv>
   \<forall>actions auth cd a.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    StoreCapAction auth cd a \<in> actions \<and>
    getTag (getCAPR cd s) \<and>
    \<not> Global (getPerms (getCAPR cd s))) \<longrightarrow>
   Permit_Store_Local_Capability (getPerms (getCapReg auth s))"

lemma StoreLocalCapPropE [elim]:
  assumes "StoreLocalCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "StoreCapAction auth cd a \<in> actions"
      and "getTag (getCAPR cd s)"
      and "\<not> Global (getPerms (getCAPR cd s))"
      and "getStateIsValid s"
  shows "Permit_Store_Local_Capability (getPerms (getCapReg auth s))"
using assms
unfolding StoreLocalCapProp_def
by auto

definition SealCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "SealCapProp s lbl s' \<equiv>
   \<forall>actions auth cd cd'.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    SealCapAction auth cd cd' \<in> actions) \<longrightarrow>
   (let t = ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s)) in
    getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    Permit_Seal (getPerms (getCapReg auth s)) \<and>
    ucast t \<in> RegionOfCap (getCapReg auth s) \<and>
    \<not> getSealed (getCAPR cd s) \<and>
    getCAPR cd' s' = setType (setSealed ((getCAPR cd s), True), t))"

lemma SealCapPropE [elim]:
  fixes s auth
  defines "t \<equiv> ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s))"
  assumes "SealCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "SealCapAction auth cd cd' \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Seal (getPerms (getCapReg auth s))"
    and "ucast t \<in> RegionOfCap (getCapReg auth s)"
    and  "\<not> getSealed (getCAPR cd s)"
    and "getCAPR cd' s' = setType (setSealed ((getCAPR cd s), True), t)"
using assms
unfolding SealCapProp_def Let_def
by auto

definition UnsealCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "UnsealCapProp s lbl s' \<equiv>
   \<forall>actions auth cd cd'.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    UnsealCapAction auth cd cd' \<in> actions) \<longrightarrow>
   (Permit_Unseal (getPerms (getCapReg auth s)) \<and>
    getTag (getCapReg auth s) \<and>
    \<not> getSealed (getCapReg auth s) \<and>
    ucast (getType (getCAPR cd s)) \<in> RegionOfCap (getCapReg auth s) \<and>
    getSealed (getCAPR cd s) \<and>
    getCAPR cd' s' \<le> setType (setSealed ((getCAPR cd s), False), 0))"

lemma UnsealCapPropE [elim]:
  assumes "UnsealCapProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "UnsealCapAction auth cd cd' \<in> actions"
      and "getStateIsValid s"
  shows "getTag (getCapReg auth s)"
    and "\<not> getSealed (getCapReg auth s)"
    and "Permit_Unseal (getPerms (getCapReg auth s))"
    and "ucast (getType (getCAPR cd s)) \<in> RegionOfCap (getCapReg auth s)"
    and "getSealed (getCAPR cd s)"
    and "getCAPR cd' s' \<le> setType (setSealed ((getCAPR cd s), False), 0)"
using assms
unfolding UnsealCapProp_def
by auto

definition SystemRegisterProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "SystemRegisterProp s lbl s' \<equiv>
   \<forall>actions cd.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>
    (cd \<noteq> 0 \<and> cd \<noteq> 1) \<and>
    cd \<in> \<Union> (CapDerivationRegisters ` actions)) \<longrightarrow>
   Access_System_Registers (getPerms (getPCC s))"

lemma SystemRegisterPropE [elim]:
  assumes "SystemRegisterProp s lbl s'"
      and "lbl = PreserveDomain actions"
      and "cd \<in> \<Union> (CapDerivationRegisters ` actions)"
      and "cd \<noteq> 0" "cd \<noteq> 1"
      and "getStateIsValid s"
  shows "Access_System_Registers (getPerms (getPCC s))"
using assms
unfolding SystemRegisterProp_def
by auto

definition InvokeCapProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "InvokeCapProp s lbl s' \<equiv>
   \<forall>cd cd'. 
   (getStateIsValid s \<and>
    (lbl = SwitchDomain (InvokeCapability cd cd'))) \<longrightarrow>
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
  assumes "InvokeCapProp s lbl s'"
      and "lbl = SwitchDomain (InvokeCapability cd cd')"
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
by auto

definition ExceptionProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "ExceptionProp s lbl s' \<equiv>
   (getStateIsValid s \<and>
    (lbl = SwitchDomain RaiseException)) \<longrightarrow>
   (getCP0StatusEXL s' \<and>
    getBase (getPCC s') + getPC s' \<in> ExceptionPCs \<and>
    getPCC s' = getKCC s \<and>
    (\<forall>cd. getCAPR cd s' = getCAPR cd s) \<and>
    (\<forall>cd. getSCAPR cd s' = SignalExceptionSCAPR cd s) \<and>
    (\<forall>a. getMEM a s' = getMEM a s) \<and>
    getBranchDelay s' = None \<and>
    BranchDelayPCC s' = None)"

lemma ExceptionPropE [elim]:
  assumes "ExceptionProp s lbl s'"
      and "lbl = SwitchDomain RaiseException"
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

definition MemoryInvariant :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "MemoryInvariant s lbl s' \<equiv>
   \<forall>actions a.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>   
    (\<nexists>prov. prov \<in> actions \<and> a \<in> WrittenAddresses prov)) \<longrightarrow>
   (getMemByte a s' = getMemByte a s)"

lemma MemoryInvariantE [elim]:
  assumes "MemoryInvariant s lbl s'"
      and "lbl = PreserveDomain actions"
      and "\<And>prov. prov \<in> actions \<Longrightarrow> a \<notin> WrittenAddresses prov"
      and "getStateIsValid s"
  shows "getMemByte a s' = getMemByte a s"
using assms
unfolding MemoryInvariant_def
by auto

definition CapabilityInvariant :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "CapabilityInvariant s lbl s' \<equiv>
   \<forall>actions loc.
   (getStateIsValid s \<and>
    (lbl = PreserveDomain actions) \<and>   
    (\<nexists>prov. prov \<in> actions \<and> loc \<in> CapDerivationTargets prov)) \<longrightarrow> 
   (getCap loc s' = getCap loc s)"

lemma CapabilityInvariantE [elim]:
  assumes "CapabilityInvariant s lbl s'"
      and "lbl = PreserveDomain actions"
      and "\<And>prov. prov \<in> actions \<Longrightarrow> loc \<notin> CapDerivationTargets prov"
      and "getStateIsValid s"
  shows "getCap loc s' = getCap loc s"
using assms
unfolding CapabilityInvariant_def
by auto

definition ValidStateProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "ValidStateProp s lbl s' \<equiv>
   getStateIsValid s \<longrightarrow>
   getStateIsValid s'"

lemma ValidStatePropE [elim]:
  assumes "ValidStateProp s lbl s'"
      and "getStateIsValid s"
  shows "getStateIsValid s'"
using assms
unfolding ValidStateProp_def
by auto

definition AddressTranslationProp :: "state \<Rightarrow> AbstractStep \<Rightarrow> state \<Rightarrow> bool" where
  "AddressTranslationProp s lbl s' \<equiv>
   \<forall>a.
   (getStateIsValid s \<and>
    \<not> Access_System_Registers (getPerms (getPCC s)) \<and>
    lbl \<noteq> SwitchDomain RaiseException) \<longrightarrow>
   getPhysicalAddress a s' = getPhysicalAddress a s"

lemma AddressTranslationPropE [elim]:
  assumes "AddressTranslationProp s lbl s'"
      and "lbl \<noteq> SwitchDomain RaiseException"
      and "\<not> Access_System_Registers (getPerms (getPCC s))"
      and "getStateIsValid s"
  shows "getPhysicalAddress a s' = getPhysicalAddress a s"
using assms
unfolding AddressTranslationProp_def
by fast+

definition AbstractSemantics :: Semantics where
  "AbstractSemantics s \<equiv> {(lbl, s') | lbl s'.  
   ExecuteProp s lbl s' \<and>
   LoadDataProp s lbl s' \<and>
   StoreDataProp s lbl s' \<and>
   RestrictCapProp s lbl s' \<and>
   LoadCapProp s lbl s' \<and>
   StoreCapProp s lbl s' \<and>
   StoreLocalCapProp s lbl s' \<and>
   SealCapProp s lbl s' \<and>
   UnsealCapProp s lbl s' \<and>
   SystemRegisterProp s lbl s' \<and> 
   InvokeCapProp s lbl s' \<and>
   ExceptionProp s lbl s' \<and>
   MemoryInvariant s lbl s' \<and>
   CapabilityInvariant s lbl s' \<and>
   ValidStateProp s lbl s' \<and>
   AddressTranslationProp s lbl s'}"

lemma AbstractSemanticsE [elim!]:
  assumes "(lbl, s') \<in> AbstractSemantics s"
  shows "ExecuteProp s lbl s'"
    and "LoadDataProp s lbl s'"
    and "StoreDataProp s lbl s'"
    and "RestrictCapProp s lbl s'"
    and "LoadCapProp s lbl s'"
    and "StoreCapProp s lbl s'"
    and "StoreLocalCapProp s lbl s'"
    and "SealCapProp s lbl s'"
    and "UnsealCapProp s lbl s'"
    and "SystemRegisterProp s lbl s'"
    and "InvokeCapProp s lbl s'"
    and "ExceptionProp s lbl s'"
    and "MemoryInvariant s lbl s'"
    and "CapabilityInvariant s lbl s'"
    and "ValidStateProp s lbl s'"
    and "AddressTranslationProp s lbl s'"
using assms
unfolding AbstractSemantics_def
by auto

definition CanBeSimulated :: "Semantics \<Rightarrow> bool" where
  "CanBeSimulated semantics \<equiv>
   \<forall>s lbl s'. (lbl, s') \<in> semantics s \<longrightarrow> (lbl, s') \<in> AbstractSemantics s"

lemma CanBeSimulatedE [elim!]:
  assumes "CanBeSimulated semantics"
      and "(lbl, s') \<in> semantics s"
  shows "(lbl, s') \<in> AbstractSemantics s"
using assms
unfolding CanBeSimulated_def
by auto

lemmas CanBeSimulatedE_Execute = ExecutePropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(1)]]
lemmas CanBeSimulatedE_LoadData = LoadDataPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(2)]]
lemmas CanBeSimulatedE_StoreData = StoreDataPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(3)]]
lemmas CanBeSimulatedE_RestrictRegCap = RestrictCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(4)]]
lemmas CanBeSimulatedE_LoadCap = LoadCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(5)]]
lemmas CanBeSimulatedE_StoreCap = StoreCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(6)]]
lemmas CanBeSimulatedE_StoreLocalCap = StoreLocalCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(7)]]
lemmas CanBeSimulatedE_SealCap = SealCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(8)]]
lemmas CanBeSimulatedE_UnsealCap = UnsealCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(9)]]
lemmas CanBeSimulatedE_SystemRegister = SystemRegisterPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(10)]]
lemmas CanBeSimulatedE_InvokeCap = InvokeCapPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(11)]]
lemmas CanBeSimulatedE_Exception = ExceptionPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(12)]]
lemmas CanBeSimulatedE_MemoryInvariant = MemoryInvariantE[OF CanBeSimulatedE[THEN AbstractSemanticsE(13)]]
lemmas CanBeSimulatedE_CapabilityInvariant = CapabilityInvariantE[OF CanBeSimulatedE[THEN AbstractSemanticsE(14)]]
lemmas CanBeSimulatedE_ValidState = ValidStatePropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(15)]]
lemmas CanBeSimulatedE_AddressTranslation = AddressTranslationPropE[OF CanBeSimulatedE[THEN AbstractSemanticsE(16)]]

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