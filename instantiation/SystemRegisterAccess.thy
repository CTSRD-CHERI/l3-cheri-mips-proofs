(*<*) 

(* Author: Kyndylan Nienhuis *)

theory SystemRegisterAccess

imports 
  "ExecutionStep"
  "LoadData"
  "RestrictCap"
  "StoreData"
  "LoadCap"
  "StoreCap"
  "SealCap"
  "UnsealCap"
begin

(*>*)
section \<open>System register access\<close>

lemma NumberedRegisterIsAccessible:
  assumes reg: "cd \<in> \<Union> (SpecialRegisterParameters ` actions)"
      and valid: "getStateIsValid s"
      and suc: "(PreserveDomain actions, s') \<in> SemanticsCheriMips s"
  shows "getSpecial_register_accessible cd s"
proof -
  obtain ac where ac: "ac \<in> actions"
              and cd: "cd \<in> SpecialRegisterParameters ac"
    using reg
    by auto
  have ghost: "getGhostStateIsValid s"
    using valid by auto
  show ?thesis
    proof (cases ac)
      case (LoadDataAction auth a l)
      hence prov: "LoadDataAction auth a l \<in> actions"
        using ac by simp
      show ?thesis
        using SemanticsLoadData[OF prov valid suc]
        using cd LoadDataAction
        by (auto split: if_splits CapRegister.splits)
    next
      case (StoreDataAction auth a l)
      hence prov: "StoreDataAction auth a l \<in> actions"
        using ac by simp
      show ?thesis
        using SemanticsStoreData[OF prov suc valid]
        using cd StoreDataAction
        by (auto split: if_splits CapRegister.splits)
    next
      case (RestrictCapAction r r')
      hence prov: "RestrictCapAction r r' \<in> actions"
        using ac by simp
      show ?thesis
        using SemanticsRestrictCap[OF prov valid suc]
        using cd RestrictCapAction
        by (auto split: CapRegister.splits)
    next
      case (LoadCapAction auth a cd)
      hence prov: "LoadCapAction auth a cd \<in> actions"
        using ac by simp
      show ?thesis
        using SemanticsLoadCap[OF prov suc]
        using cd LoadCapAction
        by (auto split: CapRegister.splits)
    next
      case (StoreCapAction auth cd a)
      hence prov: "StoreCapAction auth cd a \<in> actions"
        using ac by simp
      show ?thesis 
        using SemanticsStoreCap[OF prov suc]
        using cd StoreCapAction
        by (auto split: CapRegister.splits)
    next
      case (SealCapAction auth cd cd')
      hence prov: "SealCapAction auth cd cd' \<in> actions"
        using ac by simp
      show ?thesis 
        using SemanticsSealCap[OF prov suc]
        using cd SealCapAction
        by (auto split: CapRegister.splits)
    next
      case (UnsealCapAction auth cd cd')
      hence prov: "UnsealCapAction auth cd cd' \<in> actions"
        using ac by simp
      show ?thesis 
        using SemanticsUnsealCap[OF prov suc]
        using cd UnsealCapAction
        by (auto split: CapRegister.splits)
    qed
qed

corollary SystemRegisterInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "SpecialRegisterProp s lbl s'"
unfolding SpecialRegisterProp_def
proof clarify
  fix actions action cd
  assume reg: "cd \<in> SpecialRegisterParameters action"
     and action: "action \<in> actions"
     and system: "cd \<noteq> 0" "cd \<noteq> 1"
     and valid: "getStateIsValid s"
     and lbl: "lbl = PreserveDomain actions"
  have suc: "(PreserveDomain actions, s') \<in> SemanticsCheriMips s"
    using assms lbl by auto
  have "cd \<in> \<Union> (SpecialRegisterParameters ` actions)"
    using reg action by auto
  from NumberedRegisterIsAccessible[OF this valid suc]
  show "Access_System_Registers (getPerms (getPCC s))"
    using system reg action
    unfolding special_register_accessible_alt_def
    by (auto simp: ValueAndStatePart_simp split: if_splits)
qed

(*<*)
end
(*>*)