(*<*) 

(* Author: Kyndylan Nienhuis *)

theory CheriInstantiation

imports 
  "ExecutionStep"
  "ValidState"
  "AddressTranslation"
  "Execute"
  "LoadData"
  "StoreData"
  "RestrictCap"
  "LoadCap"
  "StoreCap"
  "SealCap"
  "UnsealCap"
  "Exception"
  "InvokeCap"
  "MemoryInvariant"
  "CapabilityInvariant"
  "SystemRegisterAccess"
begin

(*>*)

theorem CheriInstantiation:
  shows "CanBeSimulated SemanticsCheriMips"
unfolding CanBeSimulated_def
proof clarify
  fix s lbl s'
  assume as: "(lbl, s') \<in> SemanticsCheriMips s"
  show "(lbl, s') \<in> AbstractSemantics s"
    unfolding AbstractSemantics_def
    using AddressTranslationInstantiation[OF as]
    using ExceptionInstantiation[OF as]
    using ExecuteInstantiation[OF as]
    using CapabilityInvariantInstantiation[OF as]
    using InvokeCapInstantiation[OF as]
    using LoadCapInstantiation[OF as]
    using LoadDataInstantiation[OF as]
    using MemoryInvariantInstantiation[OF as]
    using RestrictCapInstantiation[OF as]
    using SealCapInstantiation[OF as]
    using StoreCapInstantiation[OF as]
    using StoreLocalCapInstantiation[OF as]
    using StoreDataInstantiation[OF as]
    using UnsealCapInstantiation[OF as]
    using SystemRegisterInstantiation[OF as]
    using ValidStateInstantiation[OF as]
    by auto
qed

(*<*)
end
(*>*)