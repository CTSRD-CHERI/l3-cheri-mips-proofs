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

corollary CheriInstantiation [simp]:
  shows "CheriAbstraction NextStates"
unfolding CheriAbstraction_def
by simp

(*<*)
end
(*>*)