(*<*) 

(* Author: Kyndylan Nienhuis *)

theory InvokeCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const InvokeCapability}}\<close>

definition SemanticsInvokePost where
  "SemanticsInvokePost codeCap dataCap capr scapr mem \<equiv>
   return (getSealed codeCap \<and>
           getSealed dataCap \<and>
           getTag codeCap \<and>
           getTag dataCap \<and>
           Permit_CCall (getPerms codeCap) \<and>
           Permit_CCall (getPerms dataCap) \<and>
           Permit_Execute (getPerms codeCap) \<and>
           \<not> Permit_Execute (getPerms dataCap) \<and>
           (getType codeCap = getType dataCap)) \<and>\<^sub>b
   (\<forall>\<^sub>bcd. read_state (getCAPR cd) =\<^sub>b 
          return (if cd = 26 
                  then setType (setSealed (dataCap, False), 0)
                  else capr cd)) \<and>\<^sub>b
   (\<forall>\<^sub>bcd. read_state (getSCAPR cd) =\<^sub>b return (scapr cd)) \<and>\<^sub>b
   (\<forall>\<^sub>ba. read_state (getMEM a) =\<^sub>b return (mem a))"

lemma Commute_SemanticsInvokePost [Commute_compositeI]:
  assumes "Commute (read_state getPCC) m"
  assumes "\<And>cd. Commute (read_state (getSCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>a. Commute (read_state (getMEM a)) m"
  shows "Commute (SemanticsInvokePost codeCap dataCap capr scapr mem) m"
unfolding SemanticsInvokePost_def
by (Commute intro: assms)

lemma SemanticsInvoke_CCallFast:
  shows "HoareTriple ((return codeCap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return dataCap =\<^sub>b read_state (getCAPR cd')) \<and>\<^sub>b
                  (return capr =\<^sub>b read_state (\<lambda>s cd. getCAPR cd s)) \<and>\<^sub>b
                  (return scapr =\<^sub>b read_state (\<lambda>s cd. getSCAPR cd s)) \<and>\<^sub>b
                  (return mem =\<^sub>b read_state (\<lambda>s a. getMEM a s)) \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  (return (v = (cd, cd'))))
                 (dfn'CCallFast v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      (SemanticsInvokePost codeCap dataCap capr scapr mem \<and>\<^sub>b
                       (read_state BranchDelayPCC =\<^sub>b 
                        return (Some (getOffset codeCap, setType (setSealed (codeCap, False), 0)))) \<and>\<^sub>b
                       (read_state getBranchDelay =\<^sub>b return None) \<and>\<^sub>b
                       (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchToPCC =\<^sub>b return None)))"
unfolding dfn'CCallFast_alt_def SemanticsInvokePost_def
unfolding CheckBranch_alt_def
by (HoareTriple intro: nonExceptionCase_exceptions[THEN HoareTriple_post_weakening]) auto

lemma SemanticsInvoke_Run_aux:
  shows "HoareTriple ((return codeCap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return dataCap =\<^sub>b read_state (getCAPR cd')) \<and>\<^sub>b
                  (return capr =\<^sub>b read_state (\<lambda>s cd. getCAPR cd s)) \<and>\<^sub>b
                  (return scapr =\<^sub>b read_state (\<lambda>s cd. getSCAPR cd s)) \<and>\<^sub>b
                  (return mem =\<^sub>b read_state (\<lambda>s a. getMEM a s)) \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  (return (case v of COP2 (CHERICOP2 (CCallFast (cs, cb))) \<Rightarrow> (cs = cd) \<and> (cb = cd')
                                   | _ \<Rightarrow> False)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      (SemanticsInvokePost codeCap dataCap capr scapr mem \<and>\<^sub>b
                       (read_state BranchDelayPCC =\<^sub>b 
                        return (Some (getOffset codeCap, setType (setSealed (codeCap, False), 0)))) \<and>\<^sub>b
                       (read_state getBranchDelay =\<^sub>b return None) \<and>\<^sub>b
                       (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchToPCC =\<^sub>b return None)))"
unfolding Run_alt_def RunActions_def HoareTriple_def
using HoareTripleE[OF SemanticsInvoke_CCallFast]
by (auto simp: ValueAndStatePart_simp split: all_split)

lemmas SemanticsInvoke_Run =
  HoareTriple_weakest_pre_disj[OF SemanticsInvoke_Run_aux
                              UndefinedCase_Run]

lemma SemanticsInvoke_Fetch:
  fixes codeCap dataCap cd cd' capr scapr mem
  defines "p \<equiv> \<lambda>w. (return codeCap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                   (return dataCap =\<^sub>b read_state (getCAPR cd')) \<and>\<^sub>b
                   (return capr =\<^sub>b read_state (\<lambda>s cd. getCAPR cd s)) \<and>\<^sub>b
                   (return scapr =\<^sub>b read_state (\<lambda>s cd. getSCAPR cd s)) \<and>\<^sub>b
                   (return mem =\<^sub>b read_state (\<lambda>s a. getMEM a s)) \<and>\<^sub>b
                   (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                   (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                   (return (case Decode w of COP2 (CHERICOP2 (CCallFast (cs, cb))) \<Rightarrow> 
                                             (cs = cd) \<and> (cb = cd')
                                           | _ \<Rightarrow> False))"
  shows "HoareTriple (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro HoareTriple_Fetch[THEN HoareTriple_post_weakening]) Commute+

lemma SemanticsInvoke_TakeBranch:
  shows "HoareTriple (read_state getExceptionSignalled \<or>\<^sub>b
                  read_state isUnpredictable \<or>\<^sub>b
                  (SemanticsInvokePost codeCap dataCap capr scapr mem \<and>\<^sub>b
                   (read_state getBranchDelay =\<^sub>b return None) \<and>\<^sub>b
                   (read_state BranchDelayPCC =\<^sub>b 
                    return (Some (getOffset codeCap, setType (setSealed (codeCap, False), 0)))) \<and>\<^sub>b
                   (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                   (read_state BranchToPCC =\<^sub>b return None)))
                 TakeBranch
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      (SemanticsInvokePost codeCap dataCap capr scapr mem \<and>\<^sub>b
                       bind (read_state getPCC) 
                            (\<lambda>x. return (x = setType (setSealed (codeCap, False), 0))) \<and>\<^sub>b
                       (read_state getBranchDelay =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchDelayPCC =\<^sub>b return None) \<and>\<^sub>b
                       bind (read_state getPC) 
                            (\<lambda>x. return (x = getOffset codeCap))))"
unfolding TakeBranch_def SemanticsInvokePost_def
by HoareTriple (auto split: option.splits)

lemma SemanticsInvoke_NextWithGhostState:
  shows "HoareTriple ((return codeCap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return dataCap =\<^sub>b read_state (getCAPR cd')) \<and>\<^sub>b
                  (return capr =\<^sub>b read_state (\<lambda>s cd. getCAPR cd s)) \<and>\<^sub>b
                  (return scapr =\<^sub>b read_state (\<lambda>s cd. getSCAPR cd s)) \<and>\<^sub>b
                  (return mem =\<^sub>b read_state (\<lambda>s a. getMEM a s)) \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  (read_state NextNonExceptionStep =\<^sub>b 
                   return (SwitchDomain (InvokeCapability cd cd'))))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      (SemanticsInvokePost codeCap dataCap capr scapr mem \<and>\<^sub>b
                       bind (read_state getPCC) 
                            (\<lambda>x. return (x = setType (setSealed (codeCap, False), 0))) \<and>\<^sub>b
                       (read_state getBranchDelay =\<^sub>b return None) \<and>\<^sub>b
                       (read_state BranchDelayPCC =\<^sub>b return None) \<and>\<^sub>b
                       bind (read_state getPC) 
                            (\<lambda>x. return (x = getOffset codeCap))))"
proof -
  note intros = SemanticsInvoke_TakeBranch[where codeCap=codeCap and dataCap=dataCap]
                SemanticsInvoke_Run[where codeCap=codeCap and dataCap=dataCap and
                                          cd=cd and cd'=cd'] 
                SemanticsInvoke_Fetch[where codeCap=codeCap and dataCap=dataCap and
                                            cd=cd and cd'=cd']
  show ?thesis
    unfolding NextWithGhostState_def 
    unfolding NextNonExceptionStep_def DomainActions_def
    by (HoareTriple intro: intros[THEN HoareTriple_post_weakening])
       (auto split: option.splits elim!: CCallFastInstructionParam_Some)
qed

theorem SemanticsInvokeCap:
  fixes s cd cd'
  defines "CodeCap \<equiv> getCAPR cd s"
  defines "DataCap \<equiv> getCAPR cd' s"
  assumes valid: "getStateIsValid s"
      and suc: "(SwitchDomain (InvokeCapability cd cd'), s') \<in> SemanticsCheriMips s"
  shows "getSealed CodeCap"
    and "getSealed DataCap"
    and "getTag CodeCap"
    and "getTag DataCap"
    and "Permit_CCall (getPerms CodeCap)"
    and "Permit_CCall (getPerms DataCap)"
    and "Permit_Execute (getPerms CodeCap)"
    and "\<not> Permit_Execute (getPerms DataCap)"
    and "getType CodeCap = getType DataCap"
    and "getPC s' = getOffset CodeCap"
    and "getPCC s' = setType (setSealed (CodeCap, False), 0)"
    and "getBranchDelay s' = None"
    and "BranchDelayPCC s' = None"
    and "\<And>x. getCAPR x s' = (if x = 26 then setType (setSealed (DataCap, False), 0)
                             else getCAPR x s)"
    and "\<And>x. getSCAPR x s' = getSCAPR x s"
    and "\<And>x. getMEM x s' = getMEM x s"
using suc valid
using SemanticsInvoke_NextWithGhostState
         [where codeCap=CodeCap and dataCap=DataCap and cd=cd and cd'=cd' and
                capr="\<lambda>cd. getCAPR cd s" and scapr="\<lambda>cd. getSCAPR cd s" and
                mem="\<lambda>a. getMEM a s",
          THEN HoareTripleE[where s=s]]
unfolding CodeCap_def DataCap_def SemanticsInvokePost_def
unfolding SemanticsCheriMips_def Next_NextWithGhostState
unfolding StateIsValid_def GhostStateIsValid_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

corollary InvokeCapInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "InvokeCapProp s lbl s'"
unfolding InvokeCapProp_def
using assms SemanticsInvokeCap
by auto

(*<*)
end
(*>*)