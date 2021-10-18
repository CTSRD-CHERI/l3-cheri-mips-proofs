(*<*) 

(* Author: Kyndylan Nienhuis *)

theory SealCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const SealCapAction}\<close>

definition SemanticsSealPost where
  "SemanticsSealPost authCap cap cd' \<equiv> 
   let t = ucast (getBase authCap) + ucast (getOffset authCap) in 
   return (\<not> getSealed cap \<and> 
           Permit_Seal (getPerms authCap) \<and> 
           getTag authCap \<and>
           \<not> getSealed authCap \<and>
           ucast t \<in> RegionOfCap authCap) \<and>\<^sub>b
   bind (read_state (getCAPR cd'))
        (\<lambda>cap'. return (cap' = setType (setSealed (cap, True), t)))"

lemma Commute_SemanticsSealPost [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cd')) m"
  shows "Commute (SemanticsSealPost authCap cap cd') m"
unfolding SemanticsSealPost_def
by (Commute intro: assms)

lemma less_mask_eq_24:
  fixes w :: "'a::len word"
  assumes "w < 16777216"
  shows   "w AND mask 24 = w"
using assms
by (intro less_mask_eq) simp

lemma SemanticsSeal_CSeal:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CSealActions v) (\<lambda>prov. return (SealCapAction auth cd cd' \<in> prov)))
                 (dfn'CSeal v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsSealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
unfolding dfn'CSeal_alt_def CSealActions_def
unfolding SemanticsSealPost_def
by (PrePost intro: nonExceptionCase_exceptions[THEN PrePost_post_weakening])
   (auto simp: not_less not_le
               ucast_plus_down[THEN sym]
               Region_member_simp
               less_mask_eq_24
         split: if_splits)

lemma SemanticsSeal_Run_aux:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (SealCapAction auth cd cd' \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsSealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def PrePost_def
using PrePostE[OF SemanticsSeal_CSeal]
by (auto simp: ValueAndStatePart_simp split: all_split)

lemmas SemanticsSeal_Run =
  PrePost_weakest_pre_disj[OF SemanticsSeal_Run_aux
                              UndefinedCase_Run]

lemma SemanticsSeal_Fetch:
  fixes auth cd cd' authCap cap cdAccessible cd'Accessible authAccessible
  defines "p \<equiv> \<lambda>w. (return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                    (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>ac. return (SealCapAction auth cd cd' \<in> ac))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemma SemanticsSeal_NextWithGhostState:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>prov. return (SealCapAction auth cd cd' \<in> prov)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsSealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
proof -
  note intros = SemanticsSeal_Run[where cap=cap and authCap=authCap and
                                        auth=auth and cd=cd and cd'=cd' and
                                        authAccessible=authAccessible] 
                SemanticsSeal_Fetch[where cap=cap and authCap=authCap and
                                          auth=auth and cd=cd and cd'=cd' and
                                          authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (PrePost intro: intros[THEN PrePost_post_weakening] UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsSealCap:
  fixes s auth
  defines "t \<equiv> ucast (getBase (getCapReg auth s)) + ucast (getOffset (getCapReg auth s))"
  assumes prov: "SealCapAction auth cd cd' \<in> actions"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "Permit_Seal (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "ucast t \<in> RegionOfCap (getCapReg auth s)"
        "\<not> getSealed (getCAPR cd s)"
        "getRegisterIsAccessible auth s"
        "getCAPR cd' s' = setType (setSealed ((getCAPR cd s), True), t)"
using prov suc
using SemanticsSeal_NextWithGhostState
         [where cap="getCAPR cd s" and cd=cd and cd'=cd' and
                authCap="getCapReg auth s" and auth=auth and
                authAccessible="getRegisterIsAccessible auth s",
          THEN PrePostE[where s=s]]
unfolding t_def SemanticsSealPost_def Let_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary SealCapInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "SealCapProp s lbl s'"
unfolding SealCapProp_def
using assms SemanticsSealCap
by auto

(*<*)
end
(*>*)