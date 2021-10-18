(*<*) 

(* Author: Kyndylan Nienhuis *)

theory UnsealCap

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of @{const UnsealCapAction}\<close>

definition SemanticsUnsealPost where
  "SemanticsUnsealPost authCap cap cd' \<equiv> 
   return (getSealed cap \<and> 
           Permit_Unseal (getPerms authCap) \<and> 
           getTag authCap \<and>
           \<not> getSealed authCap \<and>
           ucast (getType cap) \<in> RegionOfCap authCap) \<and>\<^sub>b
   bind (read_state (getCAPR cd'))
        (\<lambda>cap'. return (cap' \<le> setType (setSealed (cap, False), 0)))"

lemma Commute_SemanticsUnsealPost [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cd')) m"
  shows "Commute (SemanticsUnsealPost authCap cap cd') m"
unfolding SemanticsUnsealPost_def
by (Commute intro: assms)

lemma SemanticsUnseal_CUnseal_aux:
  fixes x y z :: "'a::len0 word"
  shows "(x + y = z) \<longleftrightarrow> (z - x = y)"
by auto

lemma SemanticsUnseal_CUnseal:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (CUnsealActions v) (\<lambda>prov. return (UnsealCapAction auth cd cd' \<in> prov)))
                 (dfn'CUnseal v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsUnsealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
unfolding dfn'CUnseal_alt_def CUnsealActions_def 
unfolding SemanticsUnsealPost_def
by (PrePost intro: nonExceptionCase_exceptions[THEN PrePost_post_weakening])
   (auto simp: not_less not_le setPerms_le
               Region_member_simp
               SemanticsUnseal_CUnseal_aux
         split: if_splits
         elim!: notE[OF _ rec'Perms_AND_leq_forget_right])

lemma SemanticsUnseal_Run_aux:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind (RunActions v) (\<lambda>prov. return (UnsealCapAction auth cd cd' \<in> prov)))
                 (Run v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsUnsealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
unfolding Run_alt_def RunActions_def PrePost_def
using PrePostE[OF SemanticsUnseal_CUnseal]
by (auto simp: ValueAndStatePart_simp split: all_split)

lemmas SemanticsUnseal_Run =
  PrePost_weakest_pre_disj[OF SemanticsUnseal_Run_aux
                              UndefinedCase_Run]

lemma SemanticsUnseal_Fetch:
  fixes auth cd cd' authCap cap cdAccessible cd'Accessible authAccessible
  defines "p \<equiv> \<lambda>w. (return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                    (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                    (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                    bind (RunActions (Decode w)) (\<lambda>ac. return (UnsealCapAction auth cd cd' \<in> ac))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                  Fetch
                  (\<lambda>b. case b of None \<Rightarrow> read_state getExceptionSignalled
                               | Some y \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p y)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemma SemanticsUnseal_NextWithGhostState:
  shows "PrePost ((return cap =\<^sub>b read_state (getCAPR cd)) \<and>\<^sub>b
                  (return authCap =\<^sub>b read_state (getCapReg auth)) \<and>\<^sub>b
                  (return authAccessible =\<^sub>b read_state (getRegisterIsAccessible auth)) \<and>\<^sub>b
                  bind DomainActions (\<lambda>prov. return (UnsealCapAction auth cd cd' \<in> prov)))
                 NextWithGhostState
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      SemanticsUnsealPost authCap cap cd' \<and>\<^sub>b
                      return authAccessible)"
proof -
  note intros = SemanticsUnseal_Run[where cap=cap and authCap=authCap and
                                          auth=auth and cd=cd and cd'=cd' and
                                          authAccessible=authAccessible] 
                SemanticsUnseal_Fetch[where cap=cap and authCap=authCap and
                                            auth=auth and cd=cd and cd'=cd' and
                                            authAccessible=authAccessible]
  show ?thesis
    unfolding NextWithGhostState_def DomainActions_def
    by (PrePost intro: intros[THEN PrePost_post_weakening] UndefinedCase_TakeBranch)
       (auto split: option.splits)
qed

theorem SemanticsUnsealCap:
  assumes prov: "UnsealCapAction auth cd cd' \<in> actions"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "Permit_Unseal (getPerms (getCapReg auth s))"
        "getTag (getCapReg auth s)"
        "\<not> getSealed (getCapReg auth s)"
        "ucast (getType (getCAPR cd s)) \<in> RegionOfCap (getCapReg auth s)"
        "getSealed (getCAPR cd s)"
        "getRegisterIsAccessible auth s"
        "getCAPR cd' s' \<le> setType (setSealed ((getCAPR cd s), False), 0)"
using assms
using SemanticsUnseal_NextWithGhostState
         [where cap="getCAPR cd s" and cd=cd and cd'=cd' and
                authCap="getCapReg auth s" and auth=auth and
                authAccessible="getRegisterIsAccessible auth s",
          THEN PrePostE[where s=s]]
unfolding SemanticsUnsealPost_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary UnsealCapInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "UnsealCapProp s lbl s'"
unfolding UnsealCapProp_def
using assms SemanticsUnsealCap
by auto

(*<*)
end
(*>*)