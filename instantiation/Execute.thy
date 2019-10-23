(*<*) 

(* Author: Kyndylan Nienhuis *)

theory Execute

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Semantics of Execute\<close>

lemma DefinedNextInstruction:
  assumes suc: "(step, s') \<in> NextStates s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
      and pred: "\<not> isUnpredictable (StatePart NextWithGhostState s)"
  shows "getNextInstruction s \<noteq> None"
proof -
  have Run_ExceptionSignalled: "PrePost (return False) 
                                        (Run w) 
                                        (\<lambda>_. read_state getExceptionSignalled)" for w
    unfolding PrePost_def by auto
  have "PrePost (NextInstruction =\<^sub>b return None)
                NextWithGhostState
                (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                     read_state isUnpredictable)"
    unfolding NextWithGhostState_def
    by (PrePost intro: Run_ExceptionSignalled
                       UndefinedCase_TakeBranch 
                       UndefinedCase_Run
                       PrePost_Fetch[where p="\<lambda>x. return False",
                                     THEN PrePost_post_weakening])
  from PrePostE[where s=s, OF this]
  show ?thesis
    using assms
    unfolding NextStates_def 
    by (auto simp: ValueAndStatePart_simp split: if_splits)
qed

subsection \<open>Valid @{const PCC}\<close>

lemma TakeBranch_ValidPCC:
  shows "PrePost (read_state getExceptionSignalled \<and>\<^sub>b
                  \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                   (read_state BranchDelayPCC =\<^sub>b return None)))
                 TakeBranch
                 (\<lambda>_. (read_state getExceptionSignalled \<and>\<^sub>b
                       bind (read_state isUnpredictable) (\<lambda>x. return (\<not> x))))"
unfolding TakeBranch_def
by PrePost auto

lemma AddressTranslation_ValidPCC_aux:
  shows "PrePost (\<not>\<^sub>b read_state getExceptionSignalled \<and>\<^sub>b \<not>\<^sub>b read_state isUnpredictable)
                 (AddressTranslation v)
                 (\<lambda>_. \<not>\<^sub>b read_state getExceptionSignalled \<or>\<^sub>b \<not>\<^sub>b read_state isUnpredictable)"
unfolding AddressTranslation_alt_def
by PrePost auto?

lemma SignalException_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) (SignalException v)"
by PrePost+

lemma SignalCapException_noReg_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) (SignalCapException_noReg v)"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) (SignalCapException_noReg v)"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) (SignalCapException_noReg v)"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) (SignalCapException_noReg v)"
unfolding SignalCapException_noReg_alt_def SignalCapException_internal_alt_def
by (Invariant intro: SignalException_Branch)+

lemma SignalTLBException_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) (SignalTLBException v)"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) (SignalTLBException v)"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) (SignalTLBException v)"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) (SignalTLBException v)"
unfolding SignalTLBException_alt_def
by (Invariant intro: SignalException_Branch)+

lemma AddressTranslation_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) (AddressTranslation v)"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) (AddressTranslation v)"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) (AddressTranslation v)"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) (AddressTranslation v)"
unfolding AddressTranslation_alt_def
by (Invariant intro: SignalException_Branch 
                     SignalTLBException_Branch)+

lemma Fetch_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) Fetch"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) Fetch"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) Fetch"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) Fetch"
unfolding Fetch_alt_def
by (Invariant intro: SignalException_Branch 
                     SignalCapException_noReg_Branch 
                     AddressTranslation_Branch)+

lemma Fetch_ValidPCC_aux:
  shows "PrePost (\<not>\<^sub>b read_state isUnpredictable)
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled \<and>\<^sub>b
                                        \<not>\<^sub>b read_state isUnpredictable
                              | Some w \<Rightarrow> \<not>\<^sub>b read_state getExceptionSignalled \<or>\<^sub>b
                                          read_state isUnpredictable)"
unfolding Fetch_alt_def
by (PrePost intro: AddressTranslation_ValidPCC_aux[THEN PrePost_post_weakening])

lemma Fetch_ValidPCC_aux2:
  shows "PrePost ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
                  (read_state getPC =\<^sub>b return pc))
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> return True
                              | Some w \<Rightarrow> return (getTag pcc \<and> 
                                                  \<not> getSealed pcc \<and> 
                                                  pc + getBase pcc \<in> MemSegmentCap pcc \<and>
                                                  Permit_Execute (getPerms pcc)))"
proof -
  note memberI = MemSegment_memberI_65word[where y="4::65 word"]
  have intros: "PrePost (return x) 
                        (AddressTranslation v) 
                        (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b return x)" for x v
    using IsInvariant_constant[where m="AddressTranslation _", THEN PrePost_post_weakening]
    by auto
  show ?thesis
    unfolding Fetch_alt_def
    (* This proof step takes a long time *)
    by (PrePost intro: intros)
       (auto simp: not_le not_less intro!: memberI)
qed

lemma Fetch_ValidPCC:
  shows "PrePost ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
                  (read_state getPC =\<^sub>b return pc) \<and>\<^sub>b
                  \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                   (read_state BranchDelayPCC =\<^sub>b return None)))
                 Fetch                
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled \<and>\<^sub>b
                                        \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
                                        (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                                        (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                                        ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                                         (read_state BranchDelayPCC =\<^sub>b return None))
                              | Some w \<Rightarrow> return (getTag pcc \<and> 
                                                  \<not> getSealed pcc \<and> 
                                                  pc + getBase pcc \<in> MemSegmentCap pcc \<and>
                                                  Permit_Execute (getPerms pcc)))"
proof -
  note Fetch_Delay = PrePost_weakest_pre_disj[OF Fetch_Branch(3) Fetch_Branch(4)]
  note Fetch_Branches = PrePost_weakest_pre_conj
                        [OF PrePost_weakest_pre_conj[OF Fetch_Branch(1) Fetch_Branch(2)]
                            this]
  note intro = PrePost_weakest_pre_conj
               [OF PrePost_weakest_pre_conj[OF Fetch_ValidPCC_aux Fetch_ValidPCC_aux2]
                   this]
  show ?thesis
    by (intro PrePostIE[OF intro]) (auto simp add: ValueAndStatePart_simp)
qed

lemma NextWithGhostState_ValidPCC:
  shows "PrePost ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
                  (read_state getPC =\<^sub>b return pc) \<and>\<^sub>b
                  \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                   (read_state BranchDelayPCC =\<^sub>b return None)))
                 NextWithGhostState
                 (\<lambda>_. (read_state getExceptionSignalled \<and>\<^sub>b
                       \<not>\<^sub>b read_state isUnpredictable) \<or>\<^sub>b
                      return (getTag pcc \<and> 
                              \<not> getSealed pcc \<and> 
                              pc + getBase pcc \<in> MemSegmentCap pcc \<and>
                              Permit_Execute (getPerms pcc)))"
proof -
  have intro_run: "PrePost (return x) (Run w) (\<lambda>_. Q \<or>\<^sub>b return x)" for x w Q
    by (intro PrePostI) auto
  note intro_fetch = Fetch_ValidPCC[THEN PrePost_post_weakening]
  show ?thesis
    unfolding NextWithGhostState_def
    by (PrePost intro:  TakeBranch_ValidPCC intro_run intro_fetch)
qed

lemma SemanticsExecute:
  assumes suc: "(step, s') \<in> NextStates s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
      and valid: "getStateIsValid s"
  shows "getTag (getPCC s)"
    and "\<not> getSealed (getPCC s)"
    and "getBase (getPCC s) + getPC s \<in> MemSegmentCap (getPCC s)"
    and "Permit_Execute (getPerms (getPCC s))"
using assms
using NextWithGhostState_ValidPCC
      [where pcc="getPCC s" and pc="getPC s", THEN PrePostE[where s=s]]
unfolding NextStates_def
unfolding StateIsValid_def EmptyGhostState_def
by (auto simp: ValueAndStatePart_simp add.commute split: if_splits)

corollary ExecuteInstantiation [simp]:
  shows "ExecuteProp NextStates"
unfolding ExecuteProp_def
using SemanticsExecute
by auto

(*<*)
end
(*>*)