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
  assumes suc: "(step, s') \<in> SemanticsCheriMips s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
      and pred: "\<not> isUnpredictable (StatePart NextWithGhostState s)"
  shows "getNextInstruction s \<noteq> None"
proof -
  have Run_ExceptionSignalled: "HoareTriple (return False) 
                                        (Run w) 
                                        (\<lambda>_. read_state getExceptionSignalled)" for w
    unfolding HoareTriple_def by auto
  have "HoareTriple (NextInstruction =\<^sub>b return None)
                NextWithGhostState
                (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                     read_state isUnpredictable)"
    unfolding NextWithGhostState_def
    by (HoareTriple intro: Run_ExceptionSignalled
                       UndefinedCase_TakeBranch 
                       UndefinedCase_Run
                       HoareTriple_Fetch[where p="\<lambda>x. return False",
                                     THEN HoareTriple_post_weakening])
  from HoareTripleE[where s=s, OF this]
  show ?thesis
    using assms
    unfolding SemanticsCheriMips_def 
    by (auto simp: ValueAndStatePart_simp split: if_splits)
qed

subsection \<open>Valid @{const PCC}\<close>

lemma TakeBranch_ValidPCC:
  shows "HoareTriple (read_state getExceptionSignalled \<and>\<^sub>b
                  \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
                  (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
                  (read_state BranchToPCC =\<^sub>b return None) \<and>\<^sub>b
                  ((read_state getBranchDelay =\<^sub>b return None) \<or>\<^sub>b
                   (read_state BranchDelayPCC =\<^sub>b return None)))
                 TakeBranch
                 (\<lambda>_. (read_state getExceptionSignalled \<and>\<^sub>b
                       bind (read_state isUnpredictable) (\<lambda>x. return (\<not> x))))"
unfolding TakeBranch_def
by HoareTriple auto

lemma AddressTranslation_ValidPCC_aux:
  shows "HoareTriple (\<not>\<^sub>b read_state getExceptionSignalled \<and>\<^sub>b \<not>\<^sub>b read_state isUnpredictable)
                 (AddressTranslation v)
                 (\<lambda>_. \<not>\<^sub>b read_state getExceptionSignalled \<or>\<^sub>b \<not>\<^sub>b read_state isUnpredictable)"
unfolding AddressTranslation_alt_def
by HoareTriple auto?

lemma SignalException_Branch:
  shows "IsInvariant (read_state getBranchTo =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state BranchToPCC =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state getBranchDelay =\<^sub>b return None) (SignalException v)"
        "IsInvariant (read_state BranchDelayPCC =\<^sub>b return None) (SignalException v)"
by HoareTriple+

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
  shows "HoareTriple (\<not>\<^sub>b read_state isUnpredictable)
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled \<and>\<^sub>b
                                        \<not>\<^sub>b read_state isUnpredictable
                              | Some w \<Rightarrow> \<not>\<^sub>b read_state getExceptionSignalled \<or>\<^sub>b
                                          read_state isUnpredictable)"
unfolding Fetch_alt_def
by (HoareTriple intro: AddressTranslation_ValidPCC_aux[THEN HoareTriple_post_weakening])

lemma Fetch_ValidPCC_aux2:
  shows "HoareTriple ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
                  (read_state getPC =\<^sub>b return pc))
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> return True
                              | Some w \<Rightarrow> return (getTag pcc \<and> 
                                                  \<not> getSealed pcc \<and> 
                                                  pc + getBase pcc \<in> RegionOfCap pcc \<and>
                                                  Permit_Execute (getPerms pcc)))"
proof -
  note memberI = Region_memberI_65word[where y="4::65 word"]
  have intros: "HoareTriple (return x) 
                        (AddressTranslation v) 
                        (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b return x)" for x v
    using IsInvariant_constant[where m="AddressTranslation _", THEN HoareTriple_post_weakening]
    by auto
  show ?thesis
    unfolding Fetch_alt_def
    (* This proof step takes a long time *)
    by (HoareTriple intro: intros)
       (auto simp: not_le not_less intro!: memberI)
qed

lemma Fetch_ValidPCC:
  shows "HoareTriple ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
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
                                                  pc + getBase pcc \<in> RegionOfCap pcc \<and>
                                                  Permit_Execute (getPerms pcc)))"
proof -
  note Fetch_Delay = HoareTriple_weakest_pre_disj[OF Fetch_Branch(3) Fetch_Branch(4)]
  note Fetch_Branches = HoareTriple_weakest_pre_conj
                        [OF HoareTriple_weakest_pre_conj[OF Fetch_Branch(1) Fetch_Branch(2)]
                            this]
  note intro = HoareTriple_weakest_pre_conj
               [OF HoareTriple_weakest_pre_conj[OF Fetch_ValidPCC_aux Fetch_ValidPCC_aux2]
                   this]
  show ?thesis
    by (intro HoareTripleIE[OF intro]) (auto simp add: ValueAndStatePart_simp)
qed

lemma NextWithGhostState_ValidPCC:
  shows "HoareTriple ((read_state getPCC =\<^sub>b return pcc) \<and>\<^sub>b
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
                              pc + getBase pcc \<in> RegionOfCap pcc \<and>
                              Permit_Execute (getPerms pcc)))"
proof -
  have intro_run: "HoareTriple (return x) (Run w) (\<lambda>_. Q \<or>\<^sub>b return x)" for x w Q
    by (intro HoareTripleI) auto
  note intro_fetch = Fetch_ValidPCC[THEN HoareTriple_post_weakening]
  show ?thesis
    unfolding NextWithGhostState_def
    by (HoareTriple intro:  TakeBranch_ValidPCC intro_run intro_fetch)
qed

lemma SemanticsExecute:
  assumes suc: "(step, s') \<in> SemanticsCheriMips s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
      and valid: "getStateIsValid s"
  shows "getTag (getPCC s)"
    and "\<not> getSealed (getPCC s)"
    and "getBase (getPCC s) + getPC s \<in> RegionOfCap (getPCC s)"
    and "Permit_Execute (getPerms (getPCC s))"
using assms
using NextWithGhostState_ValidPCC
      [where pcc="getPCC s" and pc="getPC s", THEN HoareTripleE[where s=s]]
unfolding SemanticsCheriMips_def
unfolding StateIsValid_def GhostStateIsValid_def
by (auto simp: ValueAndStatePart_simp add.commute split: if_splits)

corollary ExecuteInstantiation:
  assumes "(lbl, s') \<in> SemanticsCheriMips s"
  shows "ExecuteProp s lbl s'"
unfolding ExecuteProp_def
using assms SemanticsExecute
by auto

(*<*)
end
(*>*)