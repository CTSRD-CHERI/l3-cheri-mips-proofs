(*<*) 

(* Author: Kyndylan Nienhuis *)

theory ExecutionStep

imports 
  "CHERI-core.CheriLemmas"
  "CHERI-abstraction.CheriAbstraction"
begin
 
(*>*)
section \<open>Domain actions\<close>

subsection \<open>Capbility manipulations\<close>

subsubsection \<open>@{const CAndPerm}\<close>

thm dfn'CAndPerm_alt_def

definition CAndPermActions where
  "CAndPermActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCAndPermActions where
  "getCAndPermActions v \<equiv> ValuePart (CAndPermActions v)"

lemma CAndPermActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CAndPermActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CAndPermActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CAndPermActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CAndPermActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CAndPermActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CAndPermActions v) s"
unfolding CAndPermActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CAndPermActions_StatePart [simp]:
  shows "StatePart (CAndPermActions v) = (\<lambda>s. s)"
unfolding CAndPermActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CAndPermActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CAndPermActions v) m"
unfolding CAndPermActions_def
by (cases v) simp

subsubsection \<open>@{const CBuildCap}\<close>

thm dfn'CBuildCap_alt_def

definition CBuildCapActions where
  "CBuildCapActions \<equiv> \<lambda>(cd, cb, ct). 
   return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCBuildCapActions where
  "getCBuildCapActions v \<equiv> ValuePart (CBuildCapActions v)"

lemma CBuildCapActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CBuildCapActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CBuildCapActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CBuildCapActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CBuildCapActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CBuildCapActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CBuildCapActions v) s"
unfolding CBuildCapActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CBuildCapActions_StatePart [simp]:
  shows "StatePart (CBuildCapActions v) = (\<lambda>s. s)"
unfolding CBuildCapActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CBuildCapActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CBuildCapActions v) m"
unfolding CBuildCapActions_def
by auto

subsubsection \<open>@{const CClearHi}\<close>

thm dfn'CClearHi_alt_def

definition CClearHiActions where
  "CClearHiActions \<equiv> \<lambda>mask. 
   return ((\<lambda>cd. RestrictCapAction (RegNormal cd) (RegNormal cd)) ` 
                 {cd. mask !! (unat (cd - 16))})"

abbreviation getCClearHiActions where
  "getCClearHiActions v \<equiv> ValuePart (CClearHiActions v)"

lemma CClearHiActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CClearHiActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CClearHiActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CClearHiActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CClearHiActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CClearHiActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CClearHiActions v) s"
unfolding CClearHiActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CClearHiActions_StatePart [simp]:
  shows "StatePart (CClearHiActions v) = (\<lambda>s. s)"
unfolding CClearHiActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CClearHiActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CClearHiActions v) m"
unfolding CClearHiActions_def
by simp

subsubsection \<open>@{const CClearLo}\<close>

thm dfn'CClearLo_alt_def

definition CClearLoActions where
  "CClearLoActions \<equiv> \<lambda>mask. 
   return ((\<lambda>cd. RestrictCapAction (RegNormal cd) (RegNormal cd)) ` 
                 {cd. mask !! (unat cd)})"

abbreviation getCClearLoActions where
  "getCClearLoActions v \<equiv> ValuePart (CClearLoActions v)"

lemma CClearLoActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CClearLoActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CClearLoActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CClearLoActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CClearLoActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CClearLoActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CClearLoActions v) s"
unfolding CClearLoActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CClearLoActions_StatePart [simp]:
  shows "StatePart (CClearLoActions v) = (\<lambda>s. s)"
unfolding CClearLoActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CClearLoActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CClearLoActions v) m"
unfolding CClearLoActions_def
by simp

subsubsection \<open>@{const CClearTag}\<close>

thm dfn'CClearTag_alt_def

definition CClearTagActions where
  "CClearTagActions \<equiv> \<lambda>(cd, cb). return {RestrictCapAction (RegNormal cd) (RegNormal cd)}"

abbreviation getCClearTagActions where
  "getCClearTagActions v \<equiv> ValuePart (CClearTagActions v)"

lemma CClearTagActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CClearTagActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CClearTagActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CClearTagActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CClearTagActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CClearTagActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CClearTagActions v) s"
unfolding CClearTagActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CClearTagActions_StatePart [simp]:
  shows "StatePart (CClearTagActions v) = (\<lambda>s. s)"
unfolding CClearTagActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CClearTagActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CClearTagActions v) m"
unfolding CClearTagActions_def
by (cases v) simp

subsubsection \<open>@{const CCopyType}\<close>

thm dfn'CCopyType_alt_def

definition CCopyTypeActions where
  "CCopyTypeActions \<equiv> \<lambda>(cd, cb, ct). 
   return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCCopyTypeActions where
  "getCCopyTypeActions v \<equiv> ValuePart (CCopyTypeActions v)"

lemma CCopyTypeActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CCopyTypeActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CCopyTypeActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CCopyTypeActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CCopyTypeActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CCopyTypeActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CCopyTypeActions v) s"
unfolding CCopyTypeActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CCopyTypeActions_StatePart [simp]:
  shows "StatePart (CCopyTypeActions v) = (\<lambda>s. s)"
unfolding CCopyTypeActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CCopyTypeActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CCopyTypeActions v) m"
unfolding CCopyTypeActions_def
by auto

subsubsection \<open>@{const CFromPtr}\<close>

thm dfn'CFromPtr_alt_def

definition CFromPtrActions where
  "CFromPtrActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCFromPtrActions where
  "getCFromPtrActions v \<equiv> ValuePart (CFromPtrActions v)"

lemma CFromPtrActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CFromPtrActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CFromPtrActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CFromPtrActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CFromPtrActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CFromPtrActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CFromPtrActions v) s"
unfolding CFromPtrActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CFromPtrActions_StatePart [simp]:
  shows "StatePart (CFromPtrActions v) = (\<lambda>s. s)"
unfolding CFromPtrActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CFromPtrActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CFromPtrActions v) m"
unfolding CFromPtrActions_def
by (cases v) simp

subsubsection \<open>@{const CGetPCC}\<close>

thm dfn'CGetPCC_alt_def

definition CGetPCCActions where
  "CGetPCCActions \<equiv> \<lambda>cd. return {RestrictCapAction RegPCC (RegNormal cd)}"

abbreviation getCGetPCCActions where
  "getCGetPCCActions v \<equiv> ValuePart (CGetPCCActions v)"

lemma CGetPCCActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CGetPCCActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CGetPCCActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CGetPCCActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CGetPCCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CGetPCCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CGetPCCActions v) s"
unfolding CGetPCCActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CGetPCCActions_StatePart [simp]:
  shows "StatePart (CGetPCCActions v) = (\<lambda>s. s)"
unfolding CGetPCCActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CGetPCCActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CGetPCCActions v) m"
unfolding CGetPCCActions_def
by (cases v) simp

subsubsection \<open>@{const CGetPCCSetOffset}\<close>

thm dfn'CGetPCCSetOffset_alt_def

definition CGetPCCSetOffsetActions where
  "CGetPCCSetOffsetActions \<equiv> \<lambda>(cd, rs). return {RestrictCapAction RegPCC (RegNormal cd)}"

abbreviation getCGetPCCSetOffsetActions where
  "getCGetPCCSetOffsetActions v \<equiv> ValuePart (CGetPCCSetOffsetActions v)"

lemma CGetPCCSetOffsetActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CGetPCCSetOffsetActions v) s"
unfolding CGetPCCSetOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CGetPCCSetOffsetActions_StatePart [simp]:
  shows "StatePart (CGetPCCSetOffsetActions v) = (\<lambda>s. s)"
unfolding CGetPCCSetOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CGetPCCSetOffsetActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CGetPCCSetOffsetActions v) m"
unfolding CGetPCCSetOffsetActions_def
by (cases v) simp

subsubsection \<open>@{const CIncOffset}\<close>

thm dfn'CIncOffset_alt_def

definition CIncOffsetActions where
  "CIncOffsetActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCIncOffsetActions where
  "getCIncOffsetActions v \<equiv> ValuePart (CIncOffsetActions v)"

lemma CIncOffsetActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CIncOffsetActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CIncOffsetActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CIncOffsetActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CIncOffsetActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CIncOffsetActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CIncOffsetActions v) s"
unfolding CIncOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CIncOffsetActions_StatePart [simp]:
  shows "StatePart (CIncOffsetActions v) = (\<lambda>s. s)"
unfolding CIncOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CIncOffsetActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CIncOffsetActions v) m"
unfolding CIncOffsetActions_def
by (cases v) simp

subsubsection \<open>@{const CIncOffsetImmediate}\<close>

thm dfn'CIncOffsetImmediate_alt_def

definition CIncOffsetImmediateActions where
  "CIncOffsetImmediateActions \<equiv> \<lambda>(cd, cb, increment). 
   return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCIncOffsetImmediateActions where
  "getCIncOffsetImmediateActions v \<equiv> ValuePart (CIncOffsetImmediateActions v)"

lemma CIncOffsetImmediateActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CIncOffsetImmediateActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CIncOffsetImmediateActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CIncOffsetImmediateActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CIncOffsetImmediateActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CIncOffsetImmediateActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CIncOffsetImmediateActions v) s"
unfolding CIncOffsetImmediateActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CIncOffsetImmediateActions_StatePart [simp]:
  shows "StatePart (CIncOffsetImmediateActions v) = (\<lambda>s. s)"
unfolding CIncOffsetImmediateActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CIncOffsetImmediateActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CIncOffsetImmediateActions v) m"
unfolding CIncOffsetImmediateActions_def
by (cases v) simp

subsubsection \<open>@{const CJALR}\<close>

thm dfn'CJALR_alt_def

definition CJALRActions where
  "CJALRActions \<equiv> \<lambda>(cd, cb). 
   return {RestrictCapAction RegPCC (RegNormal cd),
           RestrictCapAction (if cb = cd then RegPCC else RegNormal cb) RegBranchDelayPCC}"

abbreviation getCJALRActions where
  "getCJALRActions v \<equiv> ValuePart (CJALRActions v)"

lemma CJALRActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CJALRActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CJALRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CJALRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CJALRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CJALRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CJALRActions v) s"
unfolding CJALRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CJALRActions_StatePart [simp]:
  shows "StatePart (CJALRActions v) = (\<lambda>s. s)"
unfolding CJALRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CJALRActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CJALRActions v) m"
unfolding CJALRActions_def
by (cases v) simp

subsubsection \<open>@{const CJR}\<close>

thm dfn'CJR_alt_def

definition CJRActions where
  "CJRActions \<equiv> \<lambda>cb. return {RestrictCapAction (RegNormal cb) RegBranchDelayPCC}"

abbreviation getCJRActions where
  "getCJRActions v \<equiv> ValuePart (CJRActions v)"

lemma CJRActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CJRActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CJRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CJRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CJRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CJRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CJRActions v) s"
unfolding CJRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CJRActions_StatePart [simp]:
  shows "StatePart (CJRActions v) = (\<lambda>s. s)"
unfolding CJRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CJRActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CJRActions v) m"
unfolding CJRActions_def
by (cases v) simp

subsubsection \<open>@{const CLC}\<close>

thm dfn'CLC_alt_def

definition CLCVirtualAddress where 
  "CLCVirtualAddress cb rt offset \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. bind (read_state (getGPR rt))
        (\<lambda>gpr. return (getBase cap + getOffset cap + gpr + 
                       scast ((word_cat (offset::11 word) (0::4 word))::15 word))))"

abbreviation getCLCVirtualAddress where
  "getCLCVirtualAddress cb rt offset \<equiv> ValuePart (CLCVirtualAddress cb rt offset)"

lemma CLCVirtualAddress_StatePart [simp]:
  shows "StatePart (CLCVirtualAddress cb rt offset) = (\<lambda>s. s)"
unfolding CLCVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLCVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
      and "Commute (read_state (getGPR rt)) m"
  shows "Commute (CLCVirtualAddress cb rt offset) m"
unfolding CLCVirtualAddress_def
using assms
by auto

definition CLCPhysicalAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                  11 word \<Rightarrow> state \<Rightarrow> PhysicalAddress option \<times> state" where 
  "CLCPhysicalAddress cb rt offset \<equiv> 
   bind (CLCVirtualAddress cb rt offset)
        (\<lambda>a. read_state (getPhysicalAddress (a, LOAD)))"

abbreviation getCLCPhysicalAddress where
  "getCLCPhysicalAddress cb rt offset \<equiv> ValuePart (CLCPhysicalAddress cb rt offset)"

lemma CLCPhysicalAddress_StatePart [simp]:
  shows "StatePart (CLCPhysicalAddress cb rt offset) = (\<lambda>s. s)"
unfolding CLCPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLCPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CLCVirtualAddress cb rt offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CLCPhysicalAddress cb rt offset) m"
unfolding CLCPhysicalAddress_def
using assms
by auto

definition CLCActions where
  "CLCActions \<equiv> \<lambda>(cd, cb, rt, offset). 
   bind (CLCPhysicalAddress cb rt offset) 
        (\<lambda>a. bind (read_state (getCAPR cb))
        (\<lambda>cap. case a of None \<Rightarrow> return {} | 
                         Some x \<Rightarrow> return (if Permit_Load_Capability (getPerms cap)
                                           then {LoadCapAction (RegNormal cb) (GetCapAddress x) cd}
                                           else {RestrictCapAction (RegNormal cd) (RegNormal cd),
                                                 LoadDataAction (RegNormal cb) x 32})))"

abbreviation getCLCActions where
  "getCLCActions v \<equiv> ValuePart (CLCActions v)"

lemma CLCActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (CLCActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CLCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CLCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CLCActions v) s"
unfolding CLCActions_def
by (auto simp: ValueAndStatePart_simp split: all_split)

lemma CLCActions_StatePart [simp]:
  shows "StatePart (CLCActions v) = (\<lambda>s. s)"
unfolding CLCActions_def
by (auto simp: ValueAndStatePart_simp split: all_split)

lemma Commute_CLCActions [Commute_compositeI]:
  assumes "\<And>cb rt offset. Commute (CLCPhysicalAddress cb rt offset) m"
      and "\<And>cb. Commute (read_state (getCAPR cb)) m"
  shows "Commute (CLCActions v) m"
unfolding CLCActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CLLC}\<close>

thm dfn'CLLC_alt_def

definition CLLCVirtualAddress where 
  "CLLCVirtualAddress cb \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. return (getBase cap + getOffset cap))"

abbreviation getCLLCVirtualAddress where
  "getCLLCVirtualAddress cb \<equiv> ValuePart (CLLCVirtualAddress cb)"

lemma CLLCVirtualAddress_StatePart [simp]:
  shows "StatePart (CLLCVirtualAddress cb) = (\<lambda>s. s)"
unfolding CLLCVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLLCVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
  shows "Commute (CLLCVirtualAddress cb) m"
unfolding CLLCVirtualAddress_def
using assms
by auto

definition CLLCPhysicalAddress :: "RegisterAddress \<Rightarrow> state \<Rightarrow> 
                                   PhysicalAddress option \<times> state" where 
  "CLLCPhysicalAddress cb \<equiv> 
   bind (CLLCVirtualAddress cb)
        (\<lambda>a. read_state (getPhysicalAddress (a, LOAD)))"

abbreviation getCLLCPhysicalAddress where
  "getCLLCPhysicalAddress cb \<equiv> ValuePart (CLLCPhysicalAddress cb)"

lemma CLLCPhysicalAddress_StatePart [simp]:
  shows "StatePart (CLLCPhysicalAddress cb) = (\<lambda>s. s)"
unfolding CLLCPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLLCPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CLLCVirtualAddress cb) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CLLCPhysicalAddress cb) m"
unfolding CLLCPhysicalAddress_def
using assms
by auto

definition CLLCActions where
  "CLLCActions \<equiv> \<lambda>(cd, cb). 
   bind (CLLCPhysicalAddress cb) 
        (\<lambda>a. bind (read_state (getCAPR cb))
        (\<lambda>cap. case a of None \<Rightarrow> return {} | 
                         Some x \<Rightarrow> return (if Permit_Load_Capability (getPerms cap)
                                           then {LoadCapAction (RegNormal cb) (GetCapAddress x) cd}
                                           else {RestrictCapAction (RegNormal cd) (RegNormal cd),
                                                 LoadDataAction (RegNormal cb) x 32})))"

abbreviation getCLLCActions where
  "getCLLCActions v \<equiv> ValuePart (CLLCActions v)"

lemma CLLCActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (CLLCActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CLLCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CLLCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CLLCActions v) s"
unfolding CLLCActions_def
by (auto simp: ValueAndStatePart_simp split: all_split)

lemma CLLCActions_StatePart [simp]:
  shows "StatePart (CLLCActions v) = (\<lambda>s. s)"
unfolding CLLCActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CLLCActions [Commute_compositeI]:
  assumes "\<And>cb. Commute (CLLCPhysicalAddress cb) m"
      and "Commute (read_state getLLbit) m"
      and "\<And>cb. Commute (read_state (getCAPR cb)) m"
  shows "Commute (CLLCActions v) m"
unfolding CLLCActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CMOVN}\<close>

thm dfn'CMOVN_alt_def

definition CMOVNActions where
  "CMOVNActions \<equiv> \<lambda>(cd, cb, rt). 
   bind (read_state (getGPR rt))
        (\<lambda>x. if x \<noteq> 0 
             then return {RestrictCapAction (RegNormal cb) (RegNormal cd)}
             else return {})"

abbreviation getCMOVNActions where
  "getCMOVNActions v \<equiv> ValuePart (CMOVNActions v)"

lemma CMOVNActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CMOVNActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CMOVNActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CMOVNActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CMOVNActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CMOVNActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CMOVNActions v) s"
unfolding CMOVNActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CMOVNActions_StatePart [simp]:
  shows "StatePart (CMOVNActions v) = (\<lambda>s. s)"
unfolding CMOVNActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CMOVNActions [Commute_compositeI]:
  assumes "\<And>x. Commute (read_state (getGPR x)) m"
  shows "Commute (CMOVNActions v) m"
unfolding CMOVNActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CMOVZ}\<close>

thm dfn'CMOVZ_alt_def

definition CMOVZActions where
  "CMOVZActions \<equiv> \<lambda>(cd, cb, rt). 
   bind (read_state (getGPR rt))
        (\<lambda>x. if x = 0 
             then return {RestrictCapAction (RegNormal cb) (RegNormal cd)}
             else return {})"

abbreviation getCMOVZActions where
  "getCMOVZActions v \<equiv> ValuePart (CMOVZActions v)"

lemma CMOVZActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CMOVZActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CMOVZActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CMOVZActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CMOVZActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CMOVZActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CMOVZActions v) s"
unfolding CMOVZActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CMOVZActions_StatePart [simp]:
  shows "StatePart (CMOVZActions v) = (\<lambda>s. s)"
unfolding CMOVZActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CMOVZActions [Commute_compositeI]:
  assumes "\<And>x. Commute (read_state (getGPR x)) m"
  shows "Commute (CMOVZActions v) m"
unfolding CMOVZActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CReadHwr}\<close>

thm dfn'CReadHwr_alt_def

definition CReadHwrActions where
  "CReadHwrActions \<equiv> \<lambda>(cd, selector). 
   return {RestrictCapAction (RegSpecial selector) (RegNormal cd)}"

abbreviation getCReadHwrActions where
  "getCReadHwrActions v \<equiv> ValuePart (CReadHwrActions v)"

lemma CReadHwrActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CReadHwrActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CReadHwrActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CReadHwrActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CReadHwrActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CReadHwrActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CReadHwrActions v) s"
unfolding CReadHwrActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CReadHwrActions_StatePart [simp]:
  shows "StatePart (CReadHwrActions v) = (\<lambda>s. s)"
unfolding CReadHwrActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CReadHwrActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CReadHwrActions v) m"
unfolding CReadHwrActions_def
by auto

subsubsection \<open>@{const CMove}\<close>

thm dfn'CMove_alt_def

definition CMoveActions where
  "CMoveActions \<equiv> \<lambda>(cd, cs). 
   return {RestrictCapAction (RegNormal cs) (RegNormal cd)}"

abbreviation getCMoveActions where
  "getCMoveActions v \<equiv> ValuePart (CMoveActions v)"

lemma CMoveActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CMoveActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CMoveActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CMoveActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CMoveActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CMoveActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CMoveActions v) s"
unfolding CMoveActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CMoveActions_StatePart [simp]:
  shows "StatePart (CMoveActions v) = (\<lambda>s. s)"
unfolding CMoveActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CMoveActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CMoveActions v) m"
unfolding CMoveActions_def
by auto

subsubsection \<open>@{const CSC}\<close>

thm dfn'CSC_alt_def

definition CSCVirtualAddress where 
  "CSCVirtualAddress cb rt offset \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. bind (read_state (getGPR rt))
        (\<lambda>gpr. return (getBase cap + getOffset cap + gpr + 
                       scast ((word_cat (offset::11 word) (0::4 word))::15 word))))"

abbreviation getCSCVirtualAddress where
  "getCSCVirtualAddress cb rt offset \<equiv> ValuePart (CSCVirtualAddress cb rt offset)"

lemma CSCVirtualAddress_StatePart [simp]:
  shows "StatePart (CSCVirtualAddress cb rt offset) = (\<lambda>s. s)"
unfolding CSCVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
      and "Commute (read_state (getGPR rt)) m"
  shows "Commute (CSCVirtualAddress cb rt offset) m"
unfolding CSCVirtualAddress_def
using assms
by auto

definition CSCPhysicalAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                  11 word \<Rightarrow> state \<Rightarrow> PhysicalAddress option \<times> state" where 
  "CSCPhysicalAddress cb rt offset \<equiv> 
   bind (CSCVirtualAddress cb rt offset)
        (\<lambda>a. read_state (getPhysicalAddress (a, STORE)))"

abbreviation getCSCPhysicalAddress where
  "getCSCPhysicalAddress cb rt offset \<equiv> ValuePart (CSCPhysicalAddress cb rt offset)"

lemma CSCPhysicalAddress_StatePart [simp]:
  shows "StatePart (CSCPhysicalAddress cb rt offset) = (\<lambda>s. s)"
unfolding CSCPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CSCVirtualAddress cb rt offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CSCPhysicalAddress cb rt offset) m"
unfolding CSCPhysicalAddress_def
using assms
by auto

definition CSCActions where
  "CSCActions \<equiv> \<lambda>(cs, cb, rt, offset). 
   bind (CSCPhysicalAddress cb rt offset)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {StoreCapAction (RegNormal cb) cs (GetCapAddress x)}))"

abbreviation getCSCActions where
  "getCSCActions v \<equiv> ValuePart (CSCActions v)"

lemma CSCActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSCActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSCActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CSCActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSCActions v) s"
unfolding CSCActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma CSCActions_StatePart [simp]:
  shows "StatePart (CSCActions v) = (\<lambda>s. s)"
unfolding CSCActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCActions [Commute_compositeI]:
  assumes "\<And>cb rt offset. Commute (CSCPhysicalAddress cb rt offset) m"
  shows "Commute (CSCActions v) m"
unfolding CSCActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CSCC}\<close>

thm dfn'CSCC_alt_def

definition CSCCVirtualAddress where 
  "CSCCVirtualAddress cb \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. return (getBase cap + getOffset cap))"

abbreviation getCSCCVirtualAddress where
  "getCSCCVirtualAddress cb \<equiv> ValuePart (CSCCVirtualAddress cb)"

lemma CSCCVirtualAddress_StatePart [simp]:
  shows "StatePart (CSCCVirtualAddress cb) = (\<lambda>s. s)"
unfolding CSCCVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCCVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
  shows "Commute (CSCCVirtualAddress cb) m"
unfolding CSCCVirtualAddress_def
using assms
by auto

definition CSCCPhysicalAddress :: "RegisterAddress \<Rightarrow> state \<Rightarrow> 
                                   PhysicalAddress option \<times> state" where 
  "CSCCPhysicalAddress cb \<equiv> 
   bind (CSCCVirtualAddress cb)
        (\<lambda>a. read_state (getPhysicalAddress (a, STORE)))"

abbreviation getCSCCPhysicalAddress where
  "getCSCCPhysicalAddress cb \<equiv> ValuePart (CSCCPhysicalAddress cb)"

lemma CSCCPhysicalAddress_StatePart [simp]:
  shows "StatePart (CSCCPhysicalAddress cb) = (\<lambda>s. s)"
unfolding CSCCPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCCPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CSCCVirtualAddress cb) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CSCCPhysicalAddress cb) m"
unfolding CSCCPhysicalAddress_def
using assms
by auto

definition CSCCActions where
  "CSCCActions \<equiv> \<lambda>(cs, cb, rd).
   bind (read_state getLLbit)
        (\<lambda>llbit. if llbit = Some True
                 then bind (CSCCPhysicalAddress cb)
                           (\<lambda>a. return (case a of None \<Rightarrow> {}  
                                                | Some x \<Rightarrow> 
                                                    {StoreCapAction (RegNormal cb) cs (GetCapAddress x)}))
                  else return {})"

abbreviation getCSCCActions where
  "getCSCCActions v \<equiv> ValuePart (CSCCActions v)"

lemma CSCCActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSCCActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSCCActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CSCCActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSCCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSCCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSCCActions v) s"
unfolding CSCCActions_def
by (auto simp: ValueAndStatePart_simp split: all_split)

lemma CSCCActions_StatePart [simp]:
  shows "StatePart (CSCCActions v) = (\<lambda>s. s)"
unfolding CSCCActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CSCCActions [Commute_compositeI]:
  assumes "\<And>cb. Commute (CSCCPhysicalAddress cb) m"
      and "\<And>cb. Commute (read_state getLLbit) m"
  shows "Commute (CSCCActions v) m"
unfolding CSCCActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const CSeal}\<close>

thm dfn'CSeal_alt_def

definition CSealActions where
  "CSealActions \<equiv> \<lambda>(cd, cs, ct). 
   return (if cd = 0 then {} else {SealCapAction (RegNormal ct) cs cd})"

abbreviation getCSealActions where
  "getCSealActions v \<equiv> ValuePart (CSealActions v)"

lemma CSealActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSealActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSealActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CSealActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSealActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSealActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSealActions v) s"
unfolding CSealActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CSealActions_StatePart [simp]:
  shows "StatePart (CSealActions v) = (\<lambda>s. s)"
unfolding CSealActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSealActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CSealActions v) m"
unfolding CSealActions_def
by (cases v) simp

subsubsection \<open>@{const CSetBounds}\<close>

thm dfn'CSetBounds_alt_def

definition CSetBoundsActions where
  "CSetBoundsActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCSetBoundsActions where
  "getCSetBoundsActions v \<equiv> ValuePart (CSetBoundsActions v)"

lemma CSetBoundsActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSetBoundsActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSetBoundsActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSetBoundsActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSetBoundsActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsActions v) s"
unfolding CSetBoundsActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CSetBoundsActions_StatePart [simp]:
  shows "StatePart (CSetBoundsActions v) = (\<lambda>s. s)"
unfolding CSetBoundsActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSetBoundsActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CSetBoundsActions v) m"
unfolding CSetBoundsActions_def
by (cases v) simp

subsubsection \<open>@{const CSetBoundsExact}\<close>

thm dfn'CSetBoundsExact_alt_def

definition CSetBoundsExactActions where
  "CSetBoundsExactActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCSetBoundsExactActions where
  "getCSetBoundsExactActions v \<equiv> ValuePart (CSetBoundsExactActions v)"

lemma CSetBoundsExactActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSetBoundsExactActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSetBoundsExactActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSetBoundsExactActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSetBoundsExactActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsExactActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsExactActions v) s"
unfolding CSetBoundsExactActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CSetBoundsExactActions_StatePart [simp]:
  shows "StatePart (CSetBoundsExactActions v) = (\<lambda>s. s)"
unfolding CSetBoundsExactActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSetBoundsExactActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CSetBoundsExactActions v) m"
unfolding CSetBoundsExactActions_def
by (cases v) simp

subsubsection \<open>@{const CSetBoundsImmediate}\<close>

thm dfn'CSetBoundsImmediate_alt_def

definition CSetBoundsImmediateActions where
  "CSetBoundsImmediateActions \<equiv> \<lambda>(cd, cb, rt). 
   return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCSetBoundsImmediateActions where
  "getCSetBoundsImmediateActions v \<equiv> ValuePart (CSetBoundsImmediateActions v)"

lemma CSetBoundsImmediateActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSetBoundsImmediateActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSetBoundsImmediateActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSetBoundsImmediateActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSetBoundsImmediateActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsImmediateActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSetBoundsImmediateActions v) s"
unfolding CSetBoundsImmediateActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CSetBoundsImmediateActions_StatePart [simp]:
  shows "StatePart (CSetBoundsImmediateActions v) = (\<lambda>s. s)"
unfolding CSetBoundsImmediateActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSetBoundsImmediateActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CSetBoundsImmediateActions v) m"
unfolding CSetBoundsImmediateActions_def
by (cases v) simp

subsubsection \<open>@{const CSetOffset}\<close>

thm dfn'CSetOffset_alt_def

definition CSetOffsetActions where
  "CSetOffsetActions \<equiv> \<lambda>(cd, cb, rt). return {RestrictCapAction (RegNormal cb) (RegNormal cd)}"

abbreviation getCSetOffsetActions where
  "getCSetOffsetActions v \<equiv> ValuePart (CSetOffsetActions v)"

lemma CSetOffsetActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSetOffsetActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CSetOffsetActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSetOffsetActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSetOffsetActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSetOffsetActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSetOffsetActions v) s"
unfolding CSetOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma CSetOffsetActions_StatePart [simp]:
  shows "StatePart (CSetOffsetActions v) = (\<lambda>s. s)"
unfolding CSetOffsetActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSetOffsetActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CSetOffsetActions v) m"
unfolding CSetOffsetActions_def
by (cases v) simp

subsubsection \<open>@{const CUnseal}\<close>

thm dfn'CUnseal_alt_def

definition CUnsealActions where
  "CUnsealActions \<equiv> \<lambda>(cd, cs, ct).
   return (if cd = 0 then {} else {UnsealCapAction (RegNormal ct) cs cd})"

abbreviation getCUnsealActions where
  "getCUnsealActions v \<equiv> ValuePart (CUnsealActions v)"

lemma CUnsealActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CUnsealActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CUnsealActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CUnsealActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CUnsealActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CUnsealActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CUnsealActions v) s"
unfolding CUnsealActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CUnsealActions_StatePart [simp]:
  shows "StatePart (CUnsealActions v) = (\<lambda>s. s)"
unfolding CUnsealActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CUnsealActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CUnsealActions v) m"
unfolding CUnsealActions_def
by (cases v) simp

subsubsection \<open>@{const CWriteHwr}\<close>

thm dfn'CWriteHwr_alt_def

definition CWriteHwrActions where
  "CWriteHwrActions \<equiv> \<lambda>(cb, selector). 
   return {RestrictCapAction (RegNormal cb) (RegSpecial selector)}"

abbreviation getCWriteHwrActions where
  "getCWriteHwrActions v \<equiv> ValuePart (CWriteHwrActions v)"

lemma CWriteHwrActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CWriteHwrActions v) s"
    and "StoreDataAction auth a' l \<notin> ValuePart (CWriteHwrActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CWriteHwrActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CWriteHwrActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CWriteHwrActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CWriteHwrActions v) s"
unfolding CWriteHwrActions_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

lemma CWriteHwrActions_StatePart [simp]:
  shows "StatePart (CWriteHwrActions v) = (\<lambda>s. s)"
unfolding CWriteHwrActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_CWriteHwrActions [intro!, Commute_compositeI, simp]:
  shows "Commute (CWriteHwrActions v) m"
unfolding CWriteHwrActions_def
by auto

subsubsection \<open>@{const ERET}\<close>

thm dfn'ERET_alt_def

definition ERETActions where
  "ERETActions \<equiv> return {RestrictCapAction (RegSpecial 31) RegPCC}"

abbreviation getERETActions where
  "getERETActions \<equiv> ValuePart ERETActions"

lemma ERETActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart ERETActions s"
    and "StoreDataAction auth a' l \<notin> ValuePart ERETActions s"
    and "LoadCapAction auth a cd \<notin> ValuePart ERETActions s"
    and "StoreCapAction auth cd a \<notin> ValuePart ERETActions s"
    and "SealCapAction auth cd cd' \<notin> ValuePart ERETActions s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart ERETActions s"
unfolding ERETActions_def
by (auto simp: ValueAndStatePart_simp)

lemma ERETActions_StatePart [simp]:
  shows "StatePart ERETActions = (\<lambda>s. s)"
unfolding ERETActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_ERETActions [intro!, Commute_compositeI, simp]:
  shows "Commute ERETActions m"
unfolding ERETActions_def
by simp

subsection \<open>Loading data\<close>

subsubsection \<open>Legacy loads virtual address\<close>

thm getVirtualAddress_alt_def

definition LegacyLoadVirtualAddress :: "RegisterAddress \<Rightarrow> 16 word \<Rightarrow> 
                                        state \<Rightarrow> VirtualAddress \<times> state" where
  "LegacyLoadVirtualAddress \<equiv> \<lambda>base offset.
   bind (read_state (getGPR base))
        (\<lambda>v. bind (read_state (getSCAPR 0))
        (\<lambda>cap. return (scast offset + v + getBase cap + getOffset cap)))"

abbreviation getLegacyLoadVirtualAddress where
  "getLegacyLoadVirtualAddress b offset \<equiv> ValuePart (LegacyLoadVirtualAddress b offset)"

lemma LegacyLoadVirtualAddress_StatePart [simp]:
  shows "StatePart (LegacyLoadVirtualAddress b offset) = (\<lambda>s. s)"
unfolding LegacyLoadVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyLoadVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getSCAPR 0)) m"
      and "Commute (read_state (getGPR b)) m"
  shows "Commute (LegacyLoadVirtualAddress b offset) m"
unfolding LegacyLoadVirtualAddress_def
using assms
by auto

subsubsection \<open>Legacy loads physical address\<close>

definition LegacyLoadPhysicalAddress :: "RegisterAddress \<Rightarrow> 16 word \<Rightarrow> 
                                         state \<Rightarrow> PhysicalAddress option \<times> state" where 
  "LegacyLoadPhysicalAddress \<equiv> \<lambda>base offset.
   bind (LegacyLoadVirtualAddress base offset)
        (\<lambda>a. read_state (getPhysicalAddress (a, LOAD)))"

abbreviation getLegacyLoadPhysicalAddress where
  "getLegacyLoadPhysicalAddress b offset \<equiv> ValuePart (LegacyLoadPhysicalAddress b offset)"

lemma LegacyLoadPhysicalAddress_StatePart [simp]:
  shows "StatePart (LegacyLoadPhysicalAddress b offset) = (\<lambda>s. s)"
unfolding LegacyLoadPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyLoadPhysicalAddress [Commute_compositeI]:
  assumes "Commute (LegacyLoadVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LegacyLoadPhysicalAddress b offset) m"
unfolding LegacyLoadPhysicalAddress_def
using assms
by auto

subsubsection \<open>Legacy loads actions\<close>

thm loadByte_alt_def
thm loadHalf_alt_def
thm loadWord_alt_def
thm loadDoubleword_alt_def

definition LegacyLoadActions where
  "LegacyLoadActions \<equiv> \<lambda>base offset length. 
   bind (LegacyLoadPhysicalAddress base offset)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {LoadDataAction (RegSpecial 0) x length}))"

abbreviation getLegacyLoadActions where
  "getLegacyLoadActions b offset l \<equiv> ValuePart (LegacyLoadActions b offset l)"

lemma LegacyLoadActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LegacyLoadActions b offset l') s"
    and "RestrictCapAction r r' \<notin> ValuePart (LegacyLoadActions b offset l') s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LegacyLoadActions b offset l') s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LegacyLoadActions b offset l') s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LegacyLoadActions b offset l') s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LegacyLoadActions b offset l') s"
unfolding LegacyLoadActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LegacyLoadActions_StatePart [simp]:
  shows "StatePart (LegacyLoadActions b offset l) = (\<lambda>s. s)"
unfolding LegacyLoadActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyLoadActions [Commute_compositeI]:
  assumes "Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LegacyLoadActions b offset l') m"
unfolding LegacyLoadActions_def
using assms
by - Commute_find_dependencies

subsubsection \<open>@{const dfn'LB}\<close>

thm dfn'LB_alt_def

definition LBActions where
  "LBActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 1"

abbreviation getLBActions where
  "getLBActions v \<equiv> ValuePart (LBActions v)"

lemma LBActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LBActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LBActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LBActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LBActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LBActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LBActions v) s"
unfolding LBActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LBActions_StatePart [simp]:
  shows "StatePart (LBActions v) = (\<lambda>s. s)"
unfolding LBActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LBActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LBActions v) m"
unfolding LBActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LBU}\<close>

thm dfn'LBU_alt_def

definition LBUActions where
  "LBUActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 1"

abbreviation getLBUActions where
  "getLBUActions v \<equiv> ValuePart (LBUActions v)"

lemma LBUActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LBUActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LBUActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LBUActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LBUActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LBUActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LBUActions v) s"
unfolding LBUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LBUActions_StatePart [simp]:
  shows "StatePart (LBUActions v) = (\<lambda>s. s)"
unfolding LBUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LBUActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LBUActions v) m"
unfolding LBUActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LH}\<close>

thm dfn'LH_alt_def

definition LHActions where
  "LHActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 2"

abbreviation getLHActions where
  "getLHActions v \<equiv> ValuePart (LHActions v)"

lemma LHActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LHActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LHActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LHActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LHActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LHActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LHActions v) s"
unfolding LHActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LHActions_StatePart [simp]:
  shows "StatePart (LHActions v) = (\<lambda>s. s)"
unfolding LHActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LHActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LHActions v) m"
unfolding LHActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LHU}\<close>

thm dfn'LHU_alt_def

definition LHUActions where
  "LHUActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 2"

abbreviation getLHUActions where
  "getLHUActions v \<equiv> ValuePart (LHUActions v)"

lemma LHUActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LHUActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LHUActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LHUActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LHUActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LHUActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LHUActions v) s"
unfolding LHUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LHUActions_StatePart [simp]:
  shows "StatePart (LHUActions v) = (\<lambda>s. s)"
unfolding LHUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LHUActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LHUActions v) m"
unfolding LHUActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LW}\<close>

thm dfn'LW_alt_def

definition LWActions where
  "LWActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 4"

abbreviation getLWActions where
  "getLWActions v \<equiv> ValuePart (LWActions v)"

lemma LWActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LWActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LWActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LWActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LWActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LWActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LWActions v) s"
unfolding LWActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LWActions_StatePart [simp]:
  shows "StatePart (LWActions v) = (\<lambda>s. s)"
unfolding LWActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LWActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LWActions v) m"
unfolding LWActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LWU}\<close>

thm dfn'LWU_alt_def

definition LWUActions where
  "LWUActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 4"

abbreviation getLWUActions where
  "getLWUActions v \<equiv> ValuePart (LWUActions v)"

lemma LWUActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LWUActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LWUActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LWUActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LWUActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LWUActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LWUActions v) s"
unfolding LWUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LWUActions_StatePart [simp]:
  shows "StatePart (LWUActions v) = (\<lambda>s. s)"
unfolding LWUActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LWUActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LWUActions v) m"
unfolding LWUActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LL}\<close>

thm dfn'LL_alt_def

definition LLActions where
  "LLActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 4"

abbreviation getLLActions where
  "getLLActions v \<equiv> ValuePart (LLActions v)"

lemma LLActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LLActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LLActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LLActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LLActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LLActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LLActions v) s"
unfolding LLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LLActions_StatePart [simp]:
  shows "StatePart (LLActions v) = (\<lambda>s. s)"
unfolding LLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LLActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LLActions v) m"
unfolding LLActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LD}\<close>

thm dfn'LD_alt_def

definition LDActions where
  "LDActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 8"

abbreviation getLDActions where
  "getLDActions v \<equiv> ValuePart (LDActions v)"

lemma LDActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LDActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LDActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LDActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LDActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LDActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LDActions v) s"
unfolding LDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LDActions_StatePart [simp]:
  shows "StatePart (LDActions v) = (\<lambda>s. s)"
unfolding LDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LDActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LDActions v) m"
unfolding LDActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LLD}\<close>

thm dfn'LLD_alt_def

definition LLDActions where
  "LLDActions \<equiv> \<lambda>(base, rt, offset). LegacyLoadActions base offset 8"

abbreviation getLLDActions where
  "getLLDActions v \<equiv> ValuePart (LLDActions v)"

lemma LLDActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LLDActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LLDActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LLDActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LLDActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LLDActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LLDActions v) s"
unfolding LLDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma LLDActions_StatePart [simp]:
  shows "StatePart (LLDActions v) = (\<lambda>s. s)"
unfolding LLDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LLDActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadPhysicalAddress b offset) m"
  shows "Commute (LLDActions v) m"
unfolding LLDActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LWL}\<close>

thm dfn'LWL_alt_def

definition LWLActions where
  "LWLActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyLoadVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {LoadDataAction (RegSpecial 0) 
                                             pAddr 
                                             (((NOT ucast vAddr) AND mask 2) + 1)})))"

abbreviation getLWLActions where
  "getLWLActions v \<equiv> ValuePart (LWLActions v)"

lemma LWLActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LWLActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LWLActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LWLActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LWLActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LWLActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LWLActions v) s"
unfolding LWLActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LWLActions_StatePart [simp]:
  shows "StatePart (LWLActions v) = (\<lambda>s. s)"
unfolding LWLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LWLActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LWLActions v) m"
unfolding LWLActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LWR}\<close>

thm dfn'LWR_alt_def

definition LWRActions where
  "LWRActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyLoadVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr AND NOT mask 2, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {LoadDataAction (RegSpecial 0) 
                                             pAddr 
                                             ((ucast vAddr AND mask 2) + 1)})))"

abbreviation getLWRActions where
  "getLWRActions v \<equiv> ValuePart (LWRActions v)"

lemma LWRActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LWRActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LWRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LWRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LWRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LWRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LWRActions v) s"
unfolding LWRActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LWRActions_StatePart [simp]:
  shows "StatePart (LWRActions v) = (\<lambda>s. s)"
unfolding LWRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LWRActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LWRActions v) m"
unfolding LWRActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LDL}\<close>

thm dfn'LDL_alt_def

definition LDLActions where
  "LDLActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyLoadVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {LoadDataAction (RegSpecial 0)
                                             pAddr 
                                             (((NOT ucast vAddr) AND mask 3) + 1)})))"

abbreviation getLDLActions where
  "getLDLActions v \<equiv> ValuePart (LDLActions v)"

lemma LDLActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LDLActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LDLActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LDLActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LDLActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LDLActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LDLActions v) s"
unfolding LDLActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LDLActions_StatePart [simp]:
  shows "StatePart (LDLActions v) = (\<lambda>s. s)"
unfolding LDLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LDLActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LDLActions v) m"
unfolding LDLActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'LDR}\<close>

thm dfn'LDR_alt_def

definition LDRActions where
  "LDRActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyLoadVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr AND NOT mask 3, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {LoadDataAction (RegSpecial 0) 
                                             pAddr 
                                             ((ucast vAddr AND mask 3) + 1)})))"

abbreviation getLDRActions where
  "getLDRActions v \<equiv> ValuePart (LDRActions v)"

lemma LDRActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (LDRActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (LDRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LDRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LDRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LDRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LDRActions v) s"
unfolding LDRActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LDRActions_StatePart [simp]:
  shows "StatePart (LDRActions v) = (\<lambda>s. s)"
unfolding LDRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LDRActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyLoadVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LDRActions v) m"
unfolding LDRActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'CLoad}\<close>

thm dfn'CLoad_alt_def

definition CLoadVirtualAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                     8 word \<Rightarrow> 2 word \<Rightarrow> state \<Rightarrow> 
                                     VirtualAddress \<times> state" where 
  "CLoadVirtualAddress cb rt offset t \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. bind (read_state (getGPR rt))
        (\<lambda>v. return (getBase cap + getOffset cap + v + (scast offset << unat t))))"

abbreviation getCLoadVirtualAddress where
  "getCLoadVirtualAddress cb rt offset t \<equiv> ValuePart (CLoadVirtualAddress cb rt offset t)"

lemma CLoadVirtualAddress_StatePart [simp]:
  shows "StatePart (CLoadVirtualAddress cb rt offset t) = (\<lambda>s. s)"
unfolding CLoadVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLoadVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
      and "Commute (read_state (getGPR rt)) m"
  shows "Commute (CLoadVirtualAddress cb rt offset t) m"
unfolding CLoadVirtualAddress_def
using assms
by auto

definition CLoadPhysicalAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                     8 word \<Rightarrow> 2 word \<Rightarrow> state \<Rightarrow> 
                                     PhysicalAddress option \<times> state" where 
  "CLoadPhysicalAddress cb rt offset t \<equiv> 
   bind (CLoadVirtualAddress cb rt offset t)
        (\<lambda>a. bind (read_state (getPhysicalAddress (a, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> None | Some y \<Rightarrow> Some y)))"

abbreviation getCLoadPhysicalAddress where
  "getCLoadPhysicalAddress cb rt offset t \<equiv> ValuePart (CLoadPhysicalAddress cb rt offset t)"

lemma CLoadPhysicalAddress_StatePart [simp]:
  shows "StatePart (CLoadPhysicalAddress cb rt offset t) = (\<lambda>s. s)"
unfolding CLoadPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLoadPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CLoadVirtualAddress cb rt offset t) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CLoadPhysicalAddress cb rt offset t) m"
unfolding CLoadPhysicalAddress_def
using assms
by auto

definition CLoadActions where
  "CLoadActions \<equiv> \<lambda>(rd, cb, rt, offset, s, t). 
   bind (CLoadPhysicalAddress cb rt offset t)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {LoadDataAction (RegNormal cb) x (2 ^ unat t)}))"

abbreviation getCLoadActions where
  "getCLoadActions v \<equiv> ValuePart (CLoadActions v)"

lemma CLoadActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (CLoadActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CLoadActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CLoadActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CLoadActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CLoadActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CLoadActions v) s"
unfolding CLoadActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma CLoadActions_StatePart [simp]:
  shows "StatePart (CLoadActions v) = (\<lambda>s. s)"
unfolding CLoadActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLoadActions [Commute_compositeI]:
  assumes "\<And>cb rt offset t. Commute (CLoadPhysicalAddress cb rt offset t) m"
  shows "Commute (CLoadActions v) m"
unfolding CLoadActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'CLLx}\<close>

thm dfn'CLLx_alt_def

definition CLLxVirtualAddress where 
  "CLLxVirtualAddress cb \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. return (getBase cap + getOffset cap))"

abbreviation getCLLxVirtualAddress where
  "getCLLxVirtualAddress cb \<equiv> ValuePart (CLLxVirtualAddress cb)"

lemma CLLxVirtualAddress_StatePart [simp]:
  shows "StatePart (CLLxVirtualAddress cb) = (\<lambda>s. s)"
unfolding CLLxVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLLxVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
  shows "Commute (CLLxVirtualAddress cb) m"
unfolding CLLxVirtualAddress_def
using assms
by auto

definition CLLxPhysicalAddress :: "RegisterAddress \<Rightarrow> state \<Rightarrow> 
                                   PhysicalAddress option \<times> state" where 
  "CLLxPhysicalAddress cb \<equiv> 
   bind (CLLxVirtualAddress cb)
        (\<lambda>a. bind (read_state (getPhysicalAddress (a, LOAD)))
        (\<lambda>x. return (case x of None \<Rightarrow> None | Some y \<Rightarrow> Some y)))"

abbreviation getCLLxPhysicalAddress where
  "getCLLxPhysicalAddress cb \<equiv> ValuePart (CLLxPhysicalAddress cb)"

lemma CLLxPhysicalAddress_StatePart [simp]:
  shows "StatePart (CLLxPhysicalAddress cb) = (\<lambda>s. s)"
unfolding CLLxPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLLxPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CLLxVirtualAddress cb) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CLLxPhysicalAddress cb) m"
unfolding CLLxPhysicalAddress_def
using assms
by auto

definition CLLxActions where
  "CLLxActions \<equiv> \<lambda>(rd, cb, stt). 
   bind (CLLxPhysicalAddress cb)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {LoadDataAction (RegNormal cb)
                                                     x 
                                                     (2 ^ unat (stt AND mask 2))}))"

abbreviation getCLLxActions where
  "getCLLxActions v \<equiv> ValuePart (CLLxActions v)"

lemma CLLxActions_simps [simp]:
  shows "StoreDataAction auth a' l \<notin> ValuePart (CLLxActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CLLxActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CLLxActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CLLxActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CLLxActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CLLxActions v) s"
unfolding CLLxActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma CLLxActions_StatePart [simp]:
  shows "StatePart (CLLxActions v) = (\<lambda>s. s)"
unfolding CLLxActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CLLxActions [Commute_compositeI]:
  assumes "\<And>cb. Commute (CLLxPhysicalAddress cb) m"
  shows "Commute (CLLxActions v) m"
unfolding CLLxActions_def
by (Commute intro: assms)

subsection \<open>Storing data\<close>

subsubsection \<open>Legacy stores virtual address\<close>

thm getVirtualAddress_alt_def

definition LegacyStoreVirtualAddress :: "RegisterAddress \<Rightarrow> 16 word \<Rightarrow> 
                                        state \<Rightarrow> VirtualAddress \<times> state" where
  "LegacyStoreVirtualAddress \<equiv> \<lambda>base offset.
   bind (read_state (getGPR base))
        (\<lambda>v. bind (read_state (getSCAPR 0))
        (\<lambda>cap. return (scast offset + v + getBase cap + getOffset cap)))"

abbreviation getLegacyStoreVirtualAddress where
  "getLegacyStoreVirtualAddress b offset \<equiv> ValuePart (LegacyStoreVirtualAddress b offset)"

lemma LegacyStoreVirtualAddress_StatePart [simp]:
  shows "StatePart (LegacyStoreVirtualAddress b offset) = (\<lambda>s. s)"
unfolding LegacyStoreVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyStoreVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getSCAPR 0)) m"
      and "Commute (read_state (getGPR b)) m"
  shows "Commute (LegacyStoreVirtualAddress b offset) m"
unfolding LegacyStoreVirtualAddress_def
using assms
by auto

subsubsection \<open>Legacy stores physical address\<close>

definition LegacyStorePhysicalAddress :: "RegisterAddress \<Rightarrow> 16 word \<Rightarrow> 
                                         state \<Rightarrow> PhysicalAddress option \<times> state" where 
  "LegacyStorePhysicalAddress \<equiv> \<lambda>base offset.
   bind (LegacyStoreVirtualAddress base offset)
        (\<lambda>a. read_state (getPhysicalAddress (a, STORE)))"

abbreviation getLegacyStorePhysicalAddress where
  "getLegacyStorePhysicalAddress b offset \<equiv> ValuePart (LegacyStorePhysicalAddress b offset)"

lemma LegacyStorePhysicalAddress_StatePart [simp]:
  shows "StatePart (LegacyStorePhysicalAddress b offset) = (\<lambda>s. s)"
unfolding LegacyStorePhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyStorePhysicalAddress [Commute_compositeI]:
  assumes "Commute (LegacyStoreVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (LegacyStorePhysicalAddress b offset) m"
unfolding LegacyStorePhysicalAddress_def
using assms
by auto

subsubsection \<open>Legacy stores actions\<close>

thm storeWord_alt_def
thm storeDoubleword_alt_def

definition LegacyStoreActions where
  "LegacyStoreActions \<equiv> \<lambda>base offset length. 
   bind (LegacyStorePhysicalAddress base offset)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {StoreDataAction (RegSpecial 0) x length}))"

abbreviation getLegacyStoreActions where
  "getLegacyStoreActions b offset l \<equiv> ValuePart (LegacyStoreActions b offset l)"

lemma LegacyStoreActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (LegacyStoreActions b offset l') s"
    and "RestrictCapAction r r' \<notin> ValuePart (LegacyStoreActions b offset l') s"
    and "LoadCapAction auth a cd \<notin> ValuePart (LegacyStoreActions b offset l') s"
    and "StoreCapAction auth cd a \<notin> ValuePart (LegacyStoreActions b offset l') s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (LegacyStoreActions b offset l') s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (LegacyStoreActions b offset l') s"
unfolding LegacyStoreActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma LegacyStoreActions_StatePart [simp]:
  shows "StatePart (LegacyStoreActions b offset l) = (\<lambda>s. s)"
unfolding LegacyStoreActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_LegacyStoreActions [Commute_compositeI]:
  assumes "Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (LegacyStoreActions b offset l') m"
unfolding LegacyStoreActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SB}\<close>

thm dfn'SB_alt_def

definition SBActions where
  "SBActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 1"

abbreviation getSBActions where
  "getSBActions v \<equiv> ValuePart (SBActions v)"

lemma SBActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SBActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SBActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SBActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SBActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SBActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SBActions v) s"
unfolding SBActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SBActions_StatePart [simp]:
  shows "StatePart (SBActions v) = (\<lambda>s. s)"
unfolding SBActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SBActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SBActions v) m"
unfolding SBActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SH}\<close>

thm dfn'SH_alt_def

definition SHActions where
  "SHActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 2"

abbreviation getSHActions where
  "getSHActions v \<equiv> ValuePart (SHActions v)"

lemma SHActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SHActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SHActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SHActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SHActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SHActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SHActions v) s"
unfolding SHActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SHActions_StatePart [simp]:
  shows "StatePart (SHActions v) = (\<lambda>s. s)"
unfolding SHActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SHActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SHActions v) m"
unfolding SHActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SW}\<close>

thm dfn'SW_alt_def

definition SWActions where
  "SWActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 4"

abbreviation getSWActions where
  "getSWActions v \<equiv> ValuePart (SWActions v)"

lemma SWActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SWActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SWActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SWActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SWActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SWActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SWActions v) s"
unfolding SWActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SWActions_StatePart [simp]:
  shows "StatePart (SWActions v) = (\<lambda>s. s)"
unfolding SWActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SWActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SWActions v) m"
unfolding SWActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SD}\<close>

thm dfn'SD_alt_def

definition SDActions where
  "SDActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 8"

abbreviation getSDActions where
  "getSDActions v \<equiv> ValuePart (SDActions v)"

lemma SDActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SDActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SDActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SDActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SDActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SDActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SDActions v) s"
unfolding SDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SDActions_StatePart [simp]:
  shows "StatePart (SDActions v) = (\<lambda>s. s)"
unfolding SDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SDActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SDActions v) m"
unfolding SDActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SC}\<close>

thm dfn'SC_alt_def

definition SCActions where
  "SCActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 4"

abbreviation getSCActions where
  "getSCActions v \<equiv> ValuePart (SCActions v)"

lemma SCActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SCActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SCActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SCActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SCActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SCActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SCActions v) s"
unfolding SCActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SCActions_StatePart [simp]:
  shows "StatePart (SCActions v) = (\<lambda>s. s)"
unfolding SCActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SCActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SCActions v) m"
unfolding SCActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SCD}\<close>

thm dfn'SCD_alt_def

definition SCDActions where
  "SCDActions \<equiv> \<lambda>(base, rt, offset). LegacyStoreActions base offset 8"

abbreviation getSCDActions where
  "getSCDActions v \<equiv> ValuePart (SCDActions v)"

lemma SCDActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SCDActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SCDActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SCDActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SCDActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SCDActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SCDActions v) s"
unfolding SCDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma SCDActions_StatePart [simp]:
  shows "StatePart (SCDActions v) = (\<lambda>s. s)"
unfolding SCDActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SCDActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStorePhysicalAddress b offset) m"
  shows "Commute (SCDActions v) m"
unfolding SCDActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SWL}\<close>

thm dfn'SWL_alt_def

definition SWLActions where
  "SWLActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyStoreVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {StoreDataAction (RegSpecial 0) 
                                                  pAddr 
                                                  (((NOT ucast vAddr) AND mask 2) + 1)})))"

abbreviation getSWLActions where
  "getSWLActions v \<equiv> ValuePart (SWLActions v)"

lemma SWLActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SWLActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SWLActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SWLActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SWLActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SWLActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SWLActions v) s"
unfolding SWLActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma SWLActions_StatePart [simp]:
  shows "StatePart (SWLActions v) = (\<lambda>s. s)"
unfolding SWLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SWLActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStoreVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (SWLActions v) m"
unfolding SWLActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SWR}\<close>

thm dfn'SWR_alt_def

definition SWRActions where
  "SWRActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyStoreVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr AND NOT mask 2, STORE)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {StoreDataAction (RegSpecial 0) 
                                                  pAddr 
                                                  ((ucast vAddr AND mask 2) + 1)})))"

abbreviation getSWRActions where
  "getSWRActions v \<equiv> ValuePart (SWRActions v)"

lemma SWRActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SWRActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SWRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SWRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SWRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SWRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SWRActions v) s"
unfolding SWRActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma SWRActions_StatePart [simp]:
  shows "StatePart (SWRActions v) = (\<lambda>s. s)"
unfolding SWRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SWRActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStoreVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (SWRActions v) m"
unfolding SWRActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SDL}\<close>

thm dfn'SDL_alt_def

definition SDLActions where
  "SDLActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyStoreVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {StoreDataAction (RegSpecial 0) 
                                                  pAddr 
                                                  (((NOT ucast vAddr) AND mask 3) + 1)})))"

abbreviation getSDLActions where
  "getSDLActions v \<equiv> ValuePart (SDLActions v)"

lemma SDLActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SDLActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SDLActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SDLActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SDLActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SDLActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SDLActions v) s"
unfolding SDLActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma SDLActions_StatePart [simp]:
  shows "StatePart (SDLActions v) = (\<lambda>s. s)"
unfolding SDLActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SDLActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStoreVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (SDLActions v) m"
unfolding SDLActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'SDR}\<close>

thm dfn'SDR_alt_def

definition SDRActions where
  "SDRActions \<equiv> \<lambda>(base, rt, offset). 
   bind (LegacyStoreVirtualAddress base offset)
        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr AND NOT mask 3, STORE)))
        (\<lambda>x. return (case x of None \<Rightarrow> {} | 
                               Some pAddr \<Rightarrow> 
                                 {StoreDataAction (RegSpecial 0) 
                                                  pAddr
                                                  ((ucast vAddr AND mask 3) + 1)})))"

abbreviation getSDRActions where
  "getSDRActions v \<equiv> ValuePart (SDRActions v)"

lemma SDRActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (SDRActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (SDRActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (SDRActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (SDRActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (SDRActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (SDRActions v) s"
unfolding SDRActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma SDRActions_StatePart [simp]:
  shows "StatePart (SDRActions v) = (\<lambda>s. s)"
unfolding SDRActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_SDRActions [Commute_compositeI]:
  assumes "\<And>b offset. Commute (LegacyStoreVirtualAddress b offset) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (SDRActions v) m"
unfolding SDRActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'CStore}\<close>

thm dfn'CStore_alt_def

definition CStoreVirtualAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                     8 word \<Rightarrow> 2 word \<Rightarrow> state \<Rightarrow> 
                                     VirtualAddress \<times> state" where 
  "CStoreVirtualAddress cb rt offset t \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. bind (read_state (getGPR rt))
        (\<lambda>v. return (getBase cap + getOffset cap + v + (scast offset << unat t))))"

abbreviation getCStoreVirtualAddress where
  "getCStoreVirtualAddress cb rt offset t \<equiv> ValuePart (CStoreVirtualAddress cb rt offset t)"

lemma CStoreVirtualAddress_StatePart [simp]:
  shows "StatePart (CStoreVirtualAddress cb rt offset t) = (\<lambda>s. s)"
unfolding CStoreVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CStoreVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
      and "Commute (read_state (getGPR rt)) m"
  shows "Commute (CStoreVirtualAddress cb rt offset t) m"
unfolding CStoreVirtualAddress_def
using assms
by auto

definition CStorePhysicalAddress :: "RegisterAddress \<Rightarrow> RegisterAddress \<Rightarrow> 
                                     8 word \<Rightarrow> 2 word \<Rightarrow> state \<Rightarrow> 
                                     PhysicalAddress option \<times> state" where 
  "CStorePhysicalAddress cb rt offset t \<equiv> 
   bind (CStoreVirtualAddress cb rt offset t)
        (\<lambda>a. read_state (getPhysicalAddress (a, STORE)))"

abbreviation getCStorePhysicalAddress where
  "getCStorePhysicalAddress cb rt offset t \<equiv> ValuePart (CStorePhysicalAddress cb rt offset t)"

lemma CStorePhysicalAddress_StatePart [simp]:
  shows "StatePart (CStorePhysicalAddress cb rt offset t) = (\<lambda>s. s)"
unfolding CStorePhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CStorePhysicalAddress [Commute_compositeI]:
  assumes "Commute (CStoreVirtualAddress cb rt offset t) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CStorePhysicalAddress cb rt offset t) m"
unfolding CStorePhysicalAddress_def
using assms
by auto

definition CStoreActions where
  "CStoreActions \<equiv> \<lambda>(rs, cb, rt, offset, t). 
   bind (CStorePhysicalAddress cb rt offset t)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {StoreDataAction (RegNormal cb) x (2 ^ unat t)}))"

abbreviation getCStoreActions where
  "getCStoreActions v \<equiv> ValuePart (CStoreActions v)"

lemma CStoreActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CStoreActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CStoreActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CStoreActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CStoreActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CStoreActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CStoreActions v) s"
unfolding CStoreActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma CStoreActions_StatePart [simp]:
  shows "StatePart (CStoreActions v) = (\<lambda>s. s)"
unfolding CStoreActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CStoreActions [Commute_compositeI]:
  assumes "\<And>cb rt offset t. Commute (CStorePhysicalAddress cb rt offset t) m"
  shows "Commute (CStoreActions v) m"
unfolding CStoreActions_def
by (Commute intro: assms)

subsubsection \<open>@{const dfn'CSCx}\<close>

thm dfn'CSCx_alt_def

definition CSCxVirtualAddress where 
  "CSCxVirtualAddress cb \<equiv> 
   bind (read_state (getCAPR cb))
        (\<lambda>cap. return (getBase cap + getOffset cap))"

abbreviation getCSCxVirtualAddress where
  "getCSCxVirtualAddress cb \<equiv> ValuePart (CSCxVirtualAddress cb)"

lemma CSCxVirtualAddress_StatePart [simp]:
  shows "StatePart (CSCxVirtualAddress cb) = (\<lambda>s. s)"
unfolding CSCxVirtualAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCxVirtualAddress [Commute_compositeI]:
  assumes "Commute (read_state (getCAPR cb)) m"
  shows "Commute (CSCxVirtualAddress cb) m"
unfolding CSCxVirtualAddress_def
using assms
by auto

definition CSCxPhysicalAddress :: "RegisterAddress \<Rightarrow> state \<Rightarrow> 
                                   PhysicalAddress option \<times> state" where 
  "CSCxPhysicalAddress cb \<equiv> 
   bind (CSCxVirtualAddress cb)
        (\<lambda>a. read_state (getPhysicalAddress (a, STORE)))"

abbreviation getCSCxPhysicalAddress where
  "getCSCxPhysicalAddress cb \<equiv> ValuePart (CSCxPhysicalAddress cb)"

lemma CSCxPhysicalAddress_StatePart [simp]:
  shows "StatePart (CSCxPhysicalAddress cb) = (\<lambda>s. s)"
unfolding CSCxPhysicalAddress_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCxPhysicalAddress [Commute_compositeI]:
  assumes "Commute (CSCxVirtualAddress cb) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
  shows "Commute (CSCxPhysicalAddress cb) m"
unfolding CSCxPhysicalAddress_def
using assms
by auto

definition CSCxActions where
  "CSCxActions \<equiv> \<lambda>(rs, cb, rd, t). 
   bind (CSCxPhysicalAddress cb)
        (\<lambda>a. return (case a of None \<Rightarrow> {} | 
                               Some x \<Rightarrow> {StoreDataAction (RegNormal cb) x (2 ^ unat t)}))"

abbreviation getCSCxActions where
  "getCSCxActions v \<equiv> ValuePart (CSCxActions v)"

lemma CSCxActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart (CSCxActions v) s"
    and "RestrictCapAction r r' \<notin> ValuePart (CSCxActions v) s"
    and "LoadCapAction auth a cd \<notin> ValuePart (CSCxActions v) s"
    and "StoreCapAction auth cd a \<notin> ValuePart (CSCxActions v) s"
    and "SealCapAction auth cd cd' \<notin> ValuePart (CSCxActions v) s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart (CSCxActions v) s"
unfolding CSCxActions_def
by (auto simp: ValueAndStatePart_simp split: option.splits)

lemma CSCxActions_StatePart [simp]:
  shows "StatePart (CSCxActions v) = (\<lambda>s. s)"
unfolding CSCxActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_CSCxActions [Commute_compositeI]:
  assumes "\<And>cb. Commute (CSCxPhysicalAddress cb) m"
  shows "Commute (CSCxActions v) m"
unfolding CSCxActions_def
by (Commute intro: assms)

subsection \<open>@{const Run}\<close>

thm Run_alt_def

definition RunActions where
  "RunActions v \<equiv>
   case v of COP2 (CHERICOP2 (CSet (CAndPerm v))) \<Rightarrow> CAndPermActions v
           | COP2 (CHERICOP2 (CBuildCap v)) \<Rightarrow> CBuildCapActions v
           | COP2 (CHERICOP2 (CClearHi v)) \<Rightarrow> CClearHiActions v
           | COP2 (CHERICOP2 (CClearLo v)) \<Rightarrow> CClearLoActions v
           | COP2 (CHERICOP2 (CSet (CClearTag v))) \<Rightarrow> CClearTagActions v
           | COP2 (CHERICOP2 (CCopyType v)) \<Rightarrow> CCopyTypeActions v
           | COP2 (CHERICOP2 (CSet (CFromPtr v))) \<Rightarrow> CFromPtrActions v
           | COP2 (CHERICOP2 (CGet (CGetPCC v))) \<Rightarrow> CGetPCCActions v
           | COP2 (CHERICOP2 (CGet (CGetPCCSetOffset v))) \<Rightarrow> CGetPCCSetOffsetActions v
           | COP2 (CHERICOP2 (CSet (CIncOffset v))) \<Rightarrow> CIncOffsetActions v
           | COP2 (CHERICOP2 (CSet (CIncOffsetImmediate v))) \<Rightarrow> CIncOffsetImmediateActions v
           | COP2 (CHERICOP2 (CJALR v)) \<Rightarrow> CJALRActions v
           | COP2 (CHERICOP2 (CJR v)) \<Rightarrow> CJRActions v
           | LDC2 (CHERILDC2 (CLC v)) \<Rightarrow> CLCActions v
           | COP2 (CHERICOP2 (CLLC v)) \<Rightarrow> CLLCActions v
           | COP2 (CHERICOP2 (CMOVN v)) \<Rightarrow> CMOVNActions v
           | COP2 (CHERICOP2 (CMOVZ v)) \<Rightarrow> CMOVZActions v
           | COP2 (CHERICOP2 (CMove v)) \<Rightarrow> CMoveActions v
           | COP2 (CHERICOP2 (CReadHwr v)) \<Rightarrow> CReadHwrActions v
           | SDC2 (CHERISDC2 (CSC v)) \<Rightarrow> CSCActions v
           | COP2 (CHERICOP2 (CSCC v)) \<Rightarrow> CSCCActions v
           | COP2 (CHERICOP2 (CSeal v)) \<Rightarrow> CSealActions v
           | COP2 (CHERICOP2 (CSet (CSetBounds v))) \<Rightarrow> CSetBoundsActions v 
           | COP2 (CHERICOP2 (CSet (CSetBoundsExact v))) \<Rightarrow> CSetBoundsExactActions v
           | COP2 (CHERICOP2 (CSet (CSetBoundsImmediate v))) \<Rightarrow> CSetBoundsImmediateActions v
           | COP2 (CHERICOP2 (CSet (CSetOffset v))) \<Rightarrow> CSetOffsetActions v
           | COP2 (CHERICOP2 (CUnseal v)) \<Rightarrow> CUnsealActions v
           | COP2 (CHERICOP2 (CWriteHwr v)) \<Rightarrow> CWriteHwrActions v
           | ERET \<Rightarrow> ERETActions
           | Load (LB v) \<Rightarrow> LBActions v
           | Load (LBU v) \<Rightarrow> LBUActions v
           | Load (LH v) \<Rightarrow> LHActions v
           | Load (LHU v) \<Rightarrow> LHUActions v
           | Load (LW v) \<Rightarrow> LWActions v
           | Load (LWU v) \<Rightarrow> LWUActions v
           | Load (LL v) \<Rightarrow> LLActions v
           | Load (LD v) \<Rightarrow> LDActions v
           | Load (LLD v) \<Rightarrow> LLDActions v
           | Load (LWL v) \<Rightarrow> LWLActions v
           | Load (LWR v) \<Rightarrow> LWRActions v
           | Load (LDL v) \<Rightarrow> LDLActions v
           | Load (LDR v) \<Rightarrow> LDRActions v
           | LWC2 (CHERILWC2 (CLoad v)) \<Rightarrow> CLoadActions v
           | COP2 (CHERICOP2 (CLLx v)) \<Rightarrow> CLLxActions v
           | Store (SB v) \<Rightarrow> SBActions v
           | Store (SH v) \<Rightarrow> SHActions v
           | Store (SW v) \<Rightarrow> SWActions v
           | Store (SD v) \<Rightarrow> SDActions v
           | Store (SC v) \<Rightarrow> SCActions v
           | Store (SCD v) \<Rightarrow> SCDActions v
           | Store (SWL v) \<Rightarrow> SWLActions v
           | Store (SWR v) \<Rightarrow> SWRActions v
           | Store (SDL v) \<Rightarrow> SDLActions v
           | Store (SDR v) \<Rightarrow> SDRActions v
           | SWC2 (CHERISWC2 (CStore v)) \<Rightarrow> CStoreActions v
           | COP2 (CHERICOP2 (CSCx v)) \<Rightarrow> CSCxActions v
           | _ \<Rightarrow> return {}"

abbreviation getRunActions where
  "getRunActions v \<equiv> ValuePart (RunActions v)"

lemma RunActions_StatePart [simp]:
  shows "StatePart (RunActions v) = (\<lambda>s. s)"
unfolding RunActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_RunActions [Commute_compositeI]:
  assumes "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
      and "\<And>v. Commute (read_state (getCAPR v)) m"
      and "\<And>v. Commute (read_state (getSCAPR v)) m"
      and "\<And>v. Commute (read_state (getGPR v)) m"
      and "\<And>cb. Commute (read_state getLLbit) m"
  shows "Commute (RunActions v) m"
unfolding RunActions_def
by (Commute_find_dependencies 
      intro: assms
             Commute_CAndPermActions
             Commute_CBuildCapActions
             Commute_CClearHiActions
             Commute_CClearLoActions
             Commute_CClearTagActions
             Commute_CCopyTypeActions
             Commute_CFromPtrActions
             Commute_CGetPCCActions
             Commute_CGetPCCSetOffsetActions
             Commute_CIncOffsetActions
             Commute_CIncOffsetImmediateActions
             Commute_CJALRActions
             Commute_CJRActions
             Commute_CLCVirtualAddress
             Commute_CLCPhysicalAddress
             Commute_CLCActions
             Commute_CLLCVirtualAddress
             Commute_CLLCPhysicalAddress
             Commute_CLLCActions
             Commute_CMOVNActions
             Commute_CMOVZActions
             Commute_CMoveActions
             Commute_CReadHwrActions
             Commute_CSCVirtualAddress
             Commute_CSCPhysicalAddress
             Commute_CSCActions
             Commute_CSCCVirtualAddress
             Commute_CSCCPhysicalAddress
             Commute_CSCCActions
             Commute_CSealActions
             Commute_CSetBoundsActions
             Commute_CSetBoundsExactActions
             Commute_CSetBoundsImmediateActions
             Commute_CSetOffsetActions
             Commute_CUnsealActions
             Commute_CWriteHwrActions
             Commute_ERETActions
             Commute_LegacyLoadVirtualAddress
             Commute_LegacyLoadPhysicalAddress
             Commute_LBActions
             Commute_LBUActions
             Commute_LHActions
             Commute_LHUActions
             Commute_LWActions
             Commute_LWUActions
             Commute_LLActions
             Commute_LDActions
             Commute_LLDActions
             Commute_LWLActions
             Commute_LWRActions
             Commute_LDLActions
             Commute_LDRActions
             Commute_CLoadVirtualAddress
             Commute_CLoadPhysicalAddress
             Commute_CLoadActions
             Commute_CLLxVirtualAddress
             Commute_CLLxPhysicalAddress
             Commute_CLLxActions
             Commute_LegacyStoreVirtualAddress
             Commute_LegacyStorePhysicalAddress
             Commute_SBActions
             Commute_SHActions
             Commute_SWActions
             Commute_SDActions
             Commute_SCActions
             Commute_SCDActions
             Commute_SWLActions
             Commute_SWRActions
             Commute_SDLActions
             Commute_SDRActions
             Commute_CStoreVirtualAddress
             Commute_CStorePhysicalAddress
             Commute_CStoreActions
             Commute_CSCxVirtualAddress
             Commute_CSCxPhysicalAddress
             Commute_CSCxActions)

subsection \<open>@{const TakeBranch}\<close>

thm TakeBranch_def

definition TakeBranchActions where
  "TakeBranchActions \<equiv>
   bind (read_state BranchDelayPCC)
        (\<lambda>v. if is_some v then return {RestrictCapAction RegBranchDelayPCC RegBranchDelayPCC,
                                       RestrictCapAction RegBranchDelayPCC RegPCC} 
             else return {})"

abbreviation getTakeBranchActions where
  "getTakeBranchActions \<equiv> ValuePart TakeBranchActions"

lemma TakeBranchActions_simps [simp]:
  shows "LoadDataAction auth a' l \<notin> ValuePart TakeBranchActions s"
    and "StoreDataAction auth a' l \<notin> ValuePart TakeBranchActions s"
    and "RestrictCapAction RegPCC loc' \<notin> ValuePart TakeBranchActions s"
    and "RestrictCapAction (RegNormal cd) loc' \<notin> ValuePart TakeBranchActions s"
    and "RestrictCapAction loc (RegNormal cd') \<notin> ValuePart TakeBranchActions s"
    and "LoadCapAction auth a cd \<notin> ValuePart TakeBranchActions s"
    and "StoreCapAction auth cd a \<notin> ValuePart TakeBranchActions s"
    and "SealCapAction auth cd cd' \<notin> ValuePart TakeBranchActions s"
    and "UnsealCapAction auth cd cd' \<notin> ValuePart TakeBranchActions s"
unfolding TakeBranchActions_def
by (auto simp: ValueAndStatePart_simp)

lemma TakeBranchActions_StatePart [simp]:
  shows "StatePart TakeBranchActions = (\<lambda>s. s)"
unfolding TakeBranchActions_def
by (auto simp: ValueAndStatePart_simp)

lemma Commute_TakeBranchActions [Commute_compositeI]:
  assumes "Commute (read_state BranchDelayPCC) m"
  shows "Commute TakeBranchActions m"
unfolding TakeBranchActions_def
using assms
by - Commute_find_dependencies

subsection \<open>@{const Next}\<close>

definition DomainActions where
  "DomainActions \<equiv>
   bind NextInstruction
        (\<lambda>inst. case inst of None \<Rightarrow> return {} 
                           | Some w \<Rightarrow> bind (RunActions (Decode w))
                                            (\<lambda>x. bind TakeBranchActions
                                            (\<lambda>y. return (x \<union> y))))"

abbreviation getDomainActions where
  "getDomainActions \<equiv> ValuePart DomainActions"

lemma DomainActions_StatePart [simp]:
  shows "StatePart DomainActions = (\<lambda>s. s)"
unfolding DomainActions_def
by (auto simp: ValueAndStatePart_simp cong: cong)

lemma Commute_DomainActions [Commute_compositeI]:
  assumes "Commute NextInstruction m"
      and "\<And>v. Commute (RunActions v) m"
      and "Commute TakeBranchActions m"
  shows "Commute DomainActions m"
unfolding DomainActions_def
using assms
by - Commute_find_dependencies

section \<open>Domain switches\<close>

lemma COP2ElseTrue [intro!]: 
  assumes "\<And>y. x = COP2 y \<Longrightarrow> f y"
  shows "case x of COP2 y \<Rightarrow> f y | _ \<Rightarrow> True"
using assms
by (auto split: instruction.split)

lemma CHERICOP2ElseTrue [intro!]: 
  assumes "\<And>y. x = CHERICOP2 y \<Longrightarrow> f y"
  shows "case x of CHERICOP2 y \<Rightarrow> f y"
using assms
by (auto split: COP2.split)

lemma CCallFastElseTrue [intro!]: 
  assumes "\<And>y. x = CCallFast y \<Longrightarrow> f y"
  shows "case x of CCallFast y \<Rightarrow> f y | _ \<Rightarrow> True"
using assms
by (auto split: CHERICOP2.split)

definition CCallFastInstructionParam where
  "CCallFastInstructionParam s \<equiv>
   case getNextInstruction s of 
     None \<Rightarrow> None
   | Some w \<Rightarrow> (case Decode w of 
                  COP2 (CHERICOP2 (CCallFast v)) \<Rightarrow> Some v
                | _ \<Rightarrow> None)"

lemma CCallFastInstructionParam_split:
  shows "Q (CCallFastInstructionParam s) = 
         ((getNextInstruction s = None \<longrightarrow> Q None) \<and>
          (\<forall>w. getNextInstruction s = Some w \<longrightarrow> 
               (\<forall>v. Decode w = COP2 (CHERICOP2 (CCallFast v)) \<longrightarrow> Q (Some v)) \<and>
               (\<exists>v. Decode w \<noteq> COP2 (CHERICOP2 (CCallFast v)) \<longrightarrow> Q None)))"
unfolding CCallFastInstructionParam_def
by (auto split: all_split)

lemma CCallFastInstructionParam_None:
  assumes "CCallFastInstructionParam s = None"
  obtains "getNextInstruction s = None"
  | w where "getNextInstruction s = Some w" 
            "\<And>v. Decode w \<noteq> COP2 (CHERICOP2 (CCallFast v))"
using assms
unfolding CCallFastInstructionParam_split[where Q="\<lambda>x. x = _"]
by auto

lemma CCallFastInstructionParam_None_sym:
  assumes "None = CCallFastInstructionParam s"
  obtains "getNextInstruction s = None"
  | w where "getNextInstruction s = Some w" 
            "\<And>v. Decode w \<noteq> COP2 (CHERICOP2 (CCallFast v))"
using CCallFastInstructionParam_None[OF assms[THEN sym]]
by metis

lemma CCallFastInstructionParam_Some:
  assumes "CCallFastInstructionParam s = Some v"
  obtains w where "getNextInstruction s = Some w"
                  "Decode w = COP2 (CHERICOP2 (CCallFast v))"
using assms
unfolding CCallFastInstructionParam_split[where Q="\<lambda>x. x = _"]
by auto

lemma CCallFastInstructionParam_Some_sym:
  assumes "Some v = CCallFastInstructionParam s"
  obtains w where "getNextInstruction s = Some w"
                  "Decode w = COP2 (CHERICOP2 (CCallFast v))"
using CCallFastInstructionParam_Some[OF assms[THEN sym]]
by metis

definition NextNonExceptionStep where
  "NextNonExceptionStep s \<equiv> 
   case CCallFastInstructionParam s of 
     None \<Rightarrow> KeepDomain (ValuePart DomainActions s)
   | Some v \<Rightarrow> SwitchDomain (InvokeCapability (fst v) (snd v))"

lemma NextNonExceptionStep_RaiseException [simp]:
  shows "(NextNonExceptionStep s = SwitchDomain RaiseException) = False"
    and "(SwitchDomain RaiseException = NextNonExceptionStep s) = False"
unfolding NextNonExceptionStep_def
by (auto split: option.splits)

section \<open>Next states\<close>

text \<open>The following is a version of \<open>Next\<close> (the function that defines the semantics of CHERI) that
takes unpredictable behaviour into account.\<close>

definition NextStates where
  "NextStates s \<equiv> 
   if isUnpredictable (StatePart NextWithGhostState s) then 
     {(KeepDomain {}, s') |s'. s' \<in> UnpredictableNext s}
   else if getExceptionSignalled (StatePart NextWithGhostState s) then 
     {(SwitchDomain RaiseException, StatePart Next s)}
   else {(NextNonExceptionStep s, StatePart Next s)}"

lemma NextStates_Exception [elim!]:
  assumes "(SwitchDomain RaiseException, s') \<in> NextStates s"
  shows "\<not> isUnpredictable (StatePart NextWithGhostState s)"
    and "getExceptionSignalled (StatePart NextWithGhostState s)"
    and "s' = StatePart Next s"
using assms
unfolding NextStates_def
by (auto split: if_splits)

lemma NextStates_PredictableNonException:
  assumes suc: "(step, s') \<in> NextStates s"
      and no_ex: "step \<noteq> SwitchDomain RaiseException"
      and pred: "\<not> isUnpredictable (StatePart NextWithGhostState s)"
  shows "\<not> getExceptionSignalled (StatePart NextWithGhostState s)"
    and "StatePart Next s = StatePart NextWithGhostState s"
    and "s' = StatePart Next s"
using assms
unfolding Next_NextWithGhostState NextStates_def
by (auto simp: ValueAndStatePart_simp split: if_splits)

text \<open>To check the correspondence with the semantics as defined in L3.\<close>

lemma DefinedNext_NextStates:
  assumes "\<not> isUnpredictable (StatePart Next s)"
  shows "\<exists>action. NextStates s = {(action, StatePart Next s)}"
proof -  
  have "\<not> isUnpredictable (StatePart NextWithGhostState s)"
    using assms 
    unfolding Next_NextWithGhostState
    by (simp add: ValueAndStatePart_simp)
  thus ?thesis
    unfolding NextStates_def Let_def
    unfolding Next_NextWithGhostState
    by auto
qed

(*<*)
end
(*>*)