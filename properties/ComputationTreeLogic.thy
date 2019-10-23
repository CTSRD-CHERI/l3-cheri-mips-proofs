(*<*)

(* Author: Kyndylan Nienhuis *)

theory ComputationTreeLogic

imports 
  Main
  LinearTemporalLogic
begin

(*>*)
section \<open>Computation tree logic\<close>

subsection \<open>The model\<close>

text \<open>We specify the model as a locale so we can later interpret it with an actual transition
system.\<close>

locale TransitionSystem =
  fixes \<M> :: "('a \<times> 'a) set"

context TransitionSystem
begin

definition Paths :: "'a \<Rightarrow> ('a path) set" where
  "Paths s = {p |p. p 0 = s \<and> (\<forall>i. (p i, p (Suc i)) \<in> \<M>)}"

lemma PathI [intro]:
  assumes "p 0 = s"
      and "\<And>i. (p i, p (Suc i)) \<in> \<M>"
  shows "p \<in> Paths s"
using assms
unfolding Paths_def
by auto

lemma PathE [elim!]:
  assumes "p \<in> Paths s"
  shows "p 0 = s"
    and "(p i, p (Suc i)) \<in> \<M>"
using assms
unfolding Paths_def
by auto  

subsection \<open>Path quantifiers\<close>

definition PathEx :: "'a ltl \<Rightarrow> 'a pred" ("E _" [90] 90) where
  "E \<phi> \<equiv> \<lambda>s. \<exists>p\<in>Paths s. \<phi> p"

definition PathAll :: "'a ltl \<Rightarrow> 'a pred" ("A _" [90] 90) where
  "A \<phi> \<equiv> \<lambda>s. \<forall>p\<in>Paths s. \<phi> p"

subsubsection \<open>Intros and elims\<close>

lemma PathExI [intro]:
  assumes "p \<in> Paths s"
      and "\<phi> p"
  shows "(E \<phi>) s"
using assms
unfolding PathEx_def
by auto

lemma PathExE [elim]:
  assumes "(E \<phi>) s"
  obtains p where "p \<in> Paths s" "\<phi> p"
using assms
unfolding PathEx_def
by auto

lemma PathAllI [intro]:
  assumes "\<And>p. p \<in> Paths s \<Longrightarrow> \<phi> p"
  shows "(A \<phi>) s"
using assms
unfolding PathAll_def
by auto

lemma PathAllE [elim]:
  assumes "(A \<phi>) s"
      and "p \<in> Paths s"
  shows "\<phi> p"
using assms
unfolding PathAll_def
by auto

subsubsection \<open>Distributive lemmas\<close>

lemma not_PathEx:
  shows "- E \<phi> = A (- \<phi>)"
unfolding PathAll_def PathEx_def
by auto

lemma not_PathAll:
  shows "- A \<phi> = E (- \<phi>)"
unfolding PathEx_def PathAll_def
by (intro ext) auto

lemma PathEx_disj:
  shows "E (\<phi> \<squnion> \<psi>) = E \<phi> \<squnion> E \<psi>"
unfolding PathEx_def
by auto

lemma PathEx_Disj:
  shows "E (\<Squnion>\<Phi>) = \<Squnion>{E \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding PathEx_def
by auto

lemma PathAll_conj:
  shows "A (\<phi> \<sqinter> \<psi>) = A \<phi> \<sqinter> A \<psi>"
unfolding PathAll_def
by auto

lemma PathAll_Conj:
  shows "A (\<Sqinter>\<Phi>) = \<Sqinter>{A \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding PathAll_def
by (intro ext) (auto simp add: setcompr_eq_image)

end

(*<*)
end
(*>*)
