(*<*)

(* Author: Kyndylan Nienhuis *)

theory LinearTemporalLogic

imports 
  Main
begin

(*>*)
section \<open>Linear temporal logic\<close>

subsection \<open>Paths\<close>

text \<open>The definition of \<open>prefix\<close>, \<open>suffix\<close> and \<open>conc\<close> are from \<open>HOL.Library.Omega_Words_Fun\<close> based
on Stefan Merz's work. We avoid the term \<open>word\<close> because we already use it for machine words.\<close>

type_synonym 'a path = "nat \<Rightarrow> 'a"

definition Suffix :: "nat \<Rightarrow> 'a path \<Rightarrow> 'a path" where
  "Suffix k p \<equiv> \<lambda>n. p (k + n)"

lemma Suffix_zero [simp]: 
  shows "Suffix 0 p = p"
by (simp add: Suffix_def)

lemma Suffix_nth [simp]: 
  shows "(Suffix k p) n = p (k + n)"
by (simp add: Suffix_def)

lemma Suffix_Suffix [simp]:
  shows "Suffix n (Suffix m p) = Suffix (m + n) p"
unfolding Suffix_def
by (intro ext) (simp add: add.commute add.left_commute)

definition Prefix :: "nat \<Rightarrow> 'a path \<Rightarrow> 'a list" where
  "Prefix k p \<equiv> map p [0..<k]"

lemma length_Prefix [simp]:
  shows "length (Prefix k p) = k"
unfolding Prefix_def
by simp

lemma Prefix_zero [simp]: 
  shows "Prefix 0 p = []"
by (simp add: Prefix_def)

lemma Prefix_nth [simp]:
  assumes "n < k"
  shows "(Prefix k p)!n = p n"
proof -
  have "n < length (Prefix k p)"
    using assms by simp
  thus ?thesis
    by (simp add: Prefix_def)
qed

definition Conc :: "['a list, 'a path] \<Rightarrow> 'a path" (infixr "\<frown>" 65) where
  "l \<frown> p \<equiv> \<lambda>n. if n < length l then l!n else p (n - length l)"

lemma Conc_empty [simp]: 
  shows "[] \<frown> p = p"
unfolding Conc_def by auto

lemma Prefix_Suffix: 
  shows "p = (Prefix n p) \<frown> (Suffix n p)"
by (rule ext) (simp add: Prefix_def Conc_def)

lemmas Prefix_Suffix_sym [simp] = Prefix_Suffix[THEN sym]

subsection \<open>Shallow embedding\<close>

text \<open>We identify a predicate with a function from \<open>'a\<close> to bool.\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

text \<open>We then define LTL formula as a predicate over paths.\<close>

type_synonym 'a ltl = "'a path pred"

subsubsection \<open>Lifting boolean operators\<close>

text \<open>True, false, negation, conjunction and disjunction are already defined for functions to
booleans. We use the notation from lattices: respectively \<open>\<top>\<close>, \<open>\<bottom>\<close>, \<open>-\<close>, \<open>\<sqinter>\<close> and \<open>\<squnion>\<close>. We then lift
the definition of implication following \<open>HOL-ex.CTL\<close> by Gertrud Bauer. For the lifted version we use
the short arrow \<open>\<rightarrow>\<close> instead of the longer \<open>\<longrightarrow>\<close> used for implications over booleans.\<close>

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

definition set_imp :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred"  (infixr "\<rightarrow>" 75) where
  "\<phi> \<rightarrow> \<psi> \<equiv> - \<phi> \<squnion> \<psi>"

lemma imp_true_false [simp]:
  shows "bot \<rightarrow> \<phi> = top"
    and "top \<rightarrow> \<phi> = \<phi>"
    and "\<phi> \<rightarrow> bot = - \<phi>"
    and "\<phi> \<rightarrow> top = top"
unfolding set_imp_def
by auto

lemma impI [intro]:
  assumes "\<phi> s \<Longrightarrow> \<psi> s"
  shows "(\<phi> \<rightarrow> \<psi>) s"
using assms
unfolding set_imp_def
by auto

lemma impD [dest]:
  assumes "(\<phi> \<rightarrow> \<psi>) s"
  shows "\<phi> s \<Longrightarrow> \<psi> s"
using assms
unfolding set_imp_def
by auto

subsection \<open>Atom\<close>

definition Atom :: "'a pred \<Rightarrow> 'a ltl" where 
  "Atom \<phi> \<equiv> \<lambda>p. \<phi> (p 0)"

lemma Atom_applied [simp]:
  shows "Atom \<phi> p = \<phi> (p 0)"
unfolding Atom_def ..

subsubsection \<open>Distributive lemmas\<close>

lemma not_Atom:
  shows "- (Atom \<phi>) = Atom (- \<phi>)"
by (intro ext) auto

lemma Atom_disj:
  shows "Atom (\<phi> \<squnion> \<psi>) = Atom \<phi> \<squnion> Atom \<psi>"
by (intro ext) auto

lemma Atom_Disj:
  shows "Atom (\<Squnion>\<Phi>) = \<Squnion>{Atom \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding Atom_def
by auto

lemma Atom_conj:
  shows "Atom (\<phi> \<sqinter> \<psi>) = Atom \<phi> \<sqinter> Atom \<psi>"
by (intro ext) auto

lemma Atom_Conj:
  shows "Atom (\<Sqinter>\<Phi>) = \<Sqinter>{Atom \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding Atom_def
by (auto simp add: setcompr_eq_image)

subsection \<open>Skip, Next\<close>

definition Skip :: "nat \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" where 
  "Skip n \<phi> \<equiv> \<lambda>p. \<phi> (Suffix n p)"

abbreviation Next :: "'a ltl \<Rightarrow> 'a ltl" ("X _" [90] 90) where 
  "Next \<equiv> Skip (Suc 0)"

lemma Skip_zero [simp]:
  shows "Skip 0 \<phi> = \<phi>"
unfolding Skip_def
by simp

lemma Skip_Skip [simp]:
  shows "Skip n (Skip m \<phi>) = Skip (n + m) \<phi>"
unfolding Skip_def
by simp

lemma Skip_applied [simp]:
  shows "(Skip n \<phi>) p = \<phi> (Suffix n p)"
unfolding Skip_def ..

subsubsection \<open>Distributive lemmas\<close>

lemma not_Skip:
  shows "- (Skip n \<phi>) = Skip n (- \<phi>)"
by (intro ext) auto

lemma Skip_disj:
  shows "Skip n (\<phi> \<squnion> \<psi>) = Skip n \<phi> \<squnion> Skip n \<psi>"
by (intro ext) auto

lemma Skip_Disj:
  shows "Skip n (\<Squnion>\<Phi>) = \<Squnion>{Skip n \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding Skip_def
by auto

lemma Skip_conj:
  shows "Skip n (\<phi> \<sqinter> \<psi>) = Skip n \<phi> \<sqinter> Skip n \<psi>"
by (intro ext) auto

lemma Skip_Conj:
  shows "Skip n (\<Sqinter>\<Phi>) = \<Sqinter>{Skip n \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding Skip_def
by (auto simp add: setcompr_eq_image)

subsection \<open>Bounded finally and globally\<close>

definition BoundedFinally :: "nat \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("BF _ _" [90, 90] 90) where
  "BF n \<phi> \<equiv> \<Squnion>{Skip i \<phi> |i. i \<le> n}"

definition BoundedGlobally :: "nat \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("BG _ _" [90, 90] 90) where
  "BG n \<phi> \<equiv> \<Sqinter>{Skip i \<phi> |i. i \<le> n}"

lemma BoundedFinally_zero [simp]:
  shows "BF 0 \<phi> = \<phi>"
unfolding BoundedFinally_def
by auto

lemma BoundedGlobally_zero [simp]:
  shows "BG 0 \<phi> = \<phi>"
unfolding BoundedGlobally_def
by auto

lemma BoundedFinally_applied:
  shows "(BF n \<phi>) p = (\<exists>i\<le>n. \<phi> (Suffix i p))"
unfolding BoundedFinally_def
by force

lemma BoundedGlobally_applied:
  shows "(BG n \<phi>) p = (\<forall>i\<le>n. \<phi> (Suffix i p))"
unfolding BoundedGlobally_def 
by force

subsubsection \<open>Intros and elims\<close>

lemma BoundedFinallyI [intro]:
  assumes "\<phi> (Suffix i p)"
      and "i \<le> n"
  shows "(BF n \<phi>) p"
using assms
unfolding BoundedFinally_applied
by auto

lemma BoundedFinallyE [elim]:
  assumes "(BF n \<phi>) p"
  obtains i where "\<phi> (Suffix i p)" "i \<le> n"
using assms
unfolding BoundedFinally_applied
by auto

lemma BoundedGloballyI [intro]:
  assumes "\<And>i. i \<le> n \<Longrightarrow> \<phi> (Suffix i p)"
  shows "(BG n \<phi>) p"
using assms
unfolding BoundedGlobally_applied
by auto

lemma BoundedGloballyE [elim]:
  assumes "(BG n \<phi>) p"
      and "i \<le> n"
  shows "\<phi> (Suffix i p)"
using assms
unfolding BoundedGlobally_applied
by auto

subsubsection \<open>Changing prefix\<close>

lemma IncreaseBoundedFinally [elim]:
  assumes "(BF n \<phi>) p"
      and "n \<le> k"
  shows "(BF k \<phi>) p"
proof -
  obtain i where "\<phi> (Suffix i p)" "i \<le> n"
    using assms
    by auto
  thus ?thesis 
    using assms
    by auto
qed

lemma DecreaseBoundedGlobally [elim]:
  assumes "(BG n \<phi>) p"
      and "k \<le> n"
  shows "(BG k \<phi>) p"
using assms
unfolding BoundedGlobally_applied
by auto

lemma PredecessorBoundedGlobally [elim!]:
  assumes "(BG (Suc n) \<phi>) p"
  shows "(BG n \<phi>) p"
using assms
by auto

lemma SuccessorBoundedGlobally [elim!]:
  assumes "(BG n \<phi>) p"
      and "\<phi> (Suffix (Suc n) p)"
  shows "(BG (Suc n) \<phi>) p"
proof
  fix i
  assume "i \<le> Suc n"
  show "\<phi> (Suffix i p)"
    proof (cases "i = Suc n")
      case True
      thus ?thesis
        using assms by auto
    next
      case False
      hence "i \<le> n"
        using `i \<le> Suc n`
        by auto
      thus ?thesis 
        using assms by auto
    qed
qed

corollary SuccessorBoundedGlobally_shifted [elim!]:
  assumes "(BG (n - Suc 0) \<phi>) p"
      and "\<phi> (Suffix n p)"
  shows "(BG n \<phi>) p"
using assms SuccessorBoundedGlobally[where n="n - 1"]
by (cases "n = 0") auto

subsubsection \<open>Distributive lemmas\<close>

lemma not_BoundedFinally:
  shows "- (BF n \<phi>) = BG n (- \<phi>)"
unfolding BoundedGlobally_def BoundedFinally_def 
by (intro ext) (auto simp add: setcompr_eq_image)

lemma not_BoundedGlobally:
  shows "- (BG n \<phi>) = BF n (- \<phi>)"
unfolding BoundedFinally_def BoundedGlobally_def
by (intro ext) (auto simp add: setcompr_eq_image)

lemma BoundedFinally_disj:
  shows "BF n (\<phi> \<squnion> \<psi>) = BF n \<phi> \<squnion> BF n \<psi>"
unfolding BoundedFinally_def
by (intro ext) (auto simp add: setcompr_eq_image)

lemma BoundedFinally_Disj:
  shows "BF n (\<Squnion>\<Phi>) = \<Squnion>{BF n \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding BoundedFinally_def
by (intro ext) (auto simp add: setcompr_eq_image)

lemma BoundedGlobally_conj:
  shows "BG n (\<phi> \<sqinter> \<psi>) = BG n \<phi> \<sqinter> BG n \<psi>"
unfolding BoundedGlobally_def
by (intro ext) (auto simp add: setcompr_eq_image)

lemma BoundedGlobally_Conj:
  shows "BG n (\<Sqinter>\<Phi>) = \<Sqinter>{BG n \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
unfolding BoundedGlobally_def
by (intro ext) (auto simp add: setcompr_eq_image)

subsection \<open>Finally and globally\<close>

definition Finally :: "'a ltl \<Rightarrow> 'a ltl" ("F _" [90] 90) where
  "F \<phi> \<equiv> \<Squnion>{Skip i \<phi> |i. True}"

definition Globally :: "'a ltl \<Rightarrow> 'a ltl" ("G _" [90] 90) where
  "G \<phi> \<equiv> \<Sqinter>{Skip i \<phi> |i. True}"

lemma Finally_applied:
  shows "(F \<phi>) p = (\<exists>i. \<phi> (Suffix i p))"
unfolding Finally_def
by force

lemma Globally_applied:
  shows "(G \<phi>) p = (\<forall>i. \<phi> (Suffix i p))"
unfolding Globally_def 
by force

subsubsection \<open>Intros and elims\<close>

lemma FinallyI [intro]:
  assumes "\<phi> (Suffix i p)"
  shows "(F \<phi>) p"
using assms
unfolding Finally_applied
by auto

lemma FinallyE [elim]:
  assumes "(F \<phi>) p"
  obtains i where "\<phi> (Suffix i p)"
using assms
unfolding Finally_applied
by auto

lemma GloballyI [intro]:
  assumes "\<And>i. \<phi> (Suffix i p)"
  shows "(G \<phi>) p"
using assms
unfolding Globally_applied
by auto

lemma GloballyE [elim!]:
  assumes "(G \<phi>) p"
  shows "\<phi> (Suffix i p)"
using assms
unfolding Globally_applied
by auto

lemma GloballyInduct [intro?, case_names base ih]:
  assumes base: "\<phi> p"
      and ih: "\<And>i. (Skip i \<phi>) p \<Longrightarrow> (Skip (Suc i) \<phi>) p"
  shows "(G \<phi>) p"
proof (rule, cases rule: nat.induct)
  show "\<phi> (Suffix 0 p)"
    using base by auto
next
  fix i
  assume "\<phi> (Suffix i p)"
  thus "\<phi> (Suffix (Suc i) p)"
    using ih by auto
qed

subsubsection \<open>Distributive lemmas\<close>

lemma Not_finally:
  shows "- (F \<phi>) = G (- \<phi>)"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied)

lemma Not_globally:
  shows "- (G \<phi>) = F (- \<phi>)"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied)

lemma Finally_disj:
  shows "F (\<phi> \<squnion> \<psi>) = F \<phi> \<squnion> F \<psi>"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied)

lemma Finally_Disj:
  shows "F (\<Squnion>\<Phi>) = \<Squnion>{F \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied setcompr_eq_image)

lemma Globally_conj:
  shows "G (\<phi> \<sqinter> \<psi>) = G \<phi> \<sqinter> G \<psi>"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied)

lemma Globally_Conj:
  shows "G (\<Sqinter>\<Phi>) = \<Sqinter>{G \<phi> |\<phi>. \<phi> \<in> \<Phi>}"
by (intro ext) 
   (auto simp add: Finally_applied Globally_applied setcompr_eq_image)

subsection \<open>Until and release\<close>

definition Until :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ U _" [90, 90] 89) where
  "\<phi> U \<psi> \<equiv> \<lambda>p. \<exists>i. \<psi> (Suffix i p) \<and> (\<forall>j<i. \<phi> (Suffix j p))"

definition WeakUntil :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ WU _" [90, 90] 89) where
  "\<phi> WU \<psi> \<equiv> \<lambda>p. \<exists>i. \<psi> (Suffix i p) \<and> (\<forall>j\<le>i. \<phi> (Suffix j p))"

definition Release :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ R _" [90, 90] 89) where
  "\<phi> R \<psi> \<equiv> \<lambda>p. \<forall>i. \<psi> (Suffix i p) \<or> (\<exists>j<i. \<phi> (Suffix j p))"

definition WeakRelease :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ WR _" [90, 90] 89) where
  "\<phi> WR \<psi> \<equiv> \<lambda>p. \<forall>i. \<psi> (Suffix i p) \<or> (\<exists>j\<le>i. \<phi> (Suffix j p))"

subsubsection \<open>Intros and elims\<close>

lemma ReleaseI [intro?]:
  assumes "\<And>i. \<psi> (Suffix i p) \<or> (\<exists>j<i. \<phi> (Suffix j p))"
  shows "(\<phi> R \<psi>) p"
using assms
unfolding Release_def
by auto

lemma WeakReleaseI [intro?]:
  assumes "\<And>i. \<psi> (Suffix i p) \<or> (\<exists>j\<le>i. \<phi> (Suffix j p))"
  shows "(\<phi> WR \<psi>) p"
using assms
unfolding WeakRelease_def
by auto

lemma ReleaseE [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "n \<noteq> 0 \<Longrightarrow> (BG (n - 1) (- \<phi>)) p"
  shows "\<psi> (Suffix n p)"
using assms
unfolding Release_def BoundedGlobally_def
by (auto simp add: setcompr_eq_image)

corollary ReleaseE_first [elim!]:
  assumes "(\<phi> R \<psi>) p"
  shows "\<psi> p"
using ReleaseE[OF assms, where n=0]
by auto

lemma WeakReleaseE [elim]:
  assumes "(\<phi> WR \<psi>) p"
      and "(BG n (- \<phi>)) p"
  shows "\<psi> (Suffix n p)"
using assms
unfolding WeakRelease_def BoundedGlobally_def
by (auto simp add: setcompr_eq_image)

corollary ReleaseE_contra [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "\<not> \<psi> (Suffix (Suc i) p)"
  shows "(BF i \<phi>) p"
using ReleaseE[OF assms(1), where n="Suc i"] assms(2)
unfolding not_BoundedFinally[THEN sym]
by auto

corollary WeakReleaseE_contra [elim]:
  assumes "(\<phi> WR \<psi>) p"
      and "\<not> \<psi> (Suffix i p)"
  shows "(BF i \<phi>) p"
using WeakReleaseE[OF assms(1), where n=i] assms(2)
unfolding not_BoundedFinally[THEN sym]
by auto

corollary ReleaseE_BoundedGloballyE [elim]:
  assumes "(BG n (- \<phi>)) p"
      and "(\<phi> R \<psi>) p"
      and "k \<le> Suc n"
  shows "\<psi> (Suffix k p)"
using assms(1, 3)
by (intro ReleaseE[OF assms(2)]) auto

corollary WeakReleaseE_BoundedGloballyE [elim]:
  assumes "(BG n (- \<phi>)) p"
      and "(\<phi> WR \<psi>) p"
      and "k \<le> n"
  shows "\<psi> (Suffix k p)"
using assms(1, 3)
by (intro WeakReleaseE[OF assms(2)]) auto

lemma ReleaseE_BoundedGloballyI_Suc [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "(BG n (- \<phi>)) p"
  shows "(BG (Suc n) \<psi>) p"
proof
  fix i
  assume "i \<le> Suc n"
  hence "\<forall>j<i. (- \<phi>) (Suffix j p)" 
    using assms(2)
    by (auto simp del: uminus_apply)
  thus "\<psi> (Suffix i p)"
    using `(\<phi> R \<psi>) p`
    unfolding Release_def
    by auto
qed

corollary ReleaseE_BoundedGloballyI [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "n \<noteq> 0 \<Longrightarrow> (BG (n - 1) (- \<phi>)) p"
  shows "(BG n \<psi>) p"
using assms ReleaseE_BoundedGloballyI_Suc[where n="n - 1"]
by (cases "n = 0") auto

lemma WeakReleaseE_BoundedGloballyI [elim]:
  assumes "(\<phi> WR \<psi>) p"
      and "(BG n (- \<phi>)) p"
  shows "(BG n \<psi>) p"
proof
  fix i
  assume "i \<le> n"
  hence "\<forall>j\<le>i. (- \<phi>) (Suffix j p)" 
    using assms(2)
    by (auto simp del: uminus_apply)
  thus "\<psi> (Suffix i p)"
    using `(\<phi> WR \<psi>) p`
    unfolding WeakRelease_def
    by auto
qed

lemma ReleaseInduct [intro?, case_names base ih]:
  assumes base: "\<psi> p"
      and ih: "\<And>i. (BG i (- \<phi>)) p \<Longrightarrow> 
                   \<psi> (Suffix i p) \<Longrightarrow>
                   \<psi> (Suffix (Suc i) p)"
  shows "(\<phi> R \<psi>) p"
proof (rule, cases rule: nat.induct)
  (* I don't get why the cases don't work *)
  print_cases
  show "\<psi> (Suffix 0 p) \<or> (\<exists>j<0. \<phi> (Suffix j p))"
    using base by auto
next
  fix n
  assume ih': "\<psi> (Suffix n p) \<or> (\<exists>j<n. \<phi> (Suffix j p))"
  show "\<psi> (Suffix (Suc n) p) \<or> (\<exists>j<Suc n. \<phi> (Suffix j p))"
    proof (rule disjCI)
      assume no_release: "\<not> (\<exists>j<Suc n. \<phi> (Suffix j p))"
      hence during: "(BG n (- \<phi>)) p" by auto
      have \<psi>: "\<psi> (Suffix n p)"
        using no_release ih' by force
      hence "\<psi> (Suffix (Suc n) p)"
        using during ih
        by auto
      thus "\<psi> (Suffix (Suc n) p)" by auto
    qed
qed

lemma WeakReleaseInduct [intro?, case_names base ih]:
  assumes base: "\<psi> p \<or> \<phi> p"
      and ih: "\<And>i. (BG (Suc i) (- \<phi>)) p \<Longrightarrow> 
                   \<psi> (Suffix i p) \<Longrightarrow>
                   \<psi> (Suffix (Suc i) p)"
  shows "(\<phi> WR \<psi>) p"
proof (rule, cases rule: nat.induct)
  (* I don't get why the cases don't work *)
  print_cases
  show "\<psi> (Suffix 0 p) \<or> (\<exists>j\<le>0. \<phi> (Suffix j p))"
    using base by auto
next
  fix n
  assume ih': "\<psi> (Suffix n p) \<or> (\<exists>j\<le>n. \<phi> (Suffix j p))"
  show "\<psi> (Suffix (Suc n) p) \<or> (\<exists>j\<le>Suc n. \<phi> (Suffix j p))"
    proof (rule disjCI)
      assume no_release: "\<not> (\<exists>j\<le>Suc n. \<phi> (Suffix j p))"
      hence during: "(BG (Suc n) (- \<phi>)) p" by auto
      have \<psi>: "\<psi> (Suffix n p)"
        using no_release ih' by force
      hence "\<psi> (Suffix (Suc n) p)"
        using during ih
        by auto
      thus "\<psi> (Suffix (Suc n) p)" by auto
    qed
qed

lemma ReleaseIE [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "\<And>i. (BF i \<phi>) p \<Longrightarrow> (BF i \<phi>') p"
      and "\<And>i. \<psi> (Suffix i p) \<Longrightarrow> \<psi>' (Suffix i p)"
  shows "(\<phi>' R \<psi>') p"
proof (intro ReleaseI)
  fix i
  show "\<psi>' (Suffix i p) \<or> (\<exists>j<i. \<phi>' (Suffix j p))"
    proof (cases "\<psi> (Suffix i p)")
      case True
      hence "\<psi>' (Suffix i p)" using assms by auto
      thus ?thesis by simp
    next
      case False
      hence "i \<noteq> 0"
        using ReleaseE_first[OF assms(1)] 
        by (cases "i = 0") simp
      hence "(BF (i - 1) \<phi>) p"
        using False
        by (intro ReleaseE_contra[OF assms(1)]) auto
      hence "(BF (i - 1) \<phi>') p"
        using assms by auto
      thus ?thesis
        using `i \<noteq> 0` by auto
    qed
qed

lemma WeakReleaseIE [elim]:
  assumes "(\<phi> WR \<psi>) p"
      and "\<And>i. (BF i \<phi>) p \<Longrightarrow> (BF i \<phi>') p"
      and "\<And>i. \<psi> (Suffix i p) \<Longrightarrow> \<psi>' (Suffix i p)"
  shows "(\<phi>' WR \<psi>') p"
proof (intro WeakReleaseI)
  fix i
  show "\<psi>' (Suffix i p) \<or> (\<exists>j\<le>i. \<phi>' (Suffix j p))"
    proof (cases "\<psi> (Suffix i p)")
      case True
      hence "\<psi>' (Suffix i p)" using assms by auto
      thus ?thesis by simp
    next
      case False
      hence "(BF i \<phi>) p"
        using False
        by (intro WeakReleaseE_contra[OF assms(1)]) auto
      hence "(BF i \<phi>') p"
        using assms by auto
      thus ?thesis by auto
    qed
qed

lemma WeakUntilImpliesUntil [elim!]:
  assumes "(\<phi> WU \<psi>) p"
  shows "(\<phi> U \<psi>) p"
using assms
unfolding Until_def WeakUntil_def
by auto

lemma ReleaseImpliesWeakRelease [elim!]:
  assumes "(\<phi> R \<psi>) p"
  shows "(\<phi> WR \<psi>) p"
using assms
unfolding Release_def WeakRelease_def
by auto
  
subsubsection \<open>Distributive lemmas\<close>

lemma not_Until:
  shows "- (\<phi> U \<psi>) = (- \<phi>) R (- \<psi>)"
unfolding Until_def Release_def
by auto

lemma not_WeakUntil:
  shows "- (\<phi> WU \<psi>) = (- \<phi>) WR (- \<psi>)"
unfolding WeakUntil_def WeakRelease_def
by auto

lemma not_Release:
  shows "- (\<phi> R \<psi>) = (- \<phi>) U (- \<psi>)"
unfolding Until_def Release_def
by (intro ext)auto

lemma not_WeakRelease:
  shows "- (\<phi> WR \<psi>) = (- \<phi>) WU (- \<psi>)"
unfolding WeakUntil_def WeakRelease_def
by (intro ext) auto

lemma Until_first_conj:
  shows "(\<phi> \<sqinter> \<psi>) U \<chi> = (\<phi> U \<chi>) \<sqinter> (\<psi> U \<chi>)"
proof (intro ext iffI)
  fix p
  assume "((\<phi> U \<chi>) \<sqinter> (\<psi> U \<chi>)) p" 
  then obtain i j where i: "\<chi> (Suffix i p)" "\<forall>k<i. \<phi> (Suffix k p)" and
                        j: "\<chi> (Suffix j p)" "\<forall>k<j. \<psi> (Suffix k p)"
    unfolding Until_def
    by auto
  define n where "n = min i j"
  have "\<chi> (Suffix n p)" "\<forall>k<n. \<phi> (Suffix k p) \<and> \<psi> (Suffix k p)"
    unfolding n_def min_def
    using i j 
    by auto
  thus "((\<phi> \<sqinter> \<psi>) U \<chi>) p"
    unfolding Until_def
    by auto
qed (auto simp: Until_def)

lemma Until_second_disj:
  shows "\<phi> U (\<psi> \<squnion> \<chi>) = (\<phi> U \<psi>) \<squnion> (\<phi> U \<chi>)"
unfolding Until_def
by auto

lemma WeakUntil_first_conj:
  shows "(\<phi> \<sqinter> \<psi>) WU \<chi> = (\<phi> WU \<chi>) \<sqinter> (\<psi> WU \<chi>)"
proof (intro ext iffI)
  fix p
  assume "((\<phi> WU \<chi>) \<sqinter> (\<psi> WU \<chi>)) p" 
  then obtain i j where i: "\<chi> (Suffix i p)" "\<forall>k\<le>i. \<phi> (Suffix k p)" and
                        j: "\<chi> (Suffix j p)" "\<forall>k\<le>j. \<psi> (Suffix k p)"
    unfolding WeakUntil_def
    by auto
  define n where "n = min i j"
  have "\<chi> (Suffix n p)" "\<forall>k\<le>n. \<phi> (Suffix k p) \<and> \<psi> (Suffix k p)"
    unfolding n_def min_def
    using i j 
    by auto
  thus "((\<phi> \<sqinter> \<psi>) WU \<chi>) p"
    unfolding WeakUntil_def
    by auto
qed (auto simp: WeakUntil_def)

lemma WeakUntil_second_disj:
  shows "\<phi> WU (\<psi> \<squnion> \<chi>) = (\<phi> WU \<psi>) \<squnion> (\<phi> WU \<chi>)"
unfolding WeakUntil_def
by auto

lemma Release_first_disj:
  shows "(\<phi> \<squnion> \<psi>) R \<chi> = (\<phi> R \<chi>) \<squnion> (\<psi> R \<chi>)"
using Until_first_conj[where \<phi>="-\<phi>" and \<psi>="-\<psi>" and \<chi>="-\<chi>", 
                       THEN arg_cong[where f="\<lambda>x. - x"]]
by (simp add: not_Until)

lemma Release_second_conj:
  shows "\<phi> R (\<psi> \<sqinter> \<chi>) = (\<phi> R \<psi>) \<sqinter> (\<phi> R \<chi>)"
unfolding Release_def
by auto

lemma WeakRelease_first_disj:
  shows "(\<phi> \<squnion> \<psi>) WR \<chi> = (\<phi> WR \<chi>) \<squnion> (\<psi> WR \<chi>)"
using WeakUntil_first_conj[where \<phi>="-\<phi>" and \<psi>="-\<psi>" and \<chi>="-\<chi>", 
                          THEN arg_cong[where f="\<lambda>x. - x"]]
by (simp add: not_WeakUntil)

lemma WeakRelease_second_conj:
  shows "\<phi> WR (\<psi> \<sqinter> \<chi>) = (\<phi> WR \<psi>) \<sqinter> (\<phi> WR \<chi>)"
unfolding WeakRelease_def
by auto

subsubsection \<open>Elims of distributive lemmas\<close>

lemma Until_first_conjE1 [elim]:
  assumes "(\<phi> U \<chi>) p"
      and "(\<psi> U \<chi>) p"
  shows "((\<phi> \<sqinter> \<psi>) U \<chi>) p"
using assms
unfolding Until_first_conj
by auto

lemma Until_first_conjE2 [elim]:
  assumes "(\<psi> U \<chi>) p"
      and "(\<phi> U \<chi>) p"
  shows "((\<phi> \<sqinter> \<psi>) U \<chi>) p"
using assms Until_first_conjE1
by metis

lemma WeakUntil_first_conjE1 [elim]:
  assumes "(\<phi> WU \<chi>) p"
      and "(\<psi> WU \<chi>) p"
  shows "((\<phi> \<sqinter> \<psi>) WU \<chi>) p"
using assms
unfolding WeakUntil_first_conj
by auto

lemma WeakUntil_first_conjE2 [elim]:
  assumes "(\<psi> WU \<chi>) p"
      and "(\<phi> WU \<chi>) p"
  shows "((\<phi> \<sqinter> \<psi>) WU \<chi>) p"
using assms WeakUntil_first_conjE1
by metis

lemma Release_second_conjE1 [elim]:
  assumes "(\<phi> R \<psi>) p"
      and "(\<phi> R \<chi>) p"
  shows "(\<phi> R (\<psi> \<sqinter> \<chi>)) p"
using assms
unfolding Release_second_conj
by auto

lemma Release_second_conjE2 [elim]:
  assumes "(\<phi> R \<chi>) p"
      and "(\<phi> R \<psi>) p"
  shows "(\<phi> R (\<psi> \<sqinter> \<chi>)) p"
using assms Release_second_conjE1
by metis

lemma WeakRelease_second_conjE1 [elim]:
  assumes "(\<phi> WR \<psi>) p"
      and "(\<phi> WR \<chi>) p"
  shows "(\<phi> WR (\<psi> \<sqinter> \<chi>)) p"
using assms
unfolding WeakRelease_second_conj
by auto

lemma WeakRelease_second_conjE2 [elim]:
  assumes "(\<phi> WR \<chi>) p"
      and "(\<phi> WR \<psi>) p"
  shows "(\<phi> WR (\<psi> \<sqinter> \<chi>)) p"
using assms WeakRelease_second_conjE1
by metis

end
