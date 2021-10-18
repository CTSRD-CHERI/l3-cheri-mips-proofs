(*<*) 

(* Author: Kyndylan Nienhuis *)

theory CompartmentAuthority

imports 
  "CHERI-core.CheriLemmas"
begin

(*>*)
section \<open>Generalised permissions\<close>

record CompartmentAuthority = 
  SystemRegisterAccess :: bool
  ExecutableAddresses :: "VirtualAddress set"
  LoadableAddresses :: "VirtualAddress set"
  CapLoadableAddresses :: "VirtualAddress set"
  StorableAddresses :: "VirtualAddress set"
  CapStorableAddresses :: "VirtualAddress set"
  LocalCapStorableAddresses :: "VirtualAddress set"
  SealableTypes :: "ObjectType set"
  UnsealableTypes :: "ObjectType set"

subsection \<open>Order over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (order) order
begin

  definition less_eq_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme \<Rightarrow> bool"
  where 
    "less_eq_CompartmentAuthority_ext perm\<^sub>1 perm\<^sub>2 \<equiv>
     (SystemRegisterAccess perm\<^sub>1 \<le> SystemRegisterAccess perm\<^sub>2) \<and>
     (ExecutableAddresses perm\<^sub>1 \<le> ExecutableAddresses perm\<^sub>2) \<and>
     (LoadableAddresses perm\<^sub>1 \<le> LoadableAddresses perm\<^sub>2) \<and>
     (CapLoadableAddresses perm\<^sub>1 \<le> CapLoadableAddresses perm\<^sub>2) \<and>
     (StorableAddresses perm\<^sub>1 \<le> StorableAddresses perm\<^sub>2) \<and>
     (CapStorableAddresses perm\<^sub>1 \<le> CapStorableAddresses perm\<^sub>2) \<and>
     (LocalCapStorableAddresses perm\<^sub>1 \<le> LocalCapStorableAddresses perm\<^sub>2) \<and>
     (SealableTypes perm\<^sub>1 \<le> SealableTypes perm\<^sub>2) \<and>
     (UnsealableTypes perm\<^sub>1 \<le> UnsealableTypes perm\<^sub>2) \<and>
     (CompartmentAuthority.more perm\<^sub>1 \<le> CompartmentAuthority.more perm\<^sub>2)"
  
  definition less_CompartmentAuthority_ext :: "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme \<Rightarrow> bool" where
    "less_CompartmentAuthority_ext perm\<^sub>1 perm\<^sub>2 \<equiv> perm\<^sub>1 \<le> perm\<^sub>2 \<and> \<not> (perm\<^sub>2 \<le> perm\<^sub>1)"
  
  instance
    by standard (auto simp: less_CompartmentAuthority_ext_def less_eq_CompartmentAuthority_ext_def)

end

subsubsection \<open>Eliminations\<close>

lemma SystemRegisterAccess_le [elim]:
  assumes "p \<le> q"
      and "SystemRegisterAccess p"
  shows "SystemRegisterAccess q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemma ExecutableAddresses_le:
  assumes "p \<le> q"
  shows "ExecutableAddresses p \<subseteq> ExecutableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas ExecutableAddresses_le_subsetD [elim] =
  subsetD[OF ExecutableAddresses_le]

lemma LoadableAddresses_le:
  assumes "p \<le> q"
  shows "LoadableAddresses p \<subseteq> LoadableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas LoadableAddresses_le_subsetD [elim] =
  subsetD[OF LoadableAddresses_le]

lemma CapLoadableAddresses_le:
  assumes "p \<le> q"
  shows "CapLoadableAddresses p \<subseteq> CapLoadableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas CapLoadableAddresses_le_subsetD [elim] =
  subsetD[OF CapLoadableAddresses_le]

lemma StorableAddresses_le:
  assumes "p \<le> q"
  shows "StorableAddresses p \<subseteq> StorableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas StorableAddresses_le_subsetD [elim] =
  subsetD[OF StorableAddresses_le]

lemma CapStorableAddresses_le:
  assumes "p \<le> q"
  shows "CapStorableAddresses p \<subseteq> CapStorableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas CapStorableAddresses_le_subsetD [elim] =
  subsetD[OF CapStorableAddresses_le]

lemma LocalCapStorableAddresses_le:
  assumes "p \<le> q"
  shows "LocalCapStorableAddresses p \<subseteq> LocalCapStorableAddresses q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas LocalCapStorableAddresses_le_subsetD [elim] =
  subsetD[OF LocalCapStorableAddresses_le]

lemma SealableTypes_le:
  assumes "p \<le> q"
  shows "SealableTypes p \<subseteq> SealableTypes q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas SealableTypes_le_subsetD [elim] =
  subsetD[OF SealableTypes_le]

lemma UnsealableTypes_le:
  assumes "p \<le> q"
  shows "UnsealableTypes p \<subseteq> UnsealableTypes q"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
by auto

lemmas UnsealableTypes_le_subsetD [elim] =
  subsetD[OF UnsealableTypes_le]

subsection \<open>Complete lattice over generalised permissions\<close>

subsubsection \<open>Bottom of generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (order_bot) order_bot
begin

  definition bot_CompartmentAuthority_ext :: "'a CompartmentAuthority_scheme" where
    "bot_CompartmentAuthority_ext = 
     \<lparr>SystemRegisterAccess = bot,
      ExecutableAddresses = bot,
      LoadableAddresses = bot,
      CapLoadableAddresses = bot,
      StorableAddresses = bot,
      CapStorableAddresses = bot,
      LocalCapStorableAddresses = bot,
      SealableTypes = bot,
      UnsealableTypes = bot, 
      \<dots> = bot\<rparr>"
  
  instance
    by standard (auto simp: bot_CompartmentAuthority_ext_def less_eq_CompartmentAuthority_ext_def)

end

lemma bot_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess bot = bot"
    and "ExecutableAddresses bot = bot"
    and "LoadableAddresses bot = bot"
    and "CapLoadableAddresses bot = bot"
    and "StorableAddresses bot = bot"
    and "CapStorableAddresses bot = bot"
    and "LocalCapStorableAddresses bot = bot"
    and "SealableTypes bot = bot"
    and "UnsealableTypes bot = bot"
    and "more bot = bot"
unfolding bot_CompartmentAuthority_ext_def
by simp_all

subsubsection \<open>Top of generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (order_top) order_top
begin

  definition top_CompartmentAuthority_ext :: "'a CompartmentAuthority_scheme" where
    "top_CompartmentAuthority_ext = 
     \<lparr>SystemRegisterAccess = top,
      ExecutableAddresses = top,
      LoadableAddresses = top,
      CapLoadableAddresses = top,
      StorableAddresses = top,
      CapStorableAddresses = top,
      LocalCapStorableAddresses = top,
      SealableTypes = top,
      UnsealableTypes = top, 
      \<dots> = top\<rparr>"
  
  instance
    by standard (auto simp: top_CompartmentAuthority_ext_def less_eq_CompartmentAuthority_ext_def)

end

lemma top_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess top = top"
    and "ExecutableAddresses top = top"
    and "LoadableAddresses top = top"
    and "CapLoadableAddresses top = top"
    and "StorableAddresses top = top"
    and "CapStorableAddresses top = top"
    and "LocalCapStorableAddresses top = top"
    and "SealableTypes top = top"
    and "UnsealableTypes top = top"
    and "more top = top"
unfolding top_CompartmentAuthority_ext_def
by simp_all

subsubsection \<open>Infimum of generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (semilattice_inf) semilattice_inf
begin

  definition inf_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "inf_CompartmentAuthority_ext left right = 
     \<lparr>SystemRegisterAccess = inf (SystemRegisterAccess left) (SystemRegisterAccess right),
      ExecutableAddresses = inf (ExecutableAddresses left) (ExecutableAddresses right),
      LoadableAddresses = inf (LoadableAddresses left) (LoadableAddresses right),
      CapLoadableAddresses = inf (CapLoadableAddresses left) (CapLoadableAddresses right),
      StorableAddresses = inf (StorableAddresses left) (StorableAddresses right),
      CapStorableAddresses = inf (CapStorableAddresses left) (CapStorableAddresses right),
      LocalCapStorableAddresses = inf (LocalCapStorableAddresses left) (LocalCapStorableAddresses right),
      SealableTypes = inf (SealableTypes left) (SealableTypes right),
      UnsealableTypes = inf (UnsealableTypes left) (UnsealableTypes right), 
      \<dots> = inf (more left) (more right)\<rparr>"
  
  instance
    by standard (auto simp: inf_CompartmentAuthority_ext_def less_eq_CompartmentAuthority_ext_def)

end

lemma inf_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (inf left right) = inf (SystemRegisterAccess left) (SystemRegisterAccess right)"
    and "ExecutableAddresses (inf left right) = inf (ExecutableAddresses left) (ExecutableAddresses right)"
    and "LoadableAddresses (inf left right) = inf (LoadableAddresses left) (LoadableAddresses right)"
    and "CapLoadableAddresses (inf left right) = inf (CapLoadableAddresses left) (CapLoadableAddresses right)"
    and "StorableAddresses (inf left right) = inf (StorableAddresses left) (StorableAddresses right)"
    and "CapStorableAddresses (inf left right) = inf (CapStorableAddresses left) (CapStorableAddresses right)"
    and "LocalCapStorableAddresses (inf left right) = inf (LocalCapStorableAddresses left) (LocalCapStorableAddresses right)"
    and "SealableTypes (inf left right) = inf (SealableTypes left) (SealableTypes right)"
    and "UnsealableTypes (inf left right) = inf (UnsealableTypes left) (UnsealableTypes right)"
    and "more (inf left right) = inf (more left) (more right)"
unfolding inf_CompartmentAuthority_ext_def
by simp_all

instantiation "CompartmentAuthority_ext" :: (Inf) Inf
begin

  definition Inf_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme set \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "Inf_CompartmentAuthority_ext permSet = 
     \<lparr>SystemRegisterAccess = Inf (SystemRegisterAccess ` permSet),
      ExecutableAddresses = Inf (ExecutableAddresses ` permSet),
      LoadableAddresses = Inf (LoadableAddresses ` permSet),
      CapLoadableAddresses = Inf (CapLoadableAddresses ` permSet),
      StorableAddresses = Inf (StorableAddresses ` permSet),
      CapStorableAddresses = Inf (CapStorableAddresses ` permSet),
      LocalCapStorableAddresses = Inf (LocalCapStorableAddresses ` permSet),
      SealableTypes = Inf (SealableTypes ` permSet),
      UnsealableTypes = Inf (UnsealableTypes ` permSet), 
      \<dots> = Inf (more ` permSet)\<rparr>"
  
  instance by standard

end

lemma Inf_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (Inf permSet) = Inf (SystemRegisterAccess ` permSet)"
    and "ExecutableAddresses (Inf permSet) = Inf (ExecutableAddresses ` permSet)"
    and "LoadableAddresses (Inf permSet) = Inf (LoadableAddresses ` permSet)"
    and "CapLoadableAddresses (Inf permSet) = Inf (CapLoadableAddresses ` permSet)"
    and "StorableAddresses (Inf permSet) = Inf (StorableAddresses ` permSet)"
    and "CapStorableAddresses (Inf permSet) = Inf (CapStorableAddresses ` permSet)"
    and "LocalCapStorableAddresses (Inf permSet) = Inf (LocalCapStorableAddresses ` permSet)"
    and "SealableTypes (Inf permSet) = Inf (SealableTypes ` permSet)"
    and "UnsealableTypes (Inf permSet) = Inf (UnsealableTypes ` permSet)"
    and "more (Inf permSet) = Inf (more ` permSet)"
unfolding Inf_CompartmentAuthority_ext_def
by simp_all

subsubsection \<open>Supremum of generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (semilattice_sup) semilattice_sup
begin

  definition sup_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "sup_CompartmentAuthority_ext left right = 
     \<lparr>SystemRegisterAccess = sup (SystemRegisterAccess left) (SystemRegisterAccess right),
      ExecutableAddresses = sup (ExecutableAddresses left) (ExecutableAddresses right),
      LoadableAddresses = sup (LoadableAddresses left) (LoadableAddresses right),
      CapLoadableAddresses = sup (CapLoadableAddresses left) (CapLoadableAddresses right),
      StorableAddresses = sup (StorableAddresses left) (StorableAddresses right),
      CapStorableAddresses = sup (CapStorableAddresses left) (CapStorableAddresses right),
      LocalCapStorableAddresses = sup (LocalCapStorableAddresses left) (LocalCapStorableAddresses right),
      SealableTypes = sup (SealableTypes left) (SealableTypes right),
      UnsealableTypes = sup (UnsealableTypes left) (UnsealableTypes right), 
      \<dots> = sup (more left) (more right)\<rparr>"
  
  instance
    by standard (auto simp: sup_CompartmentAuthority_ext_def less_eq_CompartmentAuthority_ext_def)

end

lemma sup_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (sup left right) = sup (SystemRegisterAccess left) (SystemRegisterAccess right)"
    and "ExecutableAddresses (sup left right) = sup (ExecutableAddresses left) (ExecutableAddresses right)"
    and "LoadableAddresses (sup left right) = sup (LoadableAddresses left) (LoadableAddresses right)"
    and "CapLoadableAddresses (sup left right) = sup (CapLoadableAddresses left) (CapLoadableAddresses right)"
    and "StorableAddresses (sup left right) = sup (StorableAddresses left) (StorableAddresses right)"
    and "CapStorableAddresses (sup left right) = sup (CapStorableAddresses left) (CapStorableAddresses right)"
    and "LocalCapStorableAddresses (sup left right) = sup (LocalCapStorableAddresses left) (LocalCapStorableAddresses right)"
    and "SealableTypes (sup left right) = sup (SealableTypes left) (SealableTypes right)"
    and "UnsealableTypes (sup left right) = sup (UnsealableTypes left) (UnsealableTypes right)"
    and "more (sup left right) = sup (more left) (more right)"
unfolding sup_CompartmentAuthority_ext_def
by simp_all

instantiation "CompartmentAuthority_ext" :: (Sup) Sup
begin

  definition Sup_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme set \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "Sup_CompartmentAuthority_ext permSet = 
     \<lparr>SystemRegisterAccess = Sup (SystemRegisterAccess ` permSet),
      ExecutableAddresses = Sup (ExecutableAddresses ` permSet),
      LoadableAddresses = Sup (LoadableAddresses ` permSet),
      CapLoadableAddresses = Sup (CapLoadableAddresses ` permSet),
      StorableAddresses = Sup (StorableAddresses ` permSet),
      CapStorableAddresses = Sup (CapStorableAddresses ` permSet),
      LocalCapStorableAddresses = Sup (LocalCapStorableAddresses ` permSet),
      SealableTypes = Sup (SealableTypes ` permSet),
      UnsealableTypes = Sup (UnsealableTypes ` permSet), 
      \<dots> = Sup (more ` permSet)\<rparr>"
  
  instance by standard

end

lemma Sup_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (Sup permSet) = Sup (SystemRegisterAccess ` permSet)"
    and "ExecutableAddresses (Sup permSet) = Sup (ExecutableAddresses ` permSet)"
    and "LoadableAddresses (Sup permSet) = Sup (LoadableAddresses ` permSet)"
    and "CapLoadableAddresses (Sup permSet) = Sup (CapLoadableAddresses ` permSet)"
    and "StorableAddresses (Sup permSet) = Sup (StorableAddresses ` permSet)"
    and "CapStorableAddresses (Sup permSet) = Sup (CapStorableAddresses ` permSet)"
    and "LocalCapStorableAddresses (Sup permSet) = Sup (LocalCapStorableAddresses ` permSet)"
    and "SealableTypes (Sup permSet) = Sup (SealableTypes ` permSet)"
    and "UnsealableTypes (Sup permSet) = Sup (UnsealableTypes ` permSet)"
    and "more (Sup permSet) = Sup (more ` permSet)"
unfolding Sup_CompartmentAuthority_ext_def
by simp_all

subsubsection \<open>Bounded, distributive lattice over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (Lattices.lattice) Lattices.lattice
begin  

  instance by standard

end

instantiation "CompartmentAuthority_ext" :: (bounded_lattice) bounded_lattice
begin  

  instance by standard

end

instantiation "CompartmentAuthority_ext" :: (distrib_lattice) distrib_lattice
begin
  
  instance
    by standard
       (auto simp: sup_inf_distrib1 
                   inf_CompartmentAuthority_ext_def
                   sup_CompartmentAuthority_ext_def)

end

subsubsection \<open>Boolean algebra over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (boolean_algebra) boolean_algebra
begin

  definition minus_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "minus_CompartmentAuthority_ext left right = 
     \<lparr>SystemRegisterAccess = minus (SystemRegisterAccess left) (SystemRegisterAccess right),
      ExecutableAddresses = minus (ExecutableAddresses left) (ExecutableAddresses right),
      LoadableAddresses = minus (LoadableAddresses left) (LoadableAddresses right),
      CapLoadableAddresses = minus (CapLoadableAddresses left) (CapLoadableAddresses right),
      StorableAddresses = minus (StorableAddresses left) (StorableAddresses right),
      CapStorableAddresses = minus (CapStorableAddresses left) (CapStorableAddresses right),
      LocalCapStorableAddresses = minus (LocalCapStorableAddresses left) (LocalCapStorableAddresses right),
      SealableTypes = minus (SealableTypes left) (SealableTypes right),
      UnsealableTypes = minus (UnsealableTypes left) (UnsealableTypes right), 
      \<dots> = minus (more left) (more right)\<rparr>"

  definition uminus_CompartmentAuthority_ext :: 
    "'a CompartmentAuthority_scheme \<Rightarrow> 'a CompartmentAuthority_scheme"
  where
    "uminus_CompartmentAuthority_ext perm = 
     \<lparr>SystemRegisterAccess = uminus (SystemRegisterAccess perm),
      ExecutableAddresses = uminus (ExecutableAddresses perm),
      LoadableAddresses = uminus (LoadableAddresses perm),
      CapLoadableAddresses = uminus (CapLoadableAddresses perm),
      StorableAddresses = uminus (StorableAddresses perm),
      CapStorableAddresses = uminus (CapStorableAddresses perm),
      LocalCapStorableAddresses = uminus (LocalCapStorableAddresses perm),
      SealableTypes = uminus (SealableTypes perm),
      UnsealableTypes = uminus (UnsealableTypes perm), 
      \<dots> = uminus (more perm)\<rparr>"
  
  instance
    by standard
       (auto simp: diff_eq
                   bot_CompartmentAuthority_ext_def
                   top_CompartmentAuthority_ext_def
                   inf_CompartmentAuthority_ext_def 
                   sup_CompartmentAuthority_ext_def
                   minus_CompartmentAuthority_ext_def
                   uminus_CompartmentAuthority_ext_def)

end

lemma minus_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (minus left right) = minus (SystemRegisterAccess left) (SystemRegisterAccess right)"
    and "ExecutableAddresses (minus left right) = minus (ExecutableAddresses left) (ExecutableAddresses right)"
    and "LoadableAddresses (minus left right) = minus (LoadableAddresses left) (LoadableAddresses right)"
    and "CapLoadableAddresses (minus left right) = minus (CapLoadableAddresses left) (CapLoadableAddresses right)"
    and "StorableAddresses (minus left right) = minus (StorableAddresses left) (StorableAddresses right)"
    and "CapStorableAddresses (minus left right) = minus (CapStorableAddresses left) (CapStorableAddresses right)"
    and "LocalCapStorableAddresses (minus left right) = minus (LocalCapStorableAddresses left) (LocalCapStorableAddresses right)"
    and "SealableTypes (minus left right) = minus (SealableTypes left) (SealableTypes right)"
    and "UnsealableTypes (minus left right) = minus (UnsealableTypes left) (UnsealableTypes right)"
    and "more (minus left right) = minus (more left) (more right)"
unfolding minus_CompartmentAuthority_ext_def
by simp_all

lemma uminus_CompartmentAuthority_ext_simp [simp]:
  shows "SystemRegisterAccess (uminus perm) = uminus (SystemRegisterAccess perm)"
    and "ExecutableAddresses (uminus perm) = uminus (ExecutableAddresses perm)"
    and "LoadableAddresses (uminus perm) = uminus (LoadableAddresses perm)"
    and "CapLoadableAddresses (uminus perm) = uminus (CapLoadableAddresses perm)"
    and "StorableAddresses (uminus perm) = uminus (StorableAddresses perm)"
    and "CapStorableAddresses (uminus perm) = uminus (CapStorableAddresses perm)"
    and "LocalCapStorableAddresses (uminus perm) = uminus (LocalCapStorableAddresses perm)"
    and "SealableTypes (uminus perm) = uminus (SealableTypes perm)"
    and "UnsealableTypes (uminus perm) = uminus (UnsealableTypes perm)"
    and "more (uminus perm) = uminus (more perm)"
unfolding uminus_CompartmentAuthority_ext_def
by simp_all

subsubsection \<open>Complete lattice over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (complete_lattice) complete_lattice
begin
  
  instance
    proof standard
      fix x :: "'a CompartmentAuthority_ext" and A 
      assume "x \<in> A"
      thus   "less_eq (Inf A) x"
        unfolding Inf_CompartmentAuthority_ext_def
        unfolding less_eq_CompartmentAuthority_ext_def
        by (simp add: INF_lower)
    next
      fix z :: "'a CompartmentAuthority_ext" and A 
      assume "\<And>x. x \<in> A \<Longrightarrow> less_eq z x"
      thus   "less_eq z (Inf A)"
        unfolding Inf_CompartmentAuthority_ext_def
        unfolding less_eq_CompartmentAuthority_ext_def
        by (auto simp: INF_greatest)
    next
      fix x :: "'a CompartmentAuthority_ext" and A 
      assume "x \<in> A"
      thus   "less_eq x (Sup A)"
        unfolding Sup_CompartmentAuthority_ext_def
        unfolding less_eq_CompartmentAuthority_ext_def
        by (auto simp: SUP_upper)
    next
      fix z :: "'a CompartmentAuthority_ext" and A 
      assume "\<And>x. x \<in> A \<Longrightarrow> less_eq x z"
      thus   "less_eq (Sup A) z"
        unfolding Sup_CompartmentAuthority_ext_def
        unfolding less_eq_CompartmentAuthority_ext_def
        by (auto simp: SUP_least)
    next
      show "(Inf {}::'a CompartmentAuthority_ext) = top"
        unfolding Inf_CompartmentAuthority_ext_def
        unfolding top_CompartmentAuthority_ext_def
        by simp
    next
      show "(Sup {}::'a CompartmentAuthority_ext) = bot"
        unfolding Sup_CompartmentAuthority_ext_def
        unfolding bot_CompartmentAuthority_ext_def
        by simp
    qed

end

subsubsection \<open>Complete distributive lattice over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (complete_distrib_lattice) complete_distrib_lattice
begin
  
  instance
    proof standard
      fix x :: "'a CompartmentAuthority_ext" and A 
      show "sup x (Inf A) = (INF a:A. sup x a)"
        unfolding Inf_CompartmentAuthority_ext_def
        unfolding sup_CompartmentAuthority_ext_def
        using sup_Inf[where a="CompartmentAuthority.more x"]
        by simp
    next
      fix x :: "'a CompartmentAuthority_ext" and A 
      show "inf x (Sup A) = (SUP a:A. inf x a)"
        unfolding Sup_CompartmentAuthority_ext_def
        unfolding inf_CompartmentAuthority_ext_def
        using inf_Sup[where a="CompartmentAuthority.more x"]
        by simp
    qed

end

subsubsection \<open>Complete boolean algebra over generalised permissions\<close>

instantiation "CompartmentAuthority_ext" :: (complete_boolean_algebra) complete_boolean_algebra
begin
  
  instance by standard

end

subsection \<open>Physical capability addresses\<close>

definition getTranslateCapAddresses :: 
  "VirtualAddress set \<Rightarrow> AccessType \<Rightarrow> state \<Rightarrow> PhysicalCapAddress set" 
where
  "getTranslateCapAddresses addrs t s \<equiv> 
   GetCapAddress ` getTranslateAddresses addrs t s"

lemma Commute_getTranslateCapAddresses [Commute_compositeI]: 
  assumes "Commute (read_state (getTranslateAddresses addrs t)) m"
  shows "Commute (read_state (getTranslateCapAddresses addrs t)) m"
using assms
unfolding getTranslateCapAddresses_def Commute_def
by auto

lemma getTranslateCapAddressesI [intro?]:
  assumes "getTranslateAddr (virtualAddress, t) s = Some physicalAddress"
      and "a = GetCapAddress physicalAddress"
      and "virtualAddress \<in> addrs"
  shows "a \<in> getTranslateCapAddresses addrs t s"
using assms
unfolding getTranslateCapAddresses_def
unfolding getTranslateAddresses_def
by auto

lemma getTranslateCapAddressesI_word_cat [elim]:
  assumes "getTranslateAddr (virtualAddress, t) s = Some (ExtendCapAddress a)"
      and "virtualAddress \<in> addrs"
  shows "a \<in> getTranslateCapAddresses addrs t s"
using assms
using slice_cat1[where a=a and b="0::5 word" and 'a=40]
by (intro getTranslateCapAddressesI) (auto simp: word_size)

lemma getTranslateCapAddressesE [elim]:
  assumes "a \<in> getTranslateCapAddresses addrs t s"
  obtains virtualAddress physicalAddress
    where "getTranslateAddr (virtualAddress, t) s = Some physicalAddress"
      and "virtualAddress \<in> addrs" 
      and "a = GetCapAddress physicalAddress"
using assms
unfolding getTranslateCapAddresses_def
by auto

lemma getTranslateCapAddresses_le:
  assumes "addrs \<subseteq> addrs'"
  shows "getTranslateCapAddresses addrs t s \<subseteq> getTranslateCapAddresses addrs' t s"
using assms
unfolding getTranslateCapAddresses_def
by auto

lemmas getTranslateCapAddresses_le_subsetD [elim] =
  subsetD[OF getTranslateCapAddresses_le]

lemma getTranslateCapAddresses_eqI_getTranslateAddr:
  assumes "\<And>a. getTranslateAddr a s' = getTranslateAddr a s"
  shows "getTranslateCapAddresses addrs t s' = getTranslateCapAddresses addrs t s"
using getTranslateAddresses_eqI_getTranslateAddr[OF assms]
unfolding getTranslateCapAddresses_def
by simp

lemma getTranslateCapAddresses_distrib_union:
  shows "getTranslateCapAddresses (addrs \<union> addrs') t s =
         (getTranslateCapAddresses addrs t s \<union> getTranslateCapAddresses addrs' t s)"
unfolding getTranslateCapAddresses_def
unfolding getTranslateAddresses_distrib_union
by auto

lemma getTranslateCapAddresses_distrib_Union:
  shows "getTranslateCapAddresses (\<Union>addrsSet) t s =
         (\<Union>addrs\<in>addrsSet. getTranslateCapAddresses addrs t s)"
unfolding getTranslateCapAddresses_def
unfolding getTranslateAddresses_distrib_Union
by auto

subsection \<open>Data writable addresses\<close>

definition StorablePhysAddresses where
  "StorablePhysAddresses gperm s \<equiv>
   getTranslateAddresses (StorableAddresses gperm) STORE s"

lemma StorablePhysAddresses_le:
  assumes "p \<le> q"
  shows "StorablePhysAddresses p s \<subseteq> StorablePhysAddresses q s"
using getTranslateAddresses_le[OF StorableAddresses_le[OF assms]]
unfolding StorablePhysAddresses_def
by auto

subsection \<open>Capability writable addresses\<close>

definition StorablePhysCapAddresses where
  "StorablePhysCapAddresses gperm s \<equiv>
   getTranslateCapAddresses (StorableAddresses gperm) STORE s"

lemma StorablePhysCapAddresses_le:
  assumes "p \<le> q"
  shows "StorablePhysCapAddresses p s \<subseteq> StorablePhysCapAddresses q s"
using StorableAddresses_le[OF assms]
using getTranslateCapAddresses_le
unfolding StorablePhysCapAddresses_def
by auto

subsection \<open>Always accessible registers\<close>

definition RegisterIsAlwaysAccessible :: "CapRegister \<Rightarrow> bool" where
  "RegisterIsAlwaysAccessible r \<equiv> 
   case r of RegSpecial cd \<Rightarrow> cd = 0 \<or> cd = 1
           | _ \<Rightarrow> True"

lemma RegisterIsAlwaysAccessible_simps [simp]:
  shows "RegisterIsAlwaysAccessible RegPCC"
    and "RegisterIsAlwaysAccessible RegBranchDelayPCC"
    and "RegisterIsAlwaysAccessible RegBranchToPCC"
    and "RegisterIsAlwaysAccessible (RegGeneral cd)"
    and "RegisterIsAlwaysAccessible (RegSpecial 0)"
    and "RegisterIsAlwaysAccessible (RegSpecial 1)"
unfolding RegisterIsAlwaysAccessible_def
by simp_all

subsection \<open>Readable locations\<close>

definition ReadableLocations :: "CompartmentAuthority \<Rightarrow> state \<Rightarrow> CapLocation set" where
  "ReadableLocations f s \<equiv> 
   {loc. case loc of 
      LocReg r \<Rightarrow> RegisterIsAlwaysAccessible r
    | LocMem addr \<Rightarrow> addr \<in> getTranslateCapAddresses (CapLoadableAddresses f) LOAD s}"

lemma Commute_ReadableLocations [Commute_compositeI]: 
  assumes "\<And>addrs. Commute (read_state (getTranslateCapAddresses addrs LOAD)) m"
  shows "Commute (read_state (ReadableLocations perm)) m"
using assms
unfolding ReadableLocations_def Commute_def
by auto

lemma ReadableLocations_simps [simp]:
  shows "(LocReg r) \<in> ReadableLocations f s = 
         (RegisterIsAlwaysAccessible r)"
    and "(LocMem addr) \<in> ReadableLocations f s = 
         (addr \<in> getTranslateCapAddresses (CapLoadableAddresses f) LOAD s)"
unfolding ReadableLocations_def
by simp_all

lemma ReadableLocations_le_subsetD [elim]:
  assumes "p \<le> q"
      and "loc \<in> ReadableLocations p s"
  shows "loc \<in> ReadableLocations q s"
proof (cases loc)
  case LocReg
  thus?thesis 
    using assms by auto
next
  case (LocMem a)
  have "CapLoadableAddresses p \<subseteq> CapLoadableAddresses q"
    using assms by auto
  from getTranslateCapAddresses_le[OF this]
  show ?thesis
    using LocMem assms(2)
    by auto
qed

lemma ReadableLocations_le:
  assumes "p \<le> q"
  shows "ReadableLocations p s \<subseteq> ReadableLocations q s"
using ReadableLocations_le_subsetD[OF assms]
by auto

subsection \<open>Readable capabilities\<close>

definition ReadableCaps where
  "ReadableCaps perm s \<equiv>
   {getCap loc s 
    |loc. loc \<in> ReadableLocations perm s \<and> getTag (getCap loc s)}"

lemma ReadableCapsI [intro?]:
  assumes "cap = getCap loc s"
      and "loc \<in> ReadableLocations perm s"
      and "getTag cap"
  shows "cap \<in> ReadableCaps perm s"
using assms
unfolding ReadableCaps_def
by auto

lemma ReadableCapsI_loc [elim!]:
  assumes "loc \<in> ReadableLocations perm s"
      and "getTag (getCap loc s)"
  shows "getCap loc s \<in> ReadableCaps perm s"
using assms
unfolding ReadableCaps_def
by auto

lemma ReadableCapsE_tag [elim!]:
  assumes "cap \<in> ReadableCaps perm s"
  shows "getTag cap"
using assms
unfolding ReadableCaps_def
by auto

lemma ReadableCapsE_loc [elim]:
  assumes "cap \<in> ReadableCaps perm s"
  obtains loc where "cap = getCap loc s"
                    "loc \<in> ReadableLocations perm s"
using assms
unfolding ReadableCaps_def
by auto

lemma ReadableCaps_le_subsetD [elim]:
  assumes "p \<le> q"
      and "cap \<in> ReadableCaps p s"
  shows "cap \<in> ReadableCaps q s"
using assms
unfolding ReadableCaps_def
by auto

lemma ReadableCaps_le:
  assumes "p \<le> q"
  shows "ReadableCaps p s \<subseteq> ReadableCaps q s"
using assms
by auto

subsection \<open>Generalised permissions of capabilities\<close>

definition GetAuthority :: "Capability \<Rightarrow> CompartmentAuthority" where
  "GetAuthority cap \<equiv> 
   if getTag cap
   then let perms = getPerms cap in
         \<lparr>SystemRegisterAccess = Access_System_Registers perms,
          ExecutableAddresses = if Permit_Execute perms then RegionOfCap cap else {},
          LoadableAddresses = if Permit_Load perms then RegionOfCap cap else {},
          CapLoadableAddresses = if Permit_Load_Capability perms then RegionOfCap cap else {},
          StorableAddresses = if Permit_Store perms then RegionOfCap cap else {},
          CapStorableAddresses = if Permit_Store_Capability perms then RegionOfCap cap else {},
          LocalCapStorableAddresses = if Permit_Store_Local_Capability perms then RegionOfCap cap else {},
          SealableTypes = if Permit_Seal perms then {t. ucast t \<in> RegionOfCap cap} else {},
          UnsealableTypes = if Permit_Unseal perms then {t. ucast t \<in> RegionOfCap cap} else {}\<rparr>
   else bot"

lemma GetAuthority_accessors:
  shows "SystemRegisterAccess (GetAuthority cap) = 
         (getTag cap \<and> Access_System_Registers (getPerms cap))"
    and "ExecutableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Execute (getPerms cap) 
          then RegionOfCap cap else {})"
    and "LoadableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Load (getPerms cap) 
          then RegionOfCap cap else {})"
    and "CapLoadableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Load_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "StorableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Store (getPerms cap) 
          then RegionOfCap cap else {})"
    and "CapStorableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Store_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "LocalCapStorableAddresses (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Store_Local_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "SealableTypes (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Seal (getPerms cap) 
          then {t. ucast t \<in> RegionOfCap cap} else {})"
    and "UnsealableTypes (GetAuthority cap) = 
         (if getTag cap \<and> Permit_Unseal (getPerms cap) 
          then {t. ucast t \<in> RegionOfCap cap} else {})"
unfolding GetAuthority_def Let_def
by simp_all

lemma GetAuthority_setMember_simp [simp]:
  shows "GetAuthority (setSealed (cap, v1)) = GetAuthority cap"
    and "GetAuthority (setType (cap, v2)) = GetAuthority cap"
    and "GetAuthority (setOffset (cap, v3)) = GetAuthority cap"
    and "GetAuthority (setUPerms (cap, v5)) = GetAuthority cap"
    and "GetAuthority (setTag (cap, False)) = bot"
unfolding GetAuthority_def
by (simp_all cong: cong)

lemma GetAuthority_le [intro]:
  assumes "cap' \<le> cap"
  shows "GetAuthority cap' \<le> GetAuthority cap"
proof (cases "getTag cap'")
  case False
  hence "GetAuthority cap' = bot"
    unfolding GetAuthority_def
    by simp
  thus ?thesis by auto
next
  case True
  have tag: "getTag cap" 
  and segment: "RegionOfCap cap' \<subseteq> RegionOfCap cap" 
  and perms: "getPerms cap' \<le> getPerms cap"
    using True assms
    by auto
  have *: "(if b then RegionOfCap cap' else {}) \<subseteq> 
           (if b' then RegionOfCap cap else {})"
     if "RegionOfCap cap' \<noteq> {} \<longrightarrow> b \<longrightarrow> b'" for b b'
    using segment that by auto
  have "(if b then ({t. ucast t \<in> RegionOfCap cap'}::ObjectType set) else {}) \<subseteq> 
        (if b' then {t. ucast t \<in> RegionOfCap cap} else {})"
     if "RegionOfCap cap' \<noteq> {} \<longrightarrow> b \<longrightarrow> b'" for b b'
    using segment that by auto
  thus ?thesis 
    using True tag perms *
    unfolding less_eq_CompartmentAuthority_ext_def
    unfolding less_eq_Perms_ext_alt
    by (strong_cong_simp add: GetAuthority_accessors)
qed

definition GetAuthorityOfCaps where
  "GetAuthorityOfCaps caps \<equiv> Sup {GetAuthority cap |cap. cap \<in> caps}"

lemma GetAuthorityOfCaps_empty [simp]:
  shows "GetAuthorityOfCaps {} = bot"
unfolding GetAuthorityOfCaps_def
by simp

lemma GetAuthorityOfCaps_singleton [simp]:
  shows "GetAuthorityOfCaps {cap} = GetAuthority cap"
unfolding GetAuthorityOfCaps_def
by simp

lemma GetAuthorityOfCaps_accessors [simp]:
  shows "SystemRegisterAccess (GetAuthorityOfCaps caps) = (\<exists>cap\<in>caps. SystemRegisterAccess (GetAuthority cap))"
    and "ExecutableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. ExecutableAddresses (GetAuthority cap))"
    and "LoadableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. LoadableAddresses (GetAuthority cap))"
    and "CapLoadableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. CapLoadableAddresses (GetAuthority cap))"
    and "StorableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. StorableAddresses (GetAuthority cap))"
    and "CapStorableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. CapStorableAddresses (GetAuthority cap))"
    and "LocalCapStorableAddresses (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. LocalCapStorableAddresses (GetAuthority cap))"
    and "SealableTypes (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. SealableTypes (GetAuthority cap))"
    and "UnsealableTypes (GetAuthorityOfCaps caps) = (\<Union>cap\<in>caps. UnsealableTypes (GetAuthority cap))"
    and "more (GetAuthorityOfCaps caps) = Sup (more ` GetAuthority ` caps)"
unfolding GetAuthorityOfCaps_def
by auto

lemma GetAuthorityOfCaps_subset [elim!]:
  assumes "caps \<subseteq> caps'"
  shows "GetAuthorityOfCaps caps \<le> GetAuthorityOfCaps caps'"
using assms
unfolding less_eq_CompartmentAuthority_ext_def
unfolding GetAuthorityOfCaps_def
unfolding Sup_CompartmentAuthority_ext_def
by auto

(*<*)
end
(*>*)
