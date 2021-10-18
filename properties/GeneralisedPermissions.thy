(*<*) 

(* Author: Kyndylan Nienhuis *)

theory GeneralisedPermissions

imports 
  "CHERI-core.CheriLemmas"
begin

(*>*)
section \<open>Generalised permissions\<close>

record GeneralisedPerm = 
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

instantiation "GeneralisedPerm_ext" :: (order) order
begin

  definition less_eq_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme \<Rightarrow> bool"
  where 
    "less_eq_GeneralisedPerm_ext perm\<^sub>1 perm\<^sub>2 \<equiv>
     (SystemRegisterAccess perm\<^sub>1 \<le> SystemRegisterAccess perm\<^sub>2) \<and>
     (ExecutableAddresses perm\<^sub>1 \<le> ExecutableAddresses perm\<^sub>2) \<and>
     (LoadableAddresses perm\<^sub>1 \<le> LoadableAddresses perm\<^sub>2) \<and>
     (CapLoadableAddresses perm\<^sub>1 \<le> CapLoadableAddresses perm\<^sub>2) \<and>
     (StorableAddresses perm\<^sub>1 \<le> StorableAddresses perm\<^sub>2) \<and>
     (CapStorableAddresses perm\<^sub>1 \<le> CapStorableAddresses perm\<^sub>2) \<and>
     (LocalCapStorableAddresses perm\<^sub>1 \<le> LocalCapStorableAddresses perm\<^sub>2) \<and>
     (SealableTypes perm\<^sub>1 \<le> SealableTypes perm\<^sub>2) \<and>
     (UnsealableTypes perm\<^sub>1 \<le> UnsealableTypes perm\<^sub>2) \<and>
     (GeneralisedPerm.more perm\<^sub>1 \<le> GeneralisedPerm.more perm\<^sub>2)"
  
  definition less_GeneralisedPerm_ext :: "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme \<Rightarrow> bool" where
    "less_GeneralisedPerm_ext perm\<^sub>1 perm\<^sub>2 \<equiv> perm\<^sub>1 \<le> perm\<^sub>2 \<and> \<not> (perm\<^sub>2 \<le> perm\<^sub>1)"
  
  instance
    by standard (auto simp: less_GeneralisedPerm_ext_def less_eq_GeneralisedPerm_ext_def)

end

subsubsection \<open>Eliminations\<close>

lemma SystemRegisterAccess_le [elim]:
  assumes "p \<le> q"
      and "SystemRegisterAccess p"
  shows "SystemRegisterAccess q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemma ExecutableAddresses_le:
  assumes "p \<le> q"
  shows "ExecutableAddresses p \<subseteq> ExecutableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas ExecutableAddresses_le_subsetD [elim] =
  subsetD[OF ExecutableAddresses_le]

lemma LoadableAddresses_le:
  assumes "p \<le> q"
  shows "LoadableAddresses p \<subseteq> LoadableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas LoadableAddresses_le_subsetD [elim] =
  subsetD[OF LoadableAddresses_le]

lemma CapLoadableAddresses_le:
  assumes "p \<le> q"
  shows "CapLoadableAddresses p \<subseteq> CapLoadableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas CapLoadableAddresses_le_subsetD [elim] =
  subsetD[OF CapLoadableAddresses_le]

lemma StorableAddresses_le:
  assumes "p \<le> q"
  shows "StorableAddresses p \<subseteq> StorableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas StorableAddresses_le_subsetD [elim] =
  subsetD[OF StorableAddresses_le]

lemma CapStorableAddresses_le:
  assumes "p \<le> q"
  shows "CapStorableAddresses p \<subseteq> CapStorableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas CapStorableAddresses_le_subsetD [elim] =
  subsetD[OF CapStorableAddresses_le]

lemma LocalCapStorableAddresses_le:
  assumes "p \<le> q"
  shows "LocalCapStorableAddresses p \<subseteq> LocalCapStorableAddresses q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas LocalCapStorableAddresses_le_subsetD [elim] =
  subsetD[OF LocalCapStorableAddresses_le]

lemma SealableTypes_le:
  assumes "p \<le> q"
  shows "SealableTypes p \<subseteq> SealableTypes q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas SealableTypes_le_subsetD [elim] =
  subsetD[OF SealableTypes_le]

lemma UnsealableTypes_le:
  assumes "p \<le> q"
  shows "UnsealableTypes p \<subseteq> UnsealableTypes q"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
by auto

lemmas UnsealableTypes_le_subsetD [elim] =
  subsetD[OF UnsealableTypes_le]

subsection \<open>Complete lattice over generalised permissions\<close>

subsubsection \<open>Bottom of generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (order_bot) order_bot
begin

  definition bot_GeneralisedPerm_ext :: "'a GeneralisedPerm_scheme" where
    "bot_GeneralisedPerm_ext = 
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
    by standard (auto simp: bot_GeneralisedPerm_ext_def less_eq_GeneralisedPerm_ext_def)

end

lemma bot_GeneralisedPerm_ext_simp [simp]:
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
unfolding bot_GeneralisedPerm_ext_def
by simp_all

subsubsection \<open>Top of generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (order_top) order_top
begin

  definition top_GeneralisedPerm_ext :: "'a GeneralisedPerm_scheme" where
    "top_GeneralisedPerm_ext = 
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
    by standard (auto simp: top_GeneralisedPerm_ext_def less_eq_GeneralisedPerm_ext_def)

end

lemma top_GeneralisedPerm_ext_simp [simp]:
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
unfolding top_GeneralisedPerm_ext_def
by simp_all

subsubsection \<open>Infimum of generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (semilattice_inf) semilattice_inf
begin

  definition inf_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "inf_GeneralisedPerm_ext left right = 
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
    by standard (auto simp: inf_GeneralisedPerm_ext_def less_eq_GeneralisedPerm_ext_def)

end

lemma inf_GeneralisedPerm_ext_simp [simp]:
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
unfolding inf_GeneralisedPerm_ext_def
by simp_all

instantiation "GeneralisedPerm_ext" :: (Inf) Inf
begin

  definition Inf_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme set \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "Inf_GeneralisedPerm_ext permSet = 
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

lemma Inf_GeneralisedPerm_ext_simp [simp]:
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
unfolding Inf_GeneralisedPerm_ext_def
by simp_all

subsubsection \<open>Supremum of generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (semilattice_sup) semilattice_sup
begin

  definition sup_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "sup_GeneralisedPerm_ext left right = 
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
    by standard (auto simp: sup_GeneralisedPerm_ext_def less_eq_GeneralisedPerm_ext_def)

end

lemma sup_GeneralisedPerm_ext_simp [simp]:
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
unfolding sup_GeneralisedPerm_ext_def
by simp_all

instantiation "GeneralisedPerm_ext" :: (Sup) Sup
begin

  definition Sup_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme set \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "Sup_GeneralisedPerm_ext permSet = 
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

lemma Sup_GeneralisedPerm_ext_simp [simp]:
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
unfolding Sup_GeneralisedPerm_ext_def
by simp_all

subsubsection \<open>Bounded, distributive lattice over generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (Lattices.lattice) Lattices.lattice
begin  

  instance by standard

end

instantiation "GeneralisedPerm_ext" :: (bounded_lattice) bounded_lattice
begin  

  instance by standard

end

instantiation "GeneralisedPerm_ext" :: (distrib_lattice) distrib_lattice
begin
  
  instance
    by standard
       (auto simp: sup_inf_distrib1 
                   inf_GeneralisedPerm_ext_def
                   sup_GeneralisedPerm_ext_def)

end

subsubsection \<open>Boolean algebra over generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (boolean_algebra) boolean_algebra
begin

  definition minus_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "minus_GeneralisedPerm_ext left right = 
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

  definition uminus_GeneralisedPerm_ext :: 
    "'a GeneralisedPerm_scheme \<Rightarrow> 'a GeneralisedPerm_scheme"
  where
    "uminus_GeneralisedPerm_ext perm = 
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
                   bot_GeneralisedPerm_ext_def
                   top_GeneralisedPerm_ext_def
                   inf_GeneralisedPerm_ext_def 
                   sup_GeneralisedPerm_ext_def
                   minus_GeneralisedPerm_ext_def
                   uminus_GeneralisedPerm_ext_def)

end

lemma minus_GeneralisedPerm_ext_simp [simp]:
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
unfolding minus_GeneralisedPerm_ext_def
by simp_all

lemma uminus_GeneralisedPerm_ext_simp [simp]:
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
unfolding uminus_GeneralisedPerm_ext_def
by simp_all

subsubsection \<open>Complete lattice over generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (complete_lattice) complete_lattice
begin
  
  instance
    proof standard
      fix x :: "'a GeneralisedPerm_ext" and A 
      assume "x \<in> A"
      thus   "less_eq (Inf A) x"
        unfolding Inf_GeneralisedPerm_ext_def
        unfolding less_eq_GeneralisedPerm_ext_def
        by (simp add: INF_lower)
    next
      fix z :: "'a GeneralisedPerm_ext" and A 
      assume "\<And>x. x \<in> A \<Longrightarrow> less_eq z x"
      thus   "less_eq z (Inf A)"
        unfolding Inf_GeneralisedPerm_ext_def
        unfolding less_eq_GeneralisedPerm_ext_def
        by (auto simp: INF_greatest)
    next
      fix x :: "'a GeneralisedPerm_ext" and A 
      assume "x \<in> A"
      thus   "less_eq x (Sup A)"
        unfolding Sup_GeneralisedPerm_ext_def
        unfolding less_eq_GeneralisedPerm_ext_def
        by (auto simp: SUP_upper)
    next
      fix z :: "'a GeneralisedPerm_ext" and A 
      assume "\<And>x. x \<in> A \<Longrightarrow> less_eq x z"
      thus   "less_eq (Sup A) z"
        unfolding Sup_GeneralisedPerm_ext_def
        unfolding less_eq_GeneralisedPerm_ext_def
        by (auto simp: SUP_least)
    next
      show "(Inf {}::'a GeneralisedPerm_ext) = top"
        unfolding Inf_GeneralisedPerm_ext_def
        unfolding top_GeneralisedPerm_ext_def
        by simp
    next
      show "(Sup {}::'a GeneralisedPerm_ext) = bot"
        unfolding Sup_GeneralisedPerm_ext_def
        unfolding bot_GeneralisedPerm_ext_def
        by simp
    qed

end

subsubsection \<open>Complete distributive lattice over generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (complete_distrib_lattice) complete_distrib_lattice
begin
  
  instance
    proof standard
      fix x :: "'a GeneralisedPerm_ext" and A 
      show "sup x (Inf A) = (INF a:A. sup x a)"
        unfolding Inf_GeneralisedPerm_ext_def
        unfolding sup_GeneralisedPerm_ext_def
        using sup_Inf[where a="GeneralisedPerm.more x"]
        by simp
    next
      fix x :: "'a GeneralisedPerm_ext" and A 
      show "inf x (Sup A) = (SUP a:A. inf x a)"
        unfolding Sup_GeneralisedPerm_ext_def
        unfolding inf_GeneralisedPerm_ext_def
        using inf_Sup[where a="GeneralisedPerm.more x"]
        by simp
    qed

end

subsubsection \<open>Complete boolean algebra over generalised permissions\<close>

instantiation "GeneralisedPerm_ext" :: (complete_boolean_algebra) complete_boolean_algebra
begin
  
  instance by standard

end

subsection \<open>Physical capability addresses\<close>

definition getPhysicalCapAddresses :: 
  "VirtualAddress set \<Rightarrow> AccessType \<Rightarrow> state \<Rightarrow> PhysicalCapAddress set" 
where
  "getPhysicalCapAddresses addrs t s \<equiv> 
   GetCapAddress ` getPhysicalAddresses addrs t s"

lemma Commute_getPhysicalCapAddresses [Commute_compositeI]: 
  assumes "Commute (read_state (getPhysicalAddresses addrs t)) m"
  shows "Commute (read_state (getPhysicalCapAddresses addrs t)) m"
using assms
unfolding getPhysicalCapAddresses_def Commute_def
by auto

lemma getPhysicalCapAddressesI [intro?]:
  assumes "getPhysicalAddress (virtualAddress, t) s = Some physicalAddress"
      and "a = GetCapAddress physicalAddress"
      and "virtualAddress \<in> addrs"
  shows "a \<in> getPhysicalCapAddresses addrs t s"
using assms
unfolding getPhysicalCapAddresses_def
unfolding getPhysicalAddresses_def
by auto

lemma getPhysicalCapAddressesI_word_cat [elim]:
  assumes "getPhysicalAddress (virtualAddress, t) s = Some (ExtendCapAddress a)"
      and "virtualAddress \<in> addrs"
  shows "a \<in> getPhysicalCapAddresses addrs t s"
using assms
using slice_cat1[where a=a and b="0::5 word" and 'a=40]
by (intro getPhysicalCapAddressesI) (auto simp: word_size)

lemma getPhysicalCapAddressesE [elim]:
  assumes "a \<in> getPhysicalCapAddresses addrs t s"
  obtains virtualAddress physicalAddress
    where "getPhysicalAddress (virtualAddress, t) s = Some physicalAddress"
      and "virtualAddress \<in> addrs" 
      and "a = GetCapAddress physicalAddress"
using assms
unfolding getPhysicalCapAddresses_def
by auto

lemma getPhysicalCapAddresses_le:
  assumes "addrs \<subseteq> addrs'"
  shows "getPhysicalCapAddresses addrs t s \<subseteq> getPhysicalCapAddresses addrs' t s"
using assms
unfolding getPhysicalCapAddresses_def
by auto

lemmas getPhysicalCapAddresses_le_subsetD [elim] =
  subsetD[OF getPhysicalCapAddresses_le]

lemma getPhysicalCapAddresses_eqI_getPhysicalAddress:
  assumes "\<And>a. getPhysicalAddress a s' = getPhysicalAddress a s"
  shows "getPhysicalCapAddresses addrs t s' = getPhysicalCapAddresses addrs t s"
using getPhysicalAddresses_eqI_getPhysicalAddress[OF assms]
unfolding getPhysicalCapAddresses_def
by simp

lemma getPhysicalCapAddresses_distrib_union:
  shows "getPhysicalCapAddresses (addrs \<union> addrs') t s =
         (getPhysicalCapAddresses addrs t s \<union> getPhysicalCapAddresses addrs' t s)"
unfolding getPhysicalCapAddresses_def
unfolding getPhysicalAddresses_distrib_union
by auto

lemma getPhysicalCapAddresses_distrib_Union:
  shows "getPhysicalCapAddresses (\<Union>addrsSet) t s =
         (\<Union>addrs\<in>addrsSet. getPhysicalCapAddresses addrs t s)"
unfolding getPhysicalCapAddresses_def
unfolding getPhysicalAddresses_distrib_Union
by auto

subsection \<open>Data writable addresses\<close>

definition StorablePhysAddresses where
  "StorablePhysAddresses gperm s \<equiv>
   getPhysicalAddresses (StorableAddresses gperm) STORE s"

lemma StorablePhysAddresses_le:
  assumes "p \<le> q"
  shows "StorablePhysAddresses p s \<subseteq> StorablePhysAddresses q s"
using getPhysicalAddresses_le[OF StorableAddresses_le[OF assms]]
unfolding StorablePhysAddresses_def
by auto

subsection \<open>Capability writable addresses\<close>

definition StorablePhysCapAddresses where
  "StorablePhysCapAddresses gperm s \<equiv>
   getPhysicalCapAddresses (StorableAddresses gperm) STORE s"

lemma StorablePhysCapAddresses_le:
  assumes "p \<le> q"
  shows "StorablePhysCapAddresses p s \<subseteq> StorablePhysCapAddresses q s"
using StorableAddresses_le[OF assms]
using getPhysicalCapAddresses_le
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

definition ReadableLocations :: "GeneralisedPerm \<Rightarrow> state \<Rightarrow> CapLocation set" where
  "ReadableLocations f s \<equiv> 
   {loc. case loc of 
      LocReg r \<Rightarrow> RegisterIsAlwaysAccessible r
    | LocMem addr \<Rightarrow> addr \<in> getPhysicalCapAddresses (CapLoadableAddresses f) LOAD s}"

lemma Commute_ReadableLocations [Commute_compositeI]: 
  assumes "\<And>addrs. Commute (read_state (getPhysicalCapAddresses addrs LOAD)) m"
  shows "Commute (read_state (ReadableLocations perm)) m"
using assms
unfolding ReadableLocations_def Commute_def
by auto

lemma ReadableLocations_simps [simp]:
  shows "(LocReg r) \<in> ReadableLocations f s = 
         (RegisterIsAlwaysAccessible r)"
    and "(LocMem addr) \<in> ReadableLocations f s = 
         (addr \<in> getPhysicalCapAddresses (CapLoadableAddresses f) LOAD s)"
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
  from getPhysicalCapAddresses_le[OF this]
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

definition Generalise :: "Capability \<Rightarrow> GeneralisedPerm" where
  "Generalise cap \<equiv> 
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

lemma Generalise_accessors:
  shows "SystemRegisterAccess (Generalise cap) = 
         (getTag cap \<and> Access_System_Registers (getPerms cap))"
    and "ExecutableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Execute (getPerms cap) 
          then RegionOfCap cap else {})"
    and "LoadableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Load (getPerms cap) 
          then RegionOfCap cap else {})"
    and "CapLoadableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Load_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "StorableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Store (getPerms cap) 
          then RegionOfCap cap else {})"
    and "CapStorableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Store_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "LocalCapStorableAddresses (Generalise cap) = 
         (if getTag cap \<and> Permit_Store_Local_Capability (getPerms cap) 
          then RegionOfCap cap else {})"
    and "SealableTypes (Generalise cap) = 
         (if getTag cap \<and> Permit_Seal (getPerms cap) 
          then {t. ucast t \<in> RegionOfCap cap} else {})"
    and "UnsealableTypes (Generalise cap) = 
         (if getTag cap \<and> Permit_Unseal (getPerms cap) 
          then {t. ucast t \<in> RegionOfCap cap} else {})"
unfolding Generalise_def Let_def
by simp_all

lemma Generalise_setMember_simp [simp]:
  shows "Generalise (setSealed (cap, v1)) = Generalise cap"
    and "Generalise (setType (cap, v2)) = Generalise cap"
    and "Generalise (setOffset (cap, v3)) = Generalise cap"
    and "Generalise (setUPerms (cap, v5)) = Generalise cap"
    and "Generalise (setTag (cap, False)) = bot"
unfolding Generalise_def
by (simp_all cong: cong)

lemma Generalise_le [intro]:
  assumes "cap' \<le> cap"
  shows "Generalise cap' \<le> Generalise cap"
proof (cases "getTag cap'")
  case False
  hence "Generalise cap' = bot"
    unfolding Generalise_def
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
    unfolding less_eq_GeneralisedPerm_ext_def
    unfolding less_eq_Perms_ext_alt
    by (strong_cong_simp add: Generalise_accessors)
qed

definition GeneraliseOfCaps where
  "GeneraliseOfCaps caps \<equiv> Sup {Generalise cap |cap. cap \<in> caps}"

lemma GeneraliseOfCaps_empty [simp]:
  shows "GeneraliseOfCaps {} = bot"
unfolding GeneraliseOfCaps_def
by simp

lemma GeneraliseOfCaps_singleton [simp]:
  shows "GeneraliseOfCaps {cap} = Generalise cap"
unfolding GeneraliseOfCaps_def
by simp

lemma GeneraliseOfCaps_accessors [simp]:
  shows "SystemRegisterAccess (GeneraliseOfCaps caps) = (\<exists>cap\<in>caps. SystemRegisterAccess (Generalise cap))"
    and "ExecutableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. ExecutableAddresses (Generalise cap))"
    and "LoadableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. LoadableAddresses (Generalise cap))"
    and "CapLoadableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. CapLoadableAddresses (Generalise cap))"
    and "StorableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. StorableAddresses (Generalise cap))"
    and "CapStorableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. CapStorableAddresses (Generalise cap))"
    and "LocalCapStorableAddresses (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. LocalCapStorableAddresses (Generalise cap))"
    and "SealableTypes (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. SealableTypes (Generalise cap))"
    and "UnsealableTypes (GeneraliseOfCaps caps) = (\<Union>cap\<in>caps. UnsealableTypes (Generalise cap))"
    and "more (GeneraliseOfCaps caps) = Sup (more ` Generalise ` caps)"
unfolding GeneraliseOfCaps_def
by auto

lemma GeneraliseOfCaps_subset [elim!]:
  assumes "caps \<subseteq> caps'"
  shows "GeneraliseOfCaps caps \<le> GeneraliseOfCaps caps'"
using assms
unfolding less_eq_GeneralisedPerm_ext_def
unfolding GeneraliseOfCaps_def
unfolding Sup_GeneralisedPerm_ext_def
by auto

(*<*)
end
(*>*)
