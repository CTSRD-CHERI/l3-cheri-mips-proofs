
(* Author: Kyndylan Nienhuis *)

(* This file contains versions of the security properties that are easier to read. *)

theory SecurityPropertiesReadable

(*<*) 
imports 
  "CHERI-instantiation.CheriInstantiation"
  "CHERI-traces.TraceProperties"
  "CHERI-traces.Examples"
  "LaTeXoutput"
begin
(*>*)

section \<open>Notation\<close>

text \<open>For readability we adhere to the following naming convention. Variables are in camelCase and
defined values and functions in PascalCase, without any underscores. There are a few exceptions, for
example \<open>dfn'Foo\<close> for the semantics of instruction \<open>Foo\<close>. Because the export of the L3 model does
not always adhere to these conventions, we define some translations in this section.

Furthermore, we hide some projections in cases where we think it will not introduce any confusion.\<close>

subsection \<open>Isabelle/HOL definitions\<close>

notation (latex output) "Set.empty" ("(\<emptyset>)") 
(* ("(\<^latex>\<open>\\IsaFunction{\<emptyset>}\<close>)") *)

(* syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set" ("(1{_ | _})")

translations
  "_Collect p P" <= "{p. P}"
  "_Collect p P" <= "{p|xs. P}" *)

notation (latex output)
  bitwise_less_eq ("(2(_)/ \<le>\<^latex>\<open>$_{\\mathrm{bitwise}}$\<close> (_))")

no_notation greater_eq (infix "\<ge>" 50)
no_notation greater (infix ">" 50)
no_translations "_Let (_binds b bs) e"  \<rightleftharpoons> "_Let b (_Let bs e)"

abbreviation Bit where "Bit \<equiv> bits_class.test_bit"

abbreviation WordToInt where "WordToInt \<equiv> uint"

abbreviation WordToNat where "WordToNat \<equiv> unat"

abbreviation UCast where "UCast \<equiv> ucast"

abbreviation SCast where "SCast \<equiv> scast"

abbreviation Slice where "Slice \<equiv> slice"

abbreviation Mask where "Mask \<equiv> mask"

abbreviation WordCat where "WordCat \<equiv> word_cat"

abbreviation ExtractByte where "ExtractByte \<equiv> extract_byte"

abbreviation Size where "Size \<equiv> size"

subsection \<open>Capability fields\<close>

abbreviation Tag where "Tag \<equiv> getTag"

abbreviation Base where "Base \<equiv> getBase"

abbreviation Length where "Length \<equiv> getLength"

abbreviation Offset where "Offset \<equiv> getOffset"

abbreviation IsSealed where "IsSealed \<equiv> getSealed"

definition Perms where "Perms cap \<equiv> reg'Perms (getPerms cap)"
declare Perms_def [simp]

definition UPerms where "UPerms cap \<equiv> reg'UPerms (getUPerms cap)"
declare UPerms_def [simp]

abbreviation ObjectType where "ObjectType \<equiv> getType"

abbreviation Reserved :: "Capability \<Rightarrow> 8 word" where "Reserved \<equiv> reserved"

nonterminal CapUpdateBinds and CapUpdateBind
syntax
  "_CapUpdateBind" :: "(Capability \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> CapUpdateBind" ("((_) \<leftarrow> (_))" 11)
  "" :: "CapUpdateBind \<Rightarrow> CapUpdateBinds" ("_")
  "_CapUpdateBinds" :: "CapUpdateBind \<Rightarrow> CapUpdateBinds \<Rightarrow> CapUpdateBinds" ("_,/ _")
  "_CapUpdate" :: "Capability \<Rightarrow> CapUpdateBinds \<Rightarrow> Capability" ("(2(_) with/ (_))" [10, 11] 10)

syntax (latex output) 
  "_CapUpdate" :: "Capability \<Rightarrow> CapUpdateBinds \<Rightarrow> Capability"
    ("(2(_) \<^latex>\<open>\\IsaKeyword{with}\<close>/ (_))")

translations
  "_CapUpdate cap (_CapUpdateBinds b bs)"  \<rightleftharpoons> "_CapUpdate (_CapUpdate cap b) bs"
  "cap with CONST Tag \<leftarrow> v"        \<leftharpoondown> "CONST setTag (cap, v)"
  "cap with CONST Offset \<leftarrow> v"     \<leftharpoondown> "CONST setOffset (cap, v)"
  "cap with CONST IsSealed \<leftarrow> v"   \<leftharpoondown> "CONST setSealed (cap, v)"
  "cap with CONST Perms \<leftarrow> v"      \<leftharpoondown> "CONST setPerms (cap, v)"
  "cap with CONST UPerms \<leftarrow> v"     \<leftharpoondown> "CONST setUPerms (cap, v)"
  "cap with CONST ObjectType \<leftarrow> v" \<leftharpoondown> "CONST setType (cap, v)"

(* abbreviation MemSegment where "MemSegment \<equiv> MemSegmentCap" *)

lemma MemSegment_alt:
"MemSegment b l \<equiv> 
 (if \<lbrakk>lbl ''Cond''\<rbrakk> WordToInt b + WordToInt l > 2 ^ Size b
  then \<lbrakk>lbl ''Wrap''\<rbrakk> {addr. True}
  else \<lbrakk>lbl ''NoWrap''\<rbrakk> {b + offset |offset. offset < l})"
unfolding MemSegment_def CheriLemmas.MemSegment_def
unfolding no_plus_overflow_uint_size word_size
unfolding atomize_eq
by auto

abbreviation CapBounds where "CapBounds \<equiv> MemSegmentCap"

lemma CapBounds_alt:
"CapBounds cap \<equiv> MemSegment (Base cap) (Length cap)"
by auto

(* lemma MemSegmentCap_alt:
"MemSegmentCap cap \<equiv> 
 (if \<lbrakk>lbl ''Cond''\<rbrakk> WordToInt (Base cap) + WordToInt (Length cap) > 2 ^ 64
  then \<lbrakk>lbl ''Wrap''\<rbrakk> {addr. True}
  else \<lbrakk>lbl ''NoWrap''\<rbrakk> {Base cap + offset |offset. offset < Length cap})"
unfolding MemSegment_def CheriLemmas.MemSegment_def
unfolding no_plus_overflow_uint_size word_size
unfolding atomize_eq
by auto *)

(* lemma mask_shiftl:
  shows "mask n << m = mask (n + m) AND NOT mask m"
by (intro word_eqI)
   (auto simp add: word_ops_nth_size nth_shiftl word_size)

lemma word_cat_right_zero:
  shows "word_cat x (0::'b::len0 word) = ucast x << LENGTH('b)"
by (intro word_eqI)
   (auto simp add: nth_word_cat nth_ucast nth_shiftl word_size) *)

abbreviation BitsToCap where "BitsToCap \<equiv> bitsToCap"

abbreviation CapToBits where "CapToBits \<equiv> capToBits"

(* lemma "bitsToCap (capToBits cap) = setTag (cap, False)"
unfolding bitsToCap_def capToBits_def
unfolding rec'Capability_def reg'Capability_def
unfolding Capability.make_def nullCap_def
apply strong_cong_simp
oops

lemma "capToBits (bitsToCap w) = w"
unfolding bitsToCap_def capToBits_def
unfolding rec'Capability_def reg'Capability_def
unfolding Capability.make_def nullCap_def
apply strong_cong_simp
oops *)

definition "PermitAccessSystemRegisters cap \<equiv> Access_System_Registers (getPerms cap)"
declare PermitAccessSystemRegisters_def [simp]

lemma PermitAccessSystemRegisters_alt:
"PermitAccessSystemRegisters cap = Bit (Perms cap) 10"
by simp

definition "IsInvokable cap \<equiv> Permit_CCall (getPerms cap)"
declare IsInvokable_def [simp]

lemma IsInvokable_alt:
"IsInvokable cap = Bit (Perms cap) 8"
by simp

definition "PermitExecute cap \<equiv> Permit_Execute (getPerms cap)"
declare PermitExecute_def [simp]

lemma PermitExecute_alt:
"PermitExecute cap = Bit (Perms cap) 1"
by simp

definition "PermitLoad cap \<equiv> Permit_Load (getPerms cap)"
declare PermitLoad_def [simp]

lemma PermitLoad_alt:
"PermitLoad cap = Bit (Perms cap) 2"
by simp

definition "PermitLoadCapability cap \<equiv> Permit_Load_Capability (getPerms cap)"
declare PermitLoadCapability_def [simp]

lemma PermitLoadCapability_alt:
"PermitLoadCapability cap = Bit (Perms cap) 4"
by simp

definition "PermitSeal cap \<equiv> Permit_Seal (getPerms cap)"
declare PermitSeal_def [simp]

lemma PermitSeal_alt:
"PermitSeal cap = Bit (Perms cap) 7"
by simp

definition "PermitUnseal cap \<equiv> Permit_Unseal (getPerms cap)"
declare PermitUnseal_def [simp]

lemma PermitUnseal_alt:
"PermitUnseal cap = Bit (Perms cap) 9"
by simp

definition "PermitStore cap \<equiv> Permit_Store (getPerms cap)"
declare PermitStore_def [simp]

lemma PermitStore_alt:
"PermitStore cap = Bit (Perms cap) 3"
by simp

definition "PermitStoreCapability cap \<equiv> Permit_Store_Capability (getPerms cap)"
declare PermitStoreCapability_def [simp]

lemma PermitStoreCapability_alt:
"PermitStoreCapability cap = Bit (Perms cap) 5"
by simp

definition "PermitStoreLocalCapability cap \<equiv> Permit_Store_Local_Capability (getPerms cap)"
declare PermitStoreLocalCapability_def [simp]

lemma PermitStoreLocalCapability_alt:
"PermitStoreLocalCapability cap = Bit (Perms cap) 6"
by simp

definition "IsGlobal cap \<equiv> Global (getPerms cap)"
declare IsGlobal_def [simp]

lemma IsGlobal_alt:
"IsGlobal cap = Bit (Perms cap) 0"
by simp

subsection \<open>Capability order\<close>

lemma CapabilityOrder:
  shows "(cap \<le> cap') is defined as
         \<lbrakk>lbl ''NoTag''\<rbrakk> (not Tag cap)
         or \<lbrakk>lbl ''Eq''\<rbrakk> cap = cap'
         or \<lbrakk>lbl ''Tag''\<rbrakk> Tag cap inline and Tag cap'
            and \<lbrakk>lbl ''Unsealed''\<rbrakk> (not IsSealed cap inline and not IsSealed cap')
            and \<lbrakk>lbl ''Segment''\<rbrakk> CapBounds cap \<subseteq> CapBounds cap'
            and \<lbrakk>lbl ''Perms''\<rbrakk> bitwise_less_eq (Perms cap) (Perms cap')
            and \<lbrakk>lbl ''UPerms''\<rbrakk> bitwise_less_eq (UPerms cap) (UPerms cap')
            and \<lbrakk>lbl ''Type''\<rbrakk> ObjectType cap = ObjectType cap'
            and \<lbrakk>lbl ''Reserved''\<rbrakk> Reserved cap = Reserved cap'"
unfolding less_eq_Capability_ext_def less_eq_Capability_def
unfolding less_eq_Perms_ext_def less_eq_Perms_def
unfolding less_eq_UPerms_ext_def less_eq_UPerms_def
unfolding atomize_eq
by auto

subsection \<open>State fields\<close>

definition Mem where "Mem s a \<equiv> getMEM a s"
declare Mem_def [simp]

(* This definition is not used in any proofs, but useful for explaining tagged memory. *)
definition TagOfDataType :: "DataType \<Rightarrow> bool" where
  "TagOfDataType d \<equiv> 
   case \<lbrakk>lbl ''Case''\<rbrakk> d of 
     DataType.Cap cap \<Rightarrow> \<lbrakk>lbl ''Cap''\<rbrakk> Tag cap
   | DataType.Raw w \<Rightarrow> \<lbrakk>lbl ''Raw''\<rbrakk> False"

definition MemData where "MemData s a \<equiv> getMemData a s"
declare MemData_def [simp]

lemma MemData_alt:
"MemData s a \<equiv> 
let upper = \<lbrakk>lbl ''Upper''\<rbrakk> Slice 5 a in
let lower = \<lbrakk>lbl ''Lower''\<rbrakk> a AND Mask 5 in
let big_endian = \<lbrakk>lbl ''BigEndian''\<rbrakk> lower XOR Mask 3 in 
let word256 = \<lbrakk>lbl ''Word''\<rbrakk> (case Mem s upper of 
                               Cap cap \<Rightarrow> CapToBits cap 
                             | Raw x \<Rightarrow> x) in
\<lbrakk>lbl ''Byte''\<rbrakk> ExtractByte (WordToNat big_endian) word256"
by (simp add: getMemData_def)

definition MemCap where "MemCap s a \<equiv> getMemCap a s"
declare MemCap_def [simp]

lemma MemCap_alt:
"MemCap s a \<equiv> 
case Mem s a of 
  Cap cap \<Rightarrow> cap 
  | Raw x \<Rightarrow> BitsToCap x"
by (strong_cong_simp add: getMemCap_def)

definition MemTag where "MemTag s a \<equiv> getMemTag a s"
declare MemTag_def [simp]

lemma MemTag_alt:
"MemTag s a \<equiv> Tag (MemCap s a)"
by (strong_cong_simp add: getMemTag_def)

abbreviation Gpr :: "state \<Rightarrow> 5 word \<Rightarrow> 64 word" where "Gpr \<equiv> c_gpr"

definition GPR where "GPR s i \<equiv> getGPR i s"
declare GPR_def [simp]

lemma GPR_alt:
"GPR s i \<equiv> 
inline if i = 0 then 0 else Gpr s i"
unfolding atomize_eq
by (auto simp: CHERI_Monadic_p256.GPR_def gpr_def 
               ValuePart_def monad_def)

abbreviation LLbit :: "state \<Rightarrow> bool option" where "LLbit \<equiv> getLLbit"

abbreviation KernelMode where "KernelMode \<equiv> getKernelMode"

abbreviation AccessToCU0 :: "state \<Rightarrow> bool" where "AccessToCU0 \<equiv> getCP0StatusCU0"

abbreviation BigEndian :: "state \<Rightarrow> bool"  where "BigEndian \<equiv> getCP0ConfigBE"

abbreviation ReverseEndian :: "state \<Rightarrow> bool"  where "ReverseEndian \<equiv> getCP0StatusRE"

abbreviation EXL :: "state \<Rightarrow> bool"  where "EXL \<equiv> getCP0StatusEXL"

abbreviation PC :: "state \<Rightarrow> 64 word"  where "PC \<equiv> getPC"

abbreviation PCC where "PCC \<equiv> getPCC"

abbreviation BranchDelay :: "state \<Rightarrow> 64 word option" where "BranchDelay \<equiv> getBranchDelay"

abbreviation BranchTo :: "state \<Rightarrow> 64 word option" where "BranchTo \<equiv> getBranchTo"

abbreviation BranchDelayPCC :: "state \<Rightarrow> (64 word \<times> Capability) option" where 
  "BranchDelayPCC \<equiv> CHERI_Monadic_p256.BranchDelayPCC"

abbreviation BranchToPCC :: "state \<Rightarrow> (64 word \<times> Capability) option" where 
  "BranchToPCC \<equiv> CHERI_Monadic_p256.BranchToPCC"

abbreviation IsUnpredictable :: "state \<Rightarrow> bool" where 
  "IsUnpredictable \<equiv> isUnpredictable"

abbreviation ExceptionSignalled :: "state \<Rightarrow> bool" where 
  "ExceptionSignalled \<equiv> getExceptionSignalled"

definition GeneralCapReg where "GeneralCapReg s i \<equiv> getCAPR i s"
declare GeneralCapReg_def [simp]

definition SpecialCapReg where "SpecialCapReg s i \<equiv> getSCAPR i s"
declare SpecialCapReg_def [simp]

abbreviation KCC where "KCC \<equiv> getKCC"

lemma KCC_alt:
"KCC s = SpecialCapReg s 29"
by simp

abbreviation EPCC where "EPCC \<equiv> getEPCC"

lemma EPCC_alt:
"EPCC s = SpecialCapReg s 31"
by simp

abbreviation IDC where "IDC \<equiv> getIDC"

lemma IDC_alt:
"IDC s = GeneralCapReg s 26"
by simp

abbreviation DDC where "DDC \<equiv> getDDC"

lemma DDC_alt:
"DDC s = SpecialCapReg s 0"
by simp

definition CapReg where "CapReg s i \<equiv> getCapReg i s"
declare CapReg_def [simp]

definition Cap where "Cap s l \<equiv> getCap l s"
declare Cap_def [simp]

subsection \<open>CHERI-MIPS auxiliary functions\<close>

lemma GetCapAddress_alt:
"GetCapAddress a \<equiv> Slice 5 a"
unfolding GetCapAddress_def
by auto

lemma ExtendCapAddress_alt:
"ExtendCapAddress a \<equiv> WordCat a (0::5 word)"
unfolding ExtendCapAddress_def
by auto

abbreviation TranslateAddr where "TranslateAddr \<equiv> getPhysicalAddress"

abbreviation TranslateBounds where "TranslateBounds \<equiv> getPhysicalAddresses"

lemma TranslateBounds_alt:
"pAddr \<in> TranslateBounds vAddrs t s
is defined as
exists vAddr.
vAddr \<in> vAddrs
and TranslateAddr (vAddr, t) s = Some pAddr"
unfolding getPhysicalAddresses_def
by auto

abbreviation TranslateCapAddresses where "TranslateCapAddresses \<equiv> getPhysicalCapAddresses"

lemma TranslateCapAddresses_alt:
"a \<in> TranslateCapAddresses vAddrs t s
is defined as
exists pAddr.
pAddr \<in> TranslateBounds vAddrs t s
and a = GetCapAddress pAddr"
unfolding getPhysicalCapAddresses_def
by auto

abbreviation EmptyGhostState :: "state \<Rightarrow> bool" where "EmptyGhostState \<equiv> getEmptyGhostState"

lemma EmptyGhostState_alt:
"EmptyGhostState s \<equiv> 
not IsUnpredictable s
and not ExceptionSignalled s 
and BranchTo s = None 
and BranchToPCC s = None"
by (simp add: CheriLemmas.EmptyGhostState_def ValueAndStatePart_simp)

abbreviation StateIsValid :: "state \<Rightarrow> bool" where "StateIsValid \<equiv> getStateIsValid"

lemma StateIsValid_alt:
"StateIsValid s \<equiv> 
EmptyGhostState s 
and BigEndian s 
and not ReverseEndian s
and (BranchDelay s = None or BranchDelayPCC s = None)"
by (simp add: CheriLemmas.StateIsValid_def ValueAndStatePart_simp)

abbreviation NextInstruction where "NextInstruction \<equiv> getNextInstruction"

lemma UnpredictableNext_alt_2:
"UnpredictableNext s \<equiv> 

 {s' |s'. (\<forall>a. MemData s' a = MemData s a) \<and>
          (\<forall>a. MemCap s' a = MemCap s a) \<and>
          (PCC s' = PCC s) \<and>
          (BranchDelay s' = BranchDelay s) \<and>
          (BranchDelayPCC s' = BranchDelayPCC s) \<and>
          (\<forall>cd. GeneralCapReg s' cd = GeneralCapReg s cd) \<and>
          (\<forall>cd. SpecialCapReg s' cd = SpecialCapReg s cd) \<and>
          (\<forall>vAddr. TranslateAddr vAddr s' = TranslateAddr vAddr s) \<and>
          (BigEndian s' = BigEndian s) \<and>
          (ReverseEndian s' = ReverseEndian s) \<and>
          EmptyGhostState s'}"
by (simp add: CheriLemmas.UnpredictableNext_def)

lemma UnpredictableNext_alt:
"s' \<in> UnpredictableNext s is defined as
((inline for all a. MemData s' a = MemData s a)
and (inline for all a. MemCap s' a = MemCap s a)
and PCC s' = PCC s
and BranchDelay s' = BranchDelay s
and BranchDelayPCC s' = BranchDelayPCC s
and (inline for all cd. GeneralCapReg s' cd = GeneralCapReg s cd)
and (inline for all cd. SpecialCapReg s' cd = SpecialCapReg s cd)
and (inline for all vAddr. TranslateAddr vAddr s' = TranslateAddr vAddr s)
and BigEndian s' = BigEndian s
and ReverseEndian s' = ReverseEndian s
and EmptyGhostState s')"
by (simp add: CheriLemmas.UnpredictableNext_def)

subsection \<open>Abstraction\<close>

lemma ExecuteProp_alt:
  "ExecuteProp sem is defined as
   for all s. 
   for all s'. 
   for all step.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (step, s') \<in> sem s
   and \<lbrakk>lbl ''NoEx''\<rbrakk> step \<noteq> SwitchDomain RaiseException
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (PCC s)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (PCC s)) 
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitExecute (PCC s)
   and \<lbrakk>lbl ''Segment''\<rbrakk> Base (PCC s) + PC s \<in> CapBounds (PCC s)"
unfolding ExecuteProp_def 
by simp

lemma LoadDataProp_alt:
  "LoadDataProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all a.
   for all ln.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> LoadDataAction auth a ln \<in> actions
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitLoad (CapReg s auth)
   and \<lbrakk>lbl ''Length''\<rbrakk> ln \<noteq> 0
   and \<lbrakk>lbl ''Segment''\<rbrakk> MemSegment a ln \<subseteq> 
       TranslateBounds (CapBounds (CapReg s auth)) LOAD s"
unfolding LoadDataProp_def 
by simp

lemma StoreDataProp_alt:
  "\<lbrakk>lbl ''Start''\<rbrakk> StoreDataProp sem is defined as
   \<lbrakk>lbl ''ForAll''\<rbrakk> (for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all a.
   for all ln.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> StoreDataAction auth a ln \<in> actions
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitStore (CapReg s auth)
   and \<lbrakk>lbl ''Length''\<rbrakk> ln \<noteq> 0
   and \<lbrakk>lbl ''Segment''\<rbrakk> MemSegment a ln \<subseteq> 
       TranslateBounds (CapBounds (CapReg s auth)) STORE s
   and \<lbrakk>lbl ''Cap''\<rbrakk> (not Tag (MemCap s' (GetCapAddress a)) 
                     or MemCap s' (GetCapAddress a) = MemCap s (GetCapAddress a)) )
   \<lbrakk>lbl ''End''\<rbrakk>"
unfolding StoreDataProp_def 
by simp

lemma RestrictCapProp_alt:
  "RestrictCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all r.
   for all r'.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> RestrictCapAction r r' \<in> actions
   then \<lbrakk>lbl ''Le''\<rbrakk> CapReg s' r' \<le> CapReg s r"
unfolding RestrictCapProp_def
by simp

lemma LoadCapProp_alt:
  "LoadCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all r.
   for all a.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> LoadCapAction auth a r \<in> actions
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''PermsLoad''\<rbrakk> PermitLoad (CapReg s auth)
   and \<lbrakk>lbl ''PermsLoadCap''\<rbrakk> PermitLoadCapability (CapReg s auth)
   and \<lbrakk>lbl ''Segment''\<rbrakk> MemSegment (ExtendCapAddress a) 32 \<subseteq> 
       TranslateBounds (CapBounds (CapReg s auth)) LOAD s
   and \<lbrakk>lbl ''Le''\<rbrakk> GeneralCapReg s' r \<le> MemCap s a"
unfolding LoadCapProp_def
by simp

lemma StoreCapProp_alt:
  "StoreCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all r.
   for all a.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> StoreCapAction auth r a \<in> actions
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''PermsStore''\<rbrakk> PermitStore (CapReg s auth)
   and \<lbrakk>lbl ''PermsStoreCap''\<rbrakk> PermitStoreCapability (CapReg s auth)
   and \<lbrakk>lbl ''Segment''\<rbrakk> MemSegment (ExtendCapAddress a) 32 \<subseteq> 
       TranslateBounds (CapBounds (CapReg s auth)) STORE s
   and \<lbrakk>lbl ''Eq''\<rbrakk> MemCap s' a = GeneralCapReg s r"
unfolding StoreCapProp_def
by simp 

lemma StoreLocalCapProp_alt:
  "StoreLocalCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all r.
   for all a.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> StoreCapAction auth r a \<in> actions
   and \<lbrakk>lbl ''SourceTag''\<rbrakk> Tag (GeneralCapReg s r)
   and \<lbrakk>lbl ''Local''\<rbrakk> (not IsGlobal (GeneralCapReg s r))
   then \<lbrakk>lbl ''Perms''\<rbrakk> PermitStoreLocalCapability (CapReg s auth)"
unfolding StoreLocalCapProp_def
by simp

lemma SealCapProp_alt:
  "SealCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all r.
   for all r'.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> SealCapAction auth r r' \<in> actions
   then \<lbrakk>lbl ''TDef''\<rbrakk> (let t = UCast (Base (CapReg s auth)) + UCast (Offset (CapReg s auth)) in
   \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitSeal (CapReg s auth)
   and \<lbrakk>lbl ''Segment''\<rbrakk> UCast t \<in> CapBounds (CapReg s auth)
   and \<lbrakk>lbl ''SourceUnsealed''\<rbrakk> (not IsSealed (GeneralCapReg s r))
   and \<lbrakk>lbl ''Result''\<rbrakk> GeneralCapReg s' r' = setType (setSealed ((GeneralCapReg s r), True), t))"
unfolding SealCapProp_def Let_def
by simp

lemma UnsealCapProp_alt:
  "UnsealCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all auth.
   for all r.
   for all r'.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''Action''\<rbrakk> UnsealCapAction auth r r' \<in> actions
   then \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s auth)
   and \<lbrakk>lbl ''NotSealed''\<rbrakk> (not IsSealed (CapReg s auth))
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitUnseal (CapReg s auth)
   and \<lbrakk>lbl ''Segment''\<rbrakk> UCast (ObjectType (GeneralCapReg s r)) \<in> CapBounds (CapReg s auth)
   and \<lbrakk>lbl ''SourceSealed''\<rbrakk> IsSealed (GeneralCapReg s r)
   and \<lbrakk>lbl ''Result''\<rbrakk> GeneralCapReg s' r' \<le> setType (setSealed ((GeneralCapReg s r), False), 0)"
unfolding UnsealCapProp_def
by auto

lemma SystemRegisterProp_alt:
  "SystemRegisterProp sem is defined as
   for all s.
   for all s'.
   for all actions. 
   for all r.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''NotDDC''\<rbrakk> (r \<noteq> 0 inline and r \<noteq> 1)
   and \<lbrakk>lbl ''Target''\<rbrakk> (exists action. action \<in> actions
                                        and r \<in> CapDerivationRegisters  action)
   then \<lbrakk>lbl ''Perms''\<rbrakk> PermitAccessSystemRegisters (PCC s)"
   (is "?l is defined as ?r")
unfolding SystemRegisterProp_def
by auto blast+

lemma InvokeCapProp_alt:
  "InvokeCapProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all r.
   for all r'.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (SwitchDomain (InvokeCapability r r'), s') \<in> sem s
   then \<lbrakk>lbl ''CodeDef''\<rbrakk> (let codeCap = GeneralCapReg s r in
   \<lbrakk>lbl ''DataDef''\<rbrakk> (let dataCap = GeneralCapReg s r' in
   \<lbrakk>lbl ''CodeSealed''\<rbrakk> (Tag codeCap inline and \<lbrakk>lbl ''DataTag''\<rbrakk> Tag dataCap)
   and \<lbrakk>lbl ''CodeTag''\<rbrakk> (IsSealed codeCap inline and \<lbrakk>lbl ''DataSealed''\<rbrakk> IsSealed dataCap)
   and \<lbrakk>lbl ''CodePerms''\<rbrakk> (IsInvokable codeCap inline and \<lbrakk>lbl ''DataPerms''\<rbrakk> IsInvokable dataCap)
   and \<lbrakk>lbl ''CodeExe''\<rbrakk> PermitExecute codeCap
   and \<lbrakk>lbl ''DataNotExe''\<rbrakk> (not PermitExecute dataCap)
   and \<lbrakk>lbl ''Type''\<rbrakk> ObjectType codeCap = ObjectType dataCap
   and \<lbrakk>lbl ''PC''\<rbrakk> PC s' = Offset codeCap
   and \<lbrakk>lbl ''PCC''\<rbrakk> PCC s' = setType (setSealed (codeCap, False), 0)
   and \<lbrakk>lbl ''BranchDelay''\<rbrakk> BranchDelay s' = None
   and \<lbrakk>lbl ''BranchDelayPCC''\<rbrakk> BranchDelayPCC s' = None
   and \<lbrakk>lbl ''IDC''\<rbrakk> IDC s' = setType (setSealed (dataCap, False), 0)
   and \<lbrakk>lbl ''CapReg''\<rbrakk> (inline for all cb. inline if cb \<noteq> 26 then GeneralCapReg s' cb = GeneralCapReg s cb)
   and \<lbrakk>lbl ''SCapReg''\<rbrakk> (inline for all cb. SpecialCapReg s' cb = SpecialCapReg s cb)
   and \<lbrakk>lbl ''Mem''\<rbrakk> (inline for all a. Mem s' a = Mem s a)))"
unfolding InvokeCapProp_def Let_def
by auto

lemma ExceptionProp_alt:
  "ExceptionProp sem is defined as
   for all s :: state.
   for all s' :: state.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (SwitchDomain RaiseException, s') \<in> sem s
   then \<lbrakk>lbl ''EXL''\<rbrakk> EXL s'
   and \<lbrakk>lbl ''PC''\<rbrakk> Base (PCC s') + PC s' \<in> ExceptionPCs
   and \<lbrakk>lbl ''PCC''\<rbrakk> PCC s' = KCC s
   and \<lbrakk>lbl ''CapReg''\<rbrakk> (inline for all r. GeneralCapReg s' r = GeneralCapReg s r)
   and \<lbrakk>lbl ''EPCC''\<rbrakk> (if EXL s 
                      then EPCC s' = EPCC s
                      else EPCC s' = setOffset (PCC s, PC s))
   and \<lbrakk>lbl ''SpecialCapReg''\<rbrakk> (inline for all r.
                               inline if r \<noteq> 31 
                               then SpecialCapReg s' r = SpecialCapReg s r)
   and \<lbrakk>lbl ''Mem''\<rbrakk> (inline for all a. Mem s' a = Mem s a)
   and \<lbrakk>lbl ''BranchDelay''\<rbrakk> BranchDelay s' = None
   and \<lbrakk>lbl ''BranchDelayPCC''\<rbrakk> BranchDelayPCC s' = None"
(is "?l is defined as ?r")
proof -
  have aux: "Q r" if "Q 31" "r \<noteq> 31 \<longrightarrow> Q r" for Q and r :: "5 word"
    using that by auto
  have "(\<forall>r. getSCAPR r s' = SignalExceptionSCAPR r s) = 
        ((if EXL s then EPCC s' = EPCC s else EPCC s' = setOffset (PCC s, PC s)) \<and>
         (\<forall>r. r \<noteq> 31 \<longrightarrow> getSCAPR r s' = getSCAPR r s))" for s s'
    unfolding SignalExceptionSCAPR_def
    by (auto intro: aux)
  thus ?thesis
    unfolding ExceptionProp_def
    by auto
qed

lemma MemoryInvariant_alt:
  "MemoryInvariant sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all a.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''NotWritten''\<rbrakk> 
       (not (exists action. action \<in> actions
                            and a \<in> WrittenAddresses action))
   then \<lbrakk>lbl ''Eq''\<rbrakk> MemData s' a = MemData s a"
unfolding MemoryInvariant_def
by auto blast?

lemma CapabilityInvariant_alt:
  "CapabilityInvariant sem is defined as
   for all s :: state.
   for all s' :: state.
   for all actions :: DomainAction set.
   for all loc :: CapLocation.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> sem s
   and \<lbrakk>lbl ''NotTarget''\<rbrakk> 
       (not (exists action. action \<in> actions
                            and loc \<in> CapDerivationTargets action))
   then \<lbrakk>lbl ''Eq''\<rbrakk> Cap s' loc = Cap s loc"
unfolding CapabilityInvariant_def
by auto blast?

lemma ValidStateProp_alt:
  "ValidStateProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all step :: InstructionIntention.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''Next''\<rbrakk> (step, s') \<in> sem s
   then (StateIsValid s')"
unfolding ValidStateProp_def
by simp

lemma AddressTranslationProp_alt:
  "AddressTranslationProp sem is defined as
   for all s :: state.
   for all s' :: state.
   for all step :: InstructionIntention.
   for all a.
   if \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
   and \<lbrakk>lbl ''NoASR''\<rbrakk> (not PermitAccessSystemRegisters (PCC s))
   and \<lbrakk>lbl ''Next''\<rbrakk> (step, s') \<in> sem s
   and \<lbrakk>lbl ''NoEx''\<rbrakk> step \<noteq> SwitchDomain RaiseException
   then TranslateAddr a s' = TranslateAddr a s"
unfolding AddressTranslationProp_def
by simp

lemma CheriAbstraction_alt:
  "CheriAbstraction sem is defined as
   LoadDataProp sem 
   and StoreDataProp sem
   and ExecuteProp sem 
   and LoadCapProp sem
   and StoreCapProp sem
   and StoreLocalCapProp sem
   and RestrictCapProp sem
   and SealCapProp sem
   and UnsealCapProp sem
   and SystemRegisterProp sem
   and InvokeCapProp sem
   and ExceptionProp sem
   and MemoryInvariant sem
   and CapabilityInvariant sem
   and ValidStateProp sem
   and AddressTranslationProp sem"
unfolding CheriAbstraction_def
by auto

(* lemma Provenance:
  "for all s.
   for all s'.
   for all loc.
   for all loc'.
   if \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> NextStates s
   and \<lbrakk>lbl ''parent''\<rbrakk> loc \<in> ProvenanceParents loc' s
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag (getCap loc' s')
   and \<lbrakk>lbl ''no-ghost''\<rbrakk> EmptyGhostState s
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> getTag (Cap s loc)"
using CapabilityProvenance
by auto

lemma BoundsMonotonicity:
  "for all s.
   for all s'.
   for all loc.
   for all loc'.
   if \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> NextStates s
   and \<lbrakk>lbl ''parent''\<rbrakk> loc \<in> ProvenanceParents loc' s
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag (getCap loc' s')
   and \<lbrakk>lbl ''no-ghost''\<rbrakk> EmptyGhostState s
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemSegment (getCap loc' s') \<subseteq> MemSegment (Cap s loc)"
using BoundsMonotonicity
by (auto del: subsetI)

lemma PermsMonotonicity:
  "for all s.
   for all s'.
   for all loc.
   for all loc'.
   if \<lbrakk>lbl ''Next''\<rbrakk> (KeepDomain actions, s') \<in> NextStates s
   and \<lbrakk>lbl ''parent''\<rbrakk> loc \<in> ProvenanceParents loc' s
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag (getCap loc' s')
   and \<lbrakk>lbl ''no-ghost''\<rbrakk> EmptyGhostState s
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> bitwise_less_eq (Perms (getCap loc' s')) (Perms (Cap s loc))"
using PermsMonotonicity
unfolding less_eq_Perms_ext_def less_eq_Perms_def
by auto *)

subsection \<open>Instantiation\<close>

lemma scast_word_cat_zero:
  fixes x :: "'a::len word"
  assumes "LENGTH('c) = LENGTH('a) + LENGTH('b)"
  shows "(scast (word_cat x (0::'b::len0 word)::'c::len word)::'d::len word) = 
         scast x << LENGTH('b)"
  (is "?l = ?r")
proof -
  have "LENGTH('b) \<le> LENGTH('a) + LENGTH('b) - Suc 0"
    using len_gt_0[where 'a='a]
    by arith
  thus ?thesis
    using assms
    by (intro word_eqI)
       (auto simp add: word_size nth_word_cat nth_shiftl nth_ucast nth_scast)
qed

(* 
Replace term:
definition $1 where "$1 \<equiv> ExecutionStep.get$1"
declare $1_def [simp]
syntax (latex output) "_$1" :: 'a ("$1")
translations "(CONST IsaDefinition _$1)" \<leftharpoondown> "CONST $1"

CAndPermActions
CBuildCapActions
CClearHiActions
CClearLoActions
CClearTagActions
CCopyTypeActions
CFromPtrActions
CGetPCCActions
CGetPCCSetOffsetActions
CIncOffsetActions
CIncOffsetImmediateActions
CJALRActions
CJRActions
CLCVirtualAddress
CLCPhysicalAddress
CLCActions
CLLCVirtualAddress
CLLCPhysicalAddress
CLLCActions
CMOVNActions
CMOVZActions
CReadHwrActions
CMoveActions
CSCVirtualAddress
CSCPhysicalAddress
CSCActions
CSCCVirtualAddress
CSCCPhysicalAddress
CSCCActions
CSealActions
CSetBoundsActions 
CSetBoundsExactActions
CSetBoundsImmediateActions
CSetOffsetActions
CUnsealActions
CWriteHwrActions
ERETActions
LegacyLoadVirtualAddress
LegacyLoadPhysicalAddress
LegacyLoadActions
LBActions
LBUActions
LHActions
LHUActions
LWActions
LWUActions
LLActions
LDActions
LLDActions
LWLActions
LWRActions
LDLActions
LDRActions
CLoadVirtualAddress
CLoadPhysicalAddress
CLoadActions
CLLxVirtualAddress
CLLxPhysicalAddress
CLLxActions
LegacyStoreVirtualAddress
LegacyStorePhysicalAddress
LegacyStoreActions
SBActions
SHActions
SWActions
SDActions
SCActions
SCDActions
SWLActions
SWRActions
SDLActions
SDRActions
CStoreVirtualAddress
CStorePhysicalAddress
CStoreActions
CSCxVirtualAddress
CSCxPhysicalAddress
CSCxActions
RunActions
TakeBranchActions
DomainActions

*)

definition CAndPermActions where "CAndPermActions \<equiv> ExecutionStep.getCAndPermActions"
declare CAndPermActions_def [simp]

lemma CAndPermActions_alt:
  "CAndPermActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CAndPermActions_def)

definition CBuildCapActions where "CBuildCapActions \<equiv> ExecutionStep.getCBuildCapActions"
declare CBuildCapActions_def [simp]

lemma CBuildCapActions_alt:
  "CBuildCapActions (cd, cb, ct) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CBuildCapActions_def)

definition CClearHiActions where "CClearHiActions \<equiv> ExecutionStep.getCClearHiActions"
declare CClearHiActions_def [simp]

lemma CClearHiActions_alt:
  "CClearHiActions m s = 
   {RestrictCapAction (RegNormal cd) (RegNormal cd) |cd. Bit m (WordToNat (cd - 16))}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CClearHiActions_def)

definition CClearLoActions where "CClearLoActions \<equiv> ExecutionStep.getCClearLoActions"
declare CClearLoActions_def [simp]

lemma CClearLoActions_alt:
  "CClearLoActions m s =
   {RestrictCapAction (RegNormal cd) (RegNormal cd) |cd. Bit m (WordToNat cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CClearLoActions_def)

definition CClearTagActions where "CClearTagActions \<equiv> ExecutionStep.getCClearTagActions"
declare CClearTagActions_def [simp]

lemma CClearTagActions_alt:
  "CClearTagActions (cd, cb) s = {RestrictCapAction (RegNormal cd) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CClearTagActions_def)

definition CCopyTypeActions where "CCopyTypeActions \<equiv> ExecutionStep.getCCopyTypeActions"
declare CCopyTypeActions_def [simp]

lemma CCopyTypeActions_alt:
  "CCopyTypeActions (cd, cb, ct) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CCopyTypeActions_def)

definition CFromPtrActions where "CFromPtrActions \<equiv> ExecutionStep.getCFromPtrActions"
declare CFromPtrActions_def [simp]

lemma CFromPtrActions_alt:
  "CFromPtrActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CFromPtrActions_def)

definition CGetPCCActions where "CGetPCCActions \<equiv> ExecutionStep.getCGetPCCActions"
declare CGetPCCActions_def [simp]

lemma CGetPCCActions_alt:
  "CGetPCCActions cd s = {RestrictCapAction RegPCC (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CGetPCCActions_def)

definition CGetPCCSetOffsetActions where "CGetPCCSetOffsetActions \<equiv> ExecutionStep.getCGetPCCSetOffsetActions"
declare CGetPCCSetOffsetActions_def [simp]

lemma CGetPCCSetOffsetActions_alt:
  "CGetPCCSetOffsetActions (cd, rs) s = {RestrictCapAction RegPCC (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CGetPCCSetOffsetActions_def)

definition CIncOffsetActions where "CIncOffsetActions \<equiv> ExecutionStep.getCIncOffsetActions"
declare CIncOffsetActions_def [simp]

lemma CIncOffsetActions_alt:
  "CIncOffsetActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CIncOffsetActions_def)

definition CIncOffsetImmediateActions where "CIncOffsetImmediateActions \<equiv> ExecutionStep.getCIncOffsetImmediateActions"
declare CIncOffsetImmediateActions_def [simp]

lemma CIncOffsetImmediateActions_alt:
  "CIncOffsetImmediateActions (cd, cb, increment) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CIncOffsetImmediateActions_def)

definition CJALRActions where "CJALRActions \<equiv> ExecutionStep.getCJALRActions"
declare CJALRActions_def [simp]

lemma CJALRActions_alt:
  "CJALRActions (cd, cb) s \<equiv>
   (if cb = cd
    then {RestrictCapAction RegPCC (RegNormal cd), RestrictCapAction RegPCC RegBranchDelayPCC}
    else {RestrictCapAction RegPCC (RegNormal cd), RestrictCapAction (RegNormal cb) RegBranchDelayPCC})"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CJALRActions_def)

definition CJRActions where "CJRActions \<equiv> ExecutionStep.getCJRActions"
declare CJRActions_def [simp]

lemma CJRActions_alt:
  "CJRActions cb s = {RestrictCapAction (RegNormal cb) RegBranchDelayPCC}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CJRActions_def)

definition CLCVirtualAddress where "CLCVirtualAddress \<equiv> ExecutionStep.getCLCVirtualAddress"
declare CLCVirtualAddress_def [simp]

lemma CLCVirtualAddress_alt:
  "CLCVirtualAddress cb rt offset s \<equiv>
   Base (GeneralCapReg s cb) + Offset (GeneralCapReg s cb) + GPR s rt + 16 * SCast offset"
by (simp add: ValueAndStatePart_simp 
              scast_word_cat_zero shiftl_t2n
              ExecutionStep.CLCVirtualAddress_def)

definition CLCPhysicalAddress where "CLCPhysicalAddress \<equiv> ExecutionStep.getCLCPhysicalAddress"
declare CLCPhysicalAddress_def [simp]

lemma CLCPhysicalAddress_alt:
  "CLCPhysicalAddress cb rt offset s \<equiv>
   TranslateAddr (CLCVirtualAddress cb rt offset s, LOAD) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.CLCPhysicalAddress_def)

definition CLCActions where "CLCActions \<equiv> ExecutionStep.getCLCActions"
declare CLCActions_def [simp]

lemma CLCActions_alt:
  "CLCActions (cd, cb, rt, offset) s \<equiv>
   (case (getCLCPhysicalAddress cb rt offset) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> (if PermitLoadCapability (getCAPR cb s)
               then {LoadCapAction (RegNormal cb) (GetCapAddress a) cd}
               else {RestrictCapAction (RegNormal cd) (RegNormal cd),
                     LoadDataAction (RegNormal cb) a 32}))"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CLCActions_def
         split: option.splits)

definition CLLCVirtualAddress where "CLLCVirtualAddress \<equiv> ExecutionStep.getCLLCVirtualAddress"
declare CLLCVirtualAddress_def [simp]

lemma CLLCVirtualAddress_alt:
  "CLLCVirtualAddress cb s \<equiv>
   Base (GeneralCapReg s cb) + Offset (GeneralCapReg s cb)"
by (simp add: ValueAndStatePart_simp 
              scast_word_cat_zero shiftl_t2n
              ExecutionStep.CLLCVirtualAddress_def)

definition CLLCPhysicalAddress where "CLLCPhysicalAddress \<equiv> ExecutionStep.getCLLCPhysicalAddress"
declare CLLCPhysicalAddress_def [simp]

lemma CLLCPhysicalAddress_alt:
  "CLLCPhysicalAddress cb s \<equiv>
   TranslateAddr (CLLCVirtualAddress cb s, LOAD) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.CLLCPhysicalAddress_def)

definition CLLCActions where "CLLCActions \<equiv> ExecutionStep.getCLLCActions"
declare CLLCActions_def [simp]

lemma CLLCActions_alt:
  "CLLCActions (cd, cb) s \<equiv>
   (case (getCLLCPhysicalAddress cb) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> (if PermitLoadCapability (getCAPR cb s)
               then {LoadCapAction (RegNormal cb) (GetCapAddress a) cd}
               else {RestrictCapAction (RegNormal cd) (RegNormal cd),
                     LoadDataAction (RegNormal cb) a 32}))"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CLLCActions_def
         split: option.splits)

definition CMOVNActions where "CMOVNActions \<equiv> ExecutionStep.getCMOVNActions"
declare CMOVNActions_def [simp]

lemma CMOVNActions_alt:
  "CMOVNActions (cd, cb, rt) s \<equiv>
   (if GPR s rt \<noteq> 0
    then {RestrictCapAction (RegNormal cb) (RegNormal cd)}
    else {})"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CMOVNActions_def)

definition CMOVZActions where "CMOVZActions \<equiv> ExecutionStep.getCMOVZActions"
declare CMOVZActions_def [simp]

lemma CMOVZActions_alt:
  "CMOVZActions (cd, cb, rt) s \<equiv>
   (if GPR s rt = 0
    then {RestrictCapAction (RegNormal cb) (RegNormal cd)}
    else {})"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CMOVZActions_def)

definition CMoveActions where "CMoveActions \<equiv> ExecutionStep.getCMoveActions"
declare CMoveActions_def [simp]

lemma CMoveActions_alt:
  "CMoveActions (cd, cs) s = {RestrictCapAction (RegNormal cs) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CMoveActions_def)

definition CReadHwrActions where "CReadHwrActions \<equiv> ExecutionStep.getCReadHwrActions"
declare CReadHwrActions_def [simp]

lemma CReadHwrActions_alt:
  "CReadHwrActions (cd, selector) s = 
   {RestrictCapAction (RegSpecial selector) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CReadHwrActions_def)

definition CSCVirtualAddress where "CSCVirtualAddress \<equiv> ExecutionStep.getCSCVirtualAddress"
declare CSCVirtualAddress_def [simp]

lemma CSCVirtualAddress_alt:
  "CSCVirtualAddress cb rt offset s \<equiv>
   Base (GeneralCapReg s cb) + Offset (GeneralCapReg s cb) + GPR s rt + 16 * SCast offset"
by (simp add: ValueAndStatePart_simp 
              scast_word_cat_zero shiftl_t2n
              ExecutionStep.CSCVirtualAddress_def)

definition CSCPhysicalAddress where "CSCPhysicalAddress \<equiv> ExecutionStep.getCSCPhysicalAddress"
declare CSCPhysicalAddress_def [simp]

lemma CSCPhysicalAddress_alt:
  "CSCPhysicalAddress cb rt offset s \<equiv>
   TranslateAddr (CSCVirtualAddress cb rt offset s, STORE) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.CSCPhysicalAddress_def)

definition CSCActions where "CSCActions \<equiv> ExecutionStep.getCSCActions"
declare CSCActions_def [simp]

lemma CSCActions_alt:
  "CSCActions (cs, cb, rt, offset) s \<equiv>
   (case (getCSCPhysicalAddress cb rt offset) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {StoreCapAction (RegNormal cb) cs (GetCapAddress a)})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSCActions_def cong: cong)

definition CSCCVirtualAddress where "CSCCVirtualAddress \<equiv> ExecutionStep.getCSCCVirtualAddress"
declare CSCCVirtualAddress_def [simp]

lemma CSCCVirtualAddress_alt:
  "CSCCVirtualAddress cb s \<equiv>
   Base (GeneralCapReg s cb) + Offset (GeneralCapReg s cb)"
by (simp add: ValueAndStatePart_simp 
              scast_word_cat_zero shiftl_t2n
              ExecutionStep.CSCCVirtualAddress_def)

definition CSCCPhysicalAddress where "CSCCPhysicalAddress \<equiv> ExecutionStep.getCSCCPhysicalAddress"
declare CSCCPhysicalAddress_def [simp]

lemma CSCCPhysicalAddress_alt:
  "CSCCPhysicalAddress cb s \<equiv>
   TranslateAddr (CSCCVirtualAddress cb s, STORE) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.CSCCPhysicalAddress_def)

definition CSCCActions where "CSCCActions \<equiv> ExecutionStep.getCSCCActions"
declare CSCCActions_def [simp]

lemma CSCCActions_alt:
  "CSCCActions (cs, cb, rd) s \<equiv>
   (case LLbit s of
    None \<Rightarrow> {} |
    Some False \<Rightarrow> {} |
    Some True \<Rightarrow> (case (getCSCCPhysicalAddress cb) s of
                  None \<Rightarrow> {} |
                  Some a \<Rightarrow> {StoreCapAction (RegNormal cb) cs (GetCapAddress a)}))"
unfolding atomize_eq
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSCCActions_def
         split: option.splits)

definition CSealActions where "CSealActions \<equiv> ExecutionStep.getCSealActions"
declare CSealActions_def [simp]

lemma CSealActions_alt:
  "CSealActions (cd, cs, ct) s \<equiv> 
  inline if cd = 0 then {} 
  else {SealCapAction (RegNormal ct) cs cd}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSealActions_def cong: cong)

definition CSetBoundsActions where "CSetBoundsActions \<equiv> ExecutionStep.getCSetBoundsActions"
declare CSetBoundsActions_def [simp]

lemma CSetBoundsActions_alt:
  "CSetBoundsActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSetBoundsActions_def)
 
definition CSetBoundsExactActions where "CSetBoundsExactActions \<equiv> ExecutionStep.getCSetBoundsExactActions"
declare CSetBoundsExactActions_def [simp]

lemma CSetBoundsExactActions_alt:
  "CSetBoundsExactActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSetBoundsExactActions_def)

definition CSetBoundsImmediateActions where "CSetBoundsImmediateActions \<equiv> ExecutionStep.getCSetBoundsImmediateActions"
declare CSetBoundsImmediateActions_def [simp]

lemma CSetBoundsImmediateActions_alt:
  "CSetBoundsImmediateActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSetBoundsImmediateActions_def)

definition CSetOffsetActions where "CSetOffsetActions \<equiv> ExecutionStep.getCSetOffsetActions"
declare CSetOffsetActions_def [simp]

lemma CSetOffsetActions_alt:
  "CSetOffsetActions (cd, cb, rt) s = {RestrictCapAction (RegNormal cb) (RegNormal cd)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSetOffsetActions_def)

definition CUnsealActions where "CUnsealActions \<equiv> ExecutionStep.getCUnsealActions"
declare CUnsealActions_def [simp]

lemma CUnsealActions_alt:
  "CUnsealActions (cd, cs, ct) s \<equiv> 
   inline if cd = 0 then {} 
   else {UnsealCapAction (RegNormal ct) cs cd}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CUnsealActions_def cong: cong)

definition CWriteHwrActions where "CWriteHwrActions \<equiv> ExecutionStep.getCWriteHwrActions"
declare CWriteHwrActions_def [simp]

lemma CWriteHwrActions_alt:
  "CWriteHwrActions (cb, selector) s = 
   {RestrictCapAction (RegNormal cb) (RegSpecial selector)}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CWriteHwrActions_def)

definition ERETActions where "ERETActions \<equiv> ExecutionStep.getERETActions"
declare ERETActions_def [simp]

lemma ERETActions_alt:
  "ERETActions s = {RestrictCapAction (RegSpecial 31) RegPCC}"
by (auto simp: ValueAndStatePart_simp ExecutionStep.ERETActions_def)

definition LegacyLoadVirtualAddress where "LegacyLoadVirtualAddress \<equiv> ExecutionStep.getLegacyLoadVirtualAddress"
declare LegacyLoadVirtualAddress_def [simp]

lemma LegacyLoadVirtualAddress_alt:
  "LegacyLoadVirtualAddress b offset s \<equiv>
   Base (getDDC s) + Offset (getDDC s) + getGPR b s + SCast offset"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.LegacyLoadVirtualAddress_def)

definition LegacyLoadPhysicalAddress where "LegacyLoadPhysicalAddress \<equiv> ExecutionStep.getLegacyLoadPhysicalAddress"
declare LegacyLoadPhysicalAddress_def [simp]

lemma LegacyLoadPhysicalAddress_alt:
  "LegacyLoadPhysicalAddress b offset s \<equiv>
   TranslateAddr (LegacyLoadVirtualAddress b offset s, LOAD) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.LegacyLoadPhysicalAddress_def)

definition LegacyLoadActions where "LegacyLoadActions \<equiv> ExecutionStep.getLegacyLoadActions"
declare LegacyLoadActions_def [simp]

lemma LegacyLoadActions_alt:
  "LegacyLoadActions b offset l s \<equiv>
   (case (getLegacyLoadPhysicalAddress b offset) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {LoadDataAction (RegSpecial 0) a l})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.LegacyLoadActions_def cong: cong)

definition LBActions where "LBActions \<equiv> ExecutionStep.getLBActions"
declare LBActions_def [simp]

lemma LBActions_alt:
  "LBActions (b, rt, offset) s \<equiv> LegacyLoadActions b offset 1 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.LBActions_def)

definition LBUActions where "LBUActions \<equiv> ExecutionStep.getLBUActions"
declare LBUActions_def [simp]

lemma LBUActions_alt:
  "LBUActions (b, rt, offset) s = LegacyLoadActions b offset 1 s"
by (simp add: ExecutionStep.LBUActions_def)

definition LHActions where "LHActions \<equiv> ExecutionStep.getLHActions"
declare LHActions_def [simp]

lemma LHActions_alt:
  "LHActions (b, rt, offset) s = LegacyLoadActions b offset 2 s"
by (simp add: ExecutionStep.LHActions_def)

definition LHUActions where "LHUActions \<equiv> ExecutionStep.getLHUActions"
declare LHUActions_def [simp]

lemma LHUActions_alt:
  "LHUActions (b, rt, offset) s = LegacyLoadActions b offset 2 s"
by (simp add: ExecutionStep.LHUActions_def)

definition LWActions where "LWActions \<equiv> ExecutionStep.getLWActions"
declare LWActions_def [simp]

lemma LWActions_alt:
  "LWActions (b, rt, offset) s = LegacyLoadActions b offset 4 s"
by (simp add: ExecutionStep.LWActions_def)

definition LWUActions where "LWUActions \<equiv> ExecutionStep.getLWUActions"
declare LWUActions_def [simp]

lemma LWUActions_alt:
  "LWUActions (b, rt, offset) s = LegacyLoadActions b offset 4 s"
by (simp add: ExecutionStep.LWUActions_def)

definition LLActions where "LLActions \<equiv> ExecutionStep.getLLActions"
declare LLActions_def [simp]

lemma LLActions_alt:
  "LLActions (b, rt, offset) s = LegacyLoadActions b offset 4 s"
by (simp add: ExecutionStep.LLActions_def)

definition LDActions where "LDActions \<equiv> ExecutionStep.getLDActions"
declare LDActions_def [simp]

lemma LDActions_alt:
  "LDActions (b, rt, offset) s = LegacyLoadActions b offset 8 s"
by (simp add: ExecutionStep.LDActions_def)

definition LLDActions where "LLDActions \<equiv> ExecutionStep.getLLDActions"
declare LLDActions_def [simp]

lemma LLDActions_alt:
  "LLDActions (b, rt, offset) s = LegacyLoadActions b offset 8 s"
by (simp add: ExecutionStep.LLDActions_def)

definition LWLActions where "LWLActions \<equiv> ExecutionStep.getLWLActions"
declare LWLActions_def [simp]

lemma LWLActions_alt:
  "LWLActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyLoadVirtualAddress b offset s in
   let length = (NOT UCast vAddr AND Mask 2) + 1 in
   case TranslateAddr (vAddr, LOAD) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {LoadDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.LWLActions_def cong: cong)

definition LWRActions where "LWRActions \<equiv> ExecutionStep.getLWRActions"
declare LWRActions_def [simp]

lemma LWRActions_alt:
  "LWRActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyLoadVirtualAddress b offset s in
   let length = (UCast vAddr AND Mask 2) + 1 in
   case TranslateAddr (vAddr AND NOT mask 2, LOAD) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {LoadDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.LWRActions_def cong: cong)

definition LDLActions where "LDLActions \<equiv> ExecutionStep.getLDLActions"
declare LDLActions_def [simp]

lemma LDLActions_alt:
  "LDLActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyLoadVirtualAddress b offset s in
   let length = (NOT UCast vAddr AND Mask 3) + 1 in
   case TranslateAddr (vAddr, LOAD) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {LoadDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.LDLActions_def cong: cong)

definition LDRActions where "LDRActions \<equiv> ExecutionStep.getLDRActions"
declare LDRActions_def [simp]

lemma LDRActions_alt:
  "LDRActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyLoadVirtualAddress b offset s in
   let length = (UCast vAddr AND Mask 3) + 1 in
   case TranslateAddr (vAddr AND NOT mask 3, LOAD) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {LoadDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.LDRActions_def cong: cong)

definition CLoadVirtualAddress where "CLoadVirtualAddress \<equiv> ExecutionStep.getCLoadVirtualAddress"
declare CLoadVirtualAddress_def [simp]

lemma CLoadVirtualAddress_alt:
  "CLoadVirtualAddress cb rt offset t s \<equiv>
   Base (getCAPR cb s) + Offset (getCAPR cb s) + getGPR rt s + (SCast offset << WordToNat t)"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.CLoadVirtualAddress_def)

definition CLoadPhysicalAddress where "CLoadPhysicalAddress \<equiv> ExecutionStep.getCLoadPhysicalAddress"
declare CLoadPhysicalAddress_def [simp]

lemma CLoadPhysicalAddress_alt:
  "CLoadPhysicalAddress cb rt offset t s \<equiv>
   TranslateAddr (CLoadVirtualAddress cb rt offset t s, LOAD) s"
unfolding atomize_eq
by (auto split: option.splits
         simp add: ValueAndStatePart_simp 
                   ExecutionStep.CLoadPhysicalAddress_def)

definition CLoadActions where "CLoadActions \<equiv> ExecutionStep.getCLoadActions"
declare CLoadActions_def [simp]

lemma CLoadActions_alt:
  "CLoadActions (rd, cb, rt, offset, s, t) s \<equiv>
   (case (CLoadPhysicalAddress cb rt offset t) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {LoadDataAction (RegNormal cb) a (2 ^ WordToNat t)})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CLoadActions_def cong: cong)

definition CLLxVirtualAddress where "CLLxVirtualAddress \<equiv> ExecutionStep.getCLLxVirtualAddress"
declare CLLxVirtualAddress_def [simp]

lemma CLLxVirtualAddress_alt:
  "CLLxVirtualAddress cb s \<equiv>
   Base (getCAPR cb s) + Offset (getCAPR cb s)"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.CLLxVirtualAddress_def)

definition CLLxPhysicalAddress where "CLLxPhysicalAddress \<equiv> ExecutionStep.getCLLxPhysicalAddress"
declare CLLxPhysicalAddress_def [simp]

lemma CLLxPhysicalAddress_alt:
  "CLLxPhysicalAddress cb s \<equiv>
   TranslateAddr (CLLxVirtualAddress cb s, LOAD) s"
unfolding atomize_eq
by (auto split: option.splits
         simp add: ValueAndStatePart_simp 
                   ExecutionStep.CLLxPhysicalAddress_def)

definition CLLxActions where "CLLxActions \<equiv> ExecutionStep.getCLLxActions"
declare CLLxActions_def [simp]

lemma CLLxActions_alt:
  "CLLxActions (rd, cb, stt) s \<equiv>
   (case (CLLxPhysicalAddress cb) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {LoadDataAction (RegNormal cb) a (2 ^ WordToNat (stt AND mask 2))})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CLLxActions_def cong: cong)

definition LegacyStoreVirtualAddress where "LegacyStoreVirtualAddress \<equiv> ExecutionStep.getLegacyStoreVirtualAddress"
declare LegacyStoreVirtualAddress_def [simp]

lemma LegacyStoreVirtualAddress_alt:
  "LegacyStoreVirtualAddress b offset s \<equiv>
   Base (getDDC s) + Offset (getDDC s) + getGPR b s + SCast offset"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.LegacyStoreVirtualAddress_def)

definition LegacyStorePhysicalAddress where "LegacyStorePhysicalAddress \<equiv> ExecutionStep.getLegacyStorePhysicalAddress"
declare LegacyStorePhysicalAddress_def [simp]

lemma LegacyStorePhysicalAddress_alt:
  "LegacyStorePhysicalAddress b offset s \<equiv>
   TranslateAddr (LegacyStoreVirtualAddress b offset s, STORE) s"
by (simp add: ValueAndStatePart_simp 
              ExecutionStep.LegacyStorePhysicalAddress_def)

definition LegacyStoreActions where "LegacyStoreActions \<equiv> ExecutionStep.getLegacyStoreActions"
declare LegacyStoreActions_def [simp]

lemma LegacyStoreActions_alt:
  "LegacyStoreActions b offset l s \<equiv>
   (case (getLegacyStorePhysicalAddress b offset) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {StoreDataAction (RegSpecial 0) a l})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.LegacyStoreActions_def cong: cong)

definition SBActions where "SBActions \<equiv> ExecutionStep.getSBActions"
declare SBActions_def [simp]

lemma SBActions_alt:
  "SBActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 1 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SBActions_def)

definition SHActions where "SHActions \<equiv> ExecutionStep.getSHActions"
declare SHActions_def [simp]

lemma SHActions_alt:
  "SHActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 2 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SHActions_def)

definition SWActions where "SWActions \<equiv> ExecutionStep.getSWActions"
declare SWActions_def [simp]

lemma SWActions_alt:
  "SWActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 4 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SWActions_def)

definition SDActions where "SDActions \<equiv> ExecutionStep.getSDActions"
declare SDActions_def [simp]

lemma SDActions_alt:
  "SDActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 8 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SDActions_def)

definition SCActions where "SCActions \<equiv> ExecutionStep.getSCActions"
declare SCActions_def [simp]

lemma SCActions_alt:
  "SCActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 4 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SCActions_def)

definition SCDActions where "SCDActions \<equiv> ExecutionStep.getSCDActions"
declare SCDActions_def [simp]

lemma SCDActions_alt:
  "SCDActions (b, rt, offset) s \<equiv> LegacyStoreActions b offset 8 s"
by (auto simp: ValueAndStatePart_simp ExecutionStep.SCDActions_def)

definition SWLActions where "SWLActions \<equiv> ExecutionStep.getSWLActions"
declare SWLActions_def [simp]

lemma SWLActions_alt:
  "SWLActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyStoreVirtualAddress b offset s in
   let length = (NOT UCast vAddr AND Mask 2) + 1 in
   case TranslateAddr (vAddr, STORE) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {StoreDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.SWLActions_def cong: cong)

definition SWRActions where "SWRActions \<equiv> ExecutionStep.getSWRActions"
declare SWRActions_def [simp]

lemma SWRActions_alt:
  "SWRActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyStoreVirtualAddress b offset s in
   let length = (UCast vAddr AND Mask 2) + 1 in
   case TranslateAddr (vAddr AND NOT mask 2, STORE) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {StoreDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.SWRActions_def cong: cong)

definition SDLActions where "SDLActions \<equiv> ExecutionStep.getSDLActions"
declare SDLActions_def [simp]

lemma SDLActions_alt:
  "SDLActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyStoreVirtualAddress b offset s in
   let length = (NOT UCast vAddr AND Mask 3) + 1 in
   case TranslateAddr (vAddr, STORE) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {StoreDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.SDLActions_def cong: cong)

definition SDRActions where "SDRActions \<equiv> ExecutionStep.getSDRActions"
declare SDRActions_def [simp]

lemma SDRActions_alt:
  "SDRActions (b, rt, offset) s \<equiv>
   let vAddr = LegacyStoreVirtualAddress b offset s in
   let length = (UCast vAddr AND Mask 3) + 1 in
   case TranslateAddr (vAddr AND NOT mask 3, STORE) s of 
     None \<Rightarrow> {}
   | Some pAddr \<Rightarrow> {StoreDataAction (RegSpecial 0) pAddr length}"
by (auto simp: Let_def ValueAndStatePart_simp ExecutionStep.SDRActions_def cong: cong)

definition CStoreVirtualAddress where "CStoreVirtualAddress \<equiv> ExecutionStep.getCStoreVirtualAddress"
declare CStoreVirtualAddress_def [simp]

lemma CStoreVirtualAddress_alt:
  "CStoreVirtualAddress cb rt offset t s \<equiv>
   Base (getCAPR cb s) + Offset (getCAPR cb s) + getGPR rt s + (SCast offset << WordToNat t)"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.CStoreVirtualAddress_def)

definition CStorePhysicalAddress where "CStorePhysicalAddress \<equiv> ExecutionStep.getCStorePhysicalAddress"
declare CStorePhysicalAddress_def [simp]

lemma CStorePhysicalAddress_alt:
  "CStorePhysicalAddress cb rt offset t s \<equiv>
   TranslateAddr (CStoreVirtualAddress cb rt offset t s, STORE) s"
unfolding atomize_eq
by (auto split: option.splits
         simp add: ValueAndStatePart_simp 
                   ExecutionStep.CStorePhysicalAddress_def)

definition CStoreActions where "CStoreActions \<equiv> ExecutionStep.getCStoreActions"
declare CStoreActions_def [simp]

lemma CStoreActions_alt:
  "CStoreActions (rs, cb, rt, offset, t) s \<equiv>
   (case (CStorePhysicalAddress cb rt offset t) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {StoreDataAction (RegNormal cb) a (2 ^ WordToNat t)})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CStoreActions_def cong: cong)

definition CSCxVirtualAddress where "CSCxVirtualAddress \<equiv> ExecutionStep.getCSCxVirtualAddress"
declare CSCxVirtualAddress_def [simp]

lemma CSCxVirtualAddress_alt:
  "CSCxVirtualAddress cb s \<equiv>
   Base (getCAPR cb s) + Offset (getCAPR cb s)"
unfolding atomize_eq
by (simp add: ValueAndStatePart_simp
              ExecutionStep.CSCxVirtualAddress_def)

definition CSCxPhysicalAddress where "CSCxPhysicalAddress \<equiv> ExecutionStep.getCSCxPhysicalAddress"
declare CSCxPhysicalAddress_def [simp]

lemma CSCxPhysicalAddress_alt:
  "CSCxPhysicalAddress cb s \<equiv>
   TranslateAddr (CSCxVirtualAddress cb s, STORE) s"
unfolding atomize_eq
by (auto split: option.splits
         simp add: ValueAndStatePart_simp 
                   ExecutionStep.CSCxPhysicalAddress_def)

definition CSCxActions where "CSCxActions \<equiv> ExecutionStep.getCSCxActions"
declare CSCxActions_def [simp]

lemma CSCxActions_alt:
  "CSCxActions (rs, cb, rd, t) s \<equiv>
   (case (CSCxPhysicalAddress cb) s of
    None \<Rightarrow> {} |
    Some a \<Rightarrow> {StoreDataAction (RegNormal cb) a (2 ^ WordToNat t)})"
by (auto simp: ValueAndStatePart_simp ExecutionStep.CSCxActions_def cong: cong)

definition RunActions where "RunActions \<equiv> ExecutionStep.getRunActions"
declare RunActions_def [simp]

definition TakeBranchActions where "TakeBranchActions \<equiv> ExecutionStep.getTakeBranchActions"
declare TakeBranchActions_def [simp]

lemma TakeBranchActions_alt:
  "TakeBranchActions s \<equiv>
   case BranchDelayPCC s of None \<Rightarrow> {} 
   | Some _ \<Rightarrow> {RestrictCapAction RegBranchDelayPCC RegBranchDelayPCC,
                RestrictCapAction RegBranchDelayPCC RegPCC}"
unfolding atomize_eq
by (auto split: option.splits
         simp add: ValueAndStatePart_simp ExecutionStep.TakeBranchActions_def is_some_def)

definition DomainActions where "DomainActions \<equiv> ExecutionStep.getDomainActions"
declare DomainActions_def [simp]

lemma DomainActions_alt:
  "DomainActions s \<equiv>
   case NextInstruction s of None \<Rightarrow> {} 
   | Some inst \<Rightarrow> RunActions (Decode inst) s \<union> TakeBranchActions s"
unfolding atomize_eq
by (strong_cong_simp add: ValueAndStatePart_simp ExecutionStep.DomainActions_def)

definition Next where "Next s = StatePart CHERI_Monadic_p256.Next s"
declare Next_def [simp]

definition NextWithGhostState where "NextWithGhostState s = StatePart CheriLemmas.NextWithGhostState s"
declare NextWithGhostState_def [simp]

abbreviation SemanticsCheriMips where "SemanticsCheriMips \<equiv> NextStates"

lemma SemanticsCheriMips_alt:
  "SemanticsCheriMips s \<equiv>
   if IsUnpredictable (NextWithGhostState s) 
   then {(KeepDomain {}, s') |s'. s' \<in> UnpredictableNext s}
   else if ExceptionSignalled (NextWithGhostState s)
   then {(SwitchDomain RaiseException, Next s)} 
   else case CCallFastInstructionParam s of 
     None \<Rightarrow> {(KeepDomain (DomainActions s), Next s)}
   | Some (r, r') \<Rightarrow> {(SwitchDomain (InvokeCapability r r'), Next s)}"
unfolding atomize_eq 
by (auto split: option.splits
         simp add: ValueAndStatePart_simp 
                   ExecutionStep.NextNonExceptionStep_def 
                   ExecutionStep.NextStates_def)

subsection \<open>Trace properties\<close>

abbreviation BotGeneralisedPerm :: GeneralisedPerm where "BotGeneralisedPerm \<equiv> bot"

abbreviation TopGeneralisedPerm :: GeneralisedPerm where "TopGeneralisedPerm \<equiv> top"

lemma RegisterIsAlwaysAccessible_alt:
"RegisterIsAlwaysAccessible r \<equiv>
case r of RegPCC \<Rightarrow> True
        | RegBranchDelayPCC \<Rightarrow> True
        | RegBranchToPCC \<Rightarrow> True
        | RegNormal r \<Rightarrow> True
        | RegSpecial r \<Rightarrow> (r = 0 inline or r = 1)"
unfolding atomize_eq
unfolding RegisterIsAlwaysAccessible_def
by (cases r) auto

lemma ReadableLocations_alt:
"loc \<in> ReadableLocations gPerm s 
is defined as
case loc of LocReg r \<Rightarrow> RegisterIsAlwaysAccessible r
          | LocMem addr \<Rightarrow> addr \<in> TranslateCapAddresses (CapLoadableAddresses gPerm) LOAD s"
unfolding ReadableLocations_def
by auto

lemma ReadableCaps_alt:
"cap \<in> ReadableCaps gPerm s 
is defined as
exists loc.
loc \<in> ReadableLocations gPerm s 
and cap = Cap s loc 
and Tag cap"
unfolding ReadableCaps_def
by auto

lemma StorablePhysAddresses_alt:
"StorablePhysAddresses gPerm s \<equiv>
TranslateBounds (StorableAddresses gPerm) STORE s"
unfolding StorablePhysAddresses_def
by auto

lemma StorablePhysCapAddresses_alt:
"StorablePhysCapAddresses gPerm s \<equiv>
TranslateCapAddresses (StorableAddresses gPerm) STORE s"
unfolding StorablePhysCapAddresses_def
by auto

abbreviation GPermOfCap where "GPermOfCap \<equiv> getGPerm"

lemma GPermOfCap_alt:
"GPermOfCap cap \<equiv>
 if Tag cap
 then \<lparr>SystemRegisterAccess = PermitAccessSystemRegisters cap,
        ExecutableAddresses = if PermitExecute cap then CapBounds cap else {},
        LoadableAddresses = if PermitLoad cap then CapBounds cap else {},
        CapLoadableAddresses = if PermitLoadCapability cap then CapBounds cap else {},
        StorableAddresses = if PermitStore cap then CapBounds cap else {},
        CapStorableAddresses = if PermitStoreCapability cap then CapBounds cap else {},
        LocalCapStorableAddresses = if PermitStoreLocalCapability cap and PermitStoreCapability cap 
                              then CapBounds cap else {},
        SealableTypes = if PermitSeal cap 
                        then {t. ucast t \<in> CapBounds cap} else {},
        UnsealableTypes = if PermitUnseal cap 
                          then {t. ucast t \<in> CapBounds cap} else {}\<rparr>
 else BotGeneralisedPerm"
unfolding atomize_eq
unfolding getGPerm_def Let_def
by auto

lemma GPermOfCap_SystemRegisterAccess:
"SystemRegisterAccess (GPermOfCap cap) \<equiv> 
Tag cap inline and PermitAccessSystemRegisters cap"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_ExecutableAddresses:
"ExecutableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitExecute cap 
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_LoadableAddresses:
"LoadableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitLoad cap
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_CapLoadableAddresses:
"CapLoadableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitLoadCapability cap
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_StorableAddresses:
"StorableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitStore cap
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_CapStorableAddresses:
"CapStorableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitStoreCapability cap 
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_LocalCapStorableAddresses:
"LocalCapStorableAddresses (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitStoreLocalCapability cap inline and PermitStoreCapability cap 
then CapBounds cap 
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_SealableTypes:
"SealableTypes (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitSeal cap 
then {t. ucast t \<in> CapBounds cap}
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_UnsealableTypes:
"UnsealableTypes (GPermOfCap cap) \<equiv> 
if Tag cap inline and PermitUnseal cap 
then {t. ucast t \<in> CapBounds cap}
else {}"
by (simp add: getGPerm_accessors)

lemma GPermOfCap_le:
"if cap \<le> cap'
then GPermOfCap cap \<le> GPermOfCap cap'"
using getGPerm_le
by auto

abbreviation GPermOfCaps where "GPermOfCaps \<equiv> getGPermOfCaps"

lemma GPermOfCaps_alt:
"GPermOfCaps caps \<equiv>
Sup {GPermOfCap cap |cap. cap \<in> caps}"
unfolding getGPermOfCaps_def
by auto

lemma ReachableCaps_Reg:
  "for all s.
   for all r.
   if \<lbrakk>lbl ''Accessible''\<rbrakk> RegisterIsAlwaysAccessible r
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag (CapReg s r)
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> CapReg s r \<in> ReachableCaps s"
using ReachableCaps.Reg
by auto

lemma ReachableCaps_Memory:
  "for all s.
   for all addr.
   for all cap.
   if \<lbrakk>lbl ''Parent''\<rbrakk> cap \<in> ReachableCaps s
   and \<lbrakk>lbl ''Unsealed''\<rbrakk> (not IsSealed cap)
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitLoadCapability cap
   and \<lbrakk>lbl ''Addr''\<rbrakk> addr \<in> TranslateCapAddresses (CapBounds cap) LOAD s
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag (MemCap s addr)
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemCap s addr \<in> ReachableCaps s"
using ReachableCaps.Memory
by auto

lemma ReachableCaps_Restrict:
  "for all s.
   for all cap.
   for all cap'.
   if \<lbrakk>lbl ''Parent''\<rbrakk> cap \<in> ReachableCaps s
   and \<lbrakk>lbl ''Le''\<rbrakk> cap' \<le> cap
   and \<lbrakk>lbl ''Tag''\<rbrakk> Tag cap'
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> cap' \<in> ReachableCaps s"
using ReachableCaps.Restrict
by auto

lemma ReachableCaps_Seal:
  "for all s.
   for all t.
   for all cap.
   for all sealer.
   if \<lbrakk>lbl ''Parent''\<rbrakk> cap \<in> ReachableCaps s
   and \<lbrakk>lbl ''Unsealed''\<rbrakk> (not IsSealed cap)
   and \<lbrakk>lbl ''Sealer''\<rbrakk> sealer \<in> ReachableCaps s
   and \<lbrakk>lbl ''SealerUnsealed''\<rbrakk> (not IsSealed sealer)
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitSeal sealer
   and \<lbrakk>lbl ''Type''\<rbrakk> UCast t \<in> CapBounds sealer
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> setType (setSealed (cap, True), t) \<in> ReachableCaps s"
using ReachableCaps.Seal
by auto

lemma ReachableCaps_Unseal:
  "for all s.
   for all cap.
   for all unsealer.
   if \<lbrakk>lbl ''Parent''\<rbrakk> cap \<in> ReachableCaps s
   and \<lbrakk>lbl ''Sealed''\<rbrakk> IsSealed cap
   and \<lbrakk>lbl ''Unsealer''\<rbrakk> unsealer \<in> ReachableCaps s
   and \<lbrakk>lbl ''UnsealerUnsealed''\<rbrakk> (not IsSealed unsealer)
   and \<lbrakk>lbl ''Perms''\<rbrakk> PermitUnseal unsealer
   and \<lbrakk>lbl ''Type''\<rbrakk> UCast (ObjectType cap) \<in> CapBounds unsealer
   then \<lbrakk>lbl ''Conclusion''\<rbrakk> setType (setSealed (cap, False), 0) \<in> ReachableCaps s"
using ReachableCaps.Unseal
by auto

lemma TransUsableCaps_alt:
"cap \<in> TransUsableCaps s
is defined as 
cap \<in> ReachableCaps s inline and not IsSealed cap"
unfolding TransUsableCaps_def
by auto

lemma ReachablePermissions_alt:
"ReachablePermissions s \<equiv>
GPermOfCaps (TransUsableCaps s)"
unfolding ReachablePermissions_def
by auto

lemma IntraDomainTrace_Nil:
"IntraDomainTrace [] = True"
by simp

lemma IntraDomainTrace_Cons:
"IntraDomainTrace (trace; step) \<equiv>
KeepsDomain step 
and IntraDomainTrace trace"
by simp

lemma FutureStates_Nil:
"FutureStates sem s\<^sub>0 [] = {s\<^sub>0}"
by simp

lemma FutureStates_Cons:
"s\<^sub>2 \<in> FutureStates sem s\<^sub>0 (trace; step)
is defined as
exists s\<^sub>1.
s\<^sub>1 \<in> FutureStates sem s\<^sub>0 trace 
and (step, s\<^sub>2) \<in> sem s\<^sub>1"
by auto

lemma MonotonicityReachableCaps_alt:
"MonotonicityReachableCaps sem 
is defined as
for all s. for all s'. for all trace.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s trace
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> ReachableCaps s' \<subseteq> ReachableCaps s"
unfolding MonotonicityReachableCaps_def
by auto

lemma AbstractionImpliesMonotonicityReachableCaps:
"if CheriAbstraction sem
then MonotonicityReachableCaps sem"
using TraceProperties.AbstractionImpliesMonotonicityReachableCaps
by auto

lemma SameDomainSystemRegInvariant_alt:
"SameDomainSystemRegInvariant sem
is defined as
for all s. for all s'. for all trace. for all r.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s trace
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Exceptions''\<rbrakk> (r \<noteq> 0 inline and r \<noteq> 1)
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> SpecialCapReg s' r = SpecialCapReg s r"
unfolding SameDomainSystemRegInvariant_def
by auto

lemma AbstractionImpliesSameDomainSystemRegInvariant:
"if CheriAbstraction sem
then SameDomainSystemRegInvariant sem"
using TraceProperties.AbstractionImpliesSameDomainSystemRegInvariant
by auto

lemma DomainCrossSystemRegInvariant_alt:
"DomainCrossSystemRegInvariant sem
is defined as
for all s. for all s'. for all trace. for all step. for all r.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s (trace; step) 
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''Inter''\<rbrakk> SwitchesDomain step
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Exceptions''\<rbrakk> (r \<noteq> 0 inline and r \<noteq> 1 inline and r \<noteq> 31)
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> SpecialCapReg s' r = SpecialCapReg s r"
unfolding DomainCrossSystemRegInvariant_def
by auto

lemma AbstractionImpliesDomainCrossSystemRegInvariant:
"if CheriAbstraction sem
then DomainCrossSystemRegInvariant sem"
using TraceProperties.AbstractionImpliesDomainCrossSystemRegInvariant
by auto

lemma SameDomainMemCapInvariant_alt:
"SameDomainMemCapInvariant sem
is defined as
for all s. for all s'. for all trace. for all a.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s trace
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not a \<in> StorablePhysCapAddresses (ReachablePermissions s) s)
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemCap s' a = MemCap s a"
unfolding SameDomainMemCapInvariant_def
by auto

lemma AbstractionImpliesSameDomainMemCapInvariant:
"if CheriAbstraction sem
then SameDomainMemCapInvariant sem"
using TraceProperties.AbstractionImpliesSameDomainMemCapInvariant
by auto

lemma DomainCrossMemCapInvariant_alt:
"DomainCrossMemCapInvariant sem
is defined as
for all s. for all s'. for all trace. for all step. for all a.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s (trace; step) 
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''Inter''\<rbrakk> SwitchesDomain step
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not a \<in> StorablePhysCapAddresses (ReachablePermissions s) s)
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemCap s' a = MemCap s a"
unfolding DomainCrossMemCapInvariant_def
by auto

lemma AbstractionImpliesDomainCrossMemCapInvariant:
"if CheriAbstraction sem
then DomainCrossMemCapInvariant sem"
using TraceProperties.AbstractionImpliesDomainCrossMemCapInvariant
by auto

lemma SameDomainMemoryInvariant_alt:
"SameDomainMemoryInvariant sem
is defined as
for all s. for all s'. for all trace. for all a.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s trace
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not a \<in> StorablePhysAddresses (ReachablePermissions s) s)
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemData s' a = MemData s a"
unfolding SameDomainMemoryInvariant_def
by auto

lemma AbstractionImpliesSameDomainMemoryInvariant:
"if CheriAbstraction sem
then SameDomainMemoryInvariant sem"
using TraceProperties.AbstractionImpliesSameDomainMemoryInvariant
by auto

lemma DomainCrossMemoryInvariant_alt:
"DomainCrossMemoryInvariant sem
is defined as
for all s. for all s'. for all trace. for all step. for all a.
if \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s (trace; step) 
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace 
and \<lbrakk>lbl ''Inter''\<rbrakk> SwitchesDomain step
and \<lbrakk>lbl ''NoAccess''\<rbrakk> (not a \<in> StorablePhysAddresses (ReachablePermissions s) s)
and \<lbrakk>lbl ''NoSRA''\<rbrakk> (not SystemRegisterAccess (ReachablePermissions s))
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s
then \<lbrakk>lbl ''Conclusion''\<rbrakk> MemData s' a = MemData s a"
unfolding DomainCrossMemoryInvariant_def
by auto

lemma AbstractionImpliesDomainCrossMemoryInvariant:
"if CheriAbstraction sem
then DomainCrossMemoryInvariant sem"
using TraceProperties.AbstractionImpliesDomainCrossMemoryInvariant
by auto

lemma PermIsClosed_alt:
"PermIsClosed perm s 
is defined as
for all cap.
if cap \<in> ReadableCaps perm s
and (not IsSealed cap inline or ObjectType cap \<in> UnsealableTypes perm)
then GPermOfCap cap \<le> perm"
unfolding PermIsClosed_def
by auto

(* lemma InvokableCapsNotUnsealable_alt:
"InvokableCapsNotUnsealable perm s 
is defined as
for all cap.
if cap \<in> ReadableCaps perm s
and IsInvokable cap
then IsSealed cap 
and not ObjectType cap \<in> UnsealableTypes perm"
unfolding InvokableCapsNotUnsealable_def
by auto *)

lemma CapabilityAligned_alt:
"CapabilityAligned addresses 
is defined as
for all a. for all b.
if a AND NOT mask 5 = b AND NOT mask 5
and a \<in> addresses
then b \<in> addresses"
unfolding CapabilityAligned_def
by auto

lemma AccessibleCaps_alt:
"cap \<in> AccessibleCaps addrs s
is defined as
(exists r. RegisterIsAlwaysAccessible r 
           and cap = CapReg s r)
or (exists a. a \<in> TranslateBounds addrs LOAD s
              and cap = MemCap s (GetCapAddress a))"
unfolding AccessibleCaps_def
by auto

lemma UsableCaps_alt:
"cap \<in> UsableCaps addrs types s
is defined as
cap \<in> AccessibleCaps addrs s
and Tag cap
and (not IsSealed cap or ObjectType cap \<in> types)"
unfolding UsableCaps_def
by auto

lemma InvokableCaps_alt:
"cap \<in> InvokableCaps addrs s
is defined as
cap \<in> AccessibleCaps addrs s
and Tag cap 
and IsInvokable cap"
unfolding InvokableCaps_def
by auto

lemma InvokableAddresses_alt:
"a \<in> InvokableAddresses addrs s
is defined as
exists cap. 
cap \<in> InvokableCaps addrs s
and a = Base cap + Offset cap"
unfolding InvokableAddresses_def
by auto

lemma NoSystemRegisterAccess_alt:
"NoSystemRegisterAccess addrs types s 
is defined as
for all cap. 
if cap \<in> UsableCaps addrs types s 
then not PermitAccessSystemRegisters cap"
unfolding NoSystemRegisterAccess_def
by auto

lemma ContainedCapBounds_alt:
"ContainedCapBounds addrs types s
is defined as
for all cap. 
if cap \<in> UsableCaps addrs types s 
and (PermitExecute cap
     or PermitLoad cap
     or PermitLoadCapability cap
     or PermitStore cap
     or PermitStoreCapability cap)
then CapBounds cap \<subseteq> addrs"
unfolding ContainedCapBounds_def
by auto

lemma ContainedObjectTypes_alt:
"ContainedObjectTypes addrs types s 
is defined as
for all cap. for all t.
if cap \<in> UsableCaps addrs types s 
and (PermitSeal cap inline or PermitUnseal cap)
and UCast t \<in> CapBounds cap
then t \<in> types"
unfolding ContainedObjectTypes_def
by auto

lemma InvokableCapsNotUsable_alt:
"InvokableCapsNotUsable addrs types s
is defined as 
for all cap. 
if cap \<in> InvokableCaps addrs s
then IsSealed cap inline and ObjectType cap \<notin> types"
unfolding InvokableCapsNotUsable_def
by auto

lemma IsolatedState_alt:
"IsolatedState addrs types s 
is defined as
\<lbrakk>lbl ''Aligned''\<rbrakk> CapabilityAligned addrs
and \<lbrakk>lbl ''SystemReg''\<rbrakk> NoSystemRegisterAccess addrs types s 
and \<lbrakk>lbl ''Segment''\<rbrakk> ContainedCapBounds addrs types s
and \<lbrakk>lbl ''Types''\<rbrakk> ContainedObjectTypes addrs types s 
and \<lbrakk>lbl ''NotUnsealable''\<rbrakk> InvokableCapsNotUsable addrs types s
and \<lbrakk>lbl ''Valid''\<rbrakk> StateIsValid s"
unfolding IsolatedState_def
by simp

lemma IsolationGuarantees_alt:
"IsolationGuarantees addrs types s s' 
is defined as
(\<lbrakk>lbl ''Entry''\<rbrakk> Base (PCC s') + PC s' \<in> ExceptionPCs \<union> InvokableAddresses addrs s 
\<lbrakk>lbl ''EntryEnd''\<rbrakk>)
and \<lbrakk>lbl ''Memory''\<rbrakk> (inline for all a. 
     inline if not \<lbrakk>lbl ''Translate''\<rbrakk> a \<in> TranslateBounds addrs STORE s
     then (\<lbrakk>lbl ''Value''\<rbrakk> MemData s' a = MemData s a
           and \<lbrakk>lbl ''Tag''\<rbrakk> MemTag s' (GetCapAddress a) = MemTag s (GetCapAddress a)))
\<lbrakk>lbl ''MemoryEnd''\<rbrakk>
and \<lbrakk>lbl ''SystemReg''\<rbrakk> (inline for all r. 
     inline if r \<noteq> 0 inline and r \<noteq> 1 inline and r \<noteq> 31
     then SpecialCapReg s' r = SpecialCapReg s r)
\<lbrakk>lbl ''SystemRegEnd''\<rbrakk> "
unfolding IsolationGuarantees_def
by simp

lemma CompartmentIsolation_alt:
"CompartmentIsolation sem
is defined as
for all addrs. for all types. for all s. for all s'. for all trace. for all step. 
if \<lbrakk>lbl ''Isolated''\<rbrakk> IsolatedState addrs types s 
and \<lbrakk>lbl ''Intra''\<rbrakk> IntraDomainTrace trace
and \<lbrakk>lbl ''Inter''\<rbrakk> SwitchesDomain step
and \<lbrakk>lbl ''Trace''\<rbrakk> s' \<in> FutureStates sem s (trace; step)
then \<lbrakk>lbl ''Guarantees''\<rbrakk> IsolationGuarantees addrs types s s'"
unfolding CompartmentIsolation_def
by simp

lemma AbstractionImpliesCompartmentIsolation:
"if CheriAbstraction sem
then CompartmentIsolation sem"
using Examples.CompartmentIsolation
by auto

subsection \<open>Generated snippets and syntax\<close>

(* Code generation - snippets *)

syntax (latex output) "_None" :: 'a ("None")
translations "(CONST IsaConstructor _None)" \<leftharpoondown> "CONST option.None"

text_raw \<open>
\DefineSnippet{None-type}{%
@{typeof "option.None"}
}%EndSnippet\<close>

syntax (latex output) "_Some" :: 'a ("Some")
translations "(CONST IsaConstructor _Some)" \<leftharpoondown> "CONST option.Some"

text_raw \<open>
\DefineSnippet{Some-type}{%
@{typeof "option.Some"}
}%EndSnippet\<close>

syntax (latex output) "_Load" :: 'a ("Load")
translations "(CONST IsaConstructor _Load)" \<leftharpoondown> "CONST AccessType.LOAD"

text_raw \<open>
\DefineSnippet{Load-type}{%
@{typeof "AccessType.LOAD"}
}%EndSnippet\<close>

syntax (latex output) "_Store" :: 'a ("Store")
translations "(CONST IsaConstructor _Store)" \<leftharpoondown> "CONST AccessType.STORE"

text_raw \<open>
\DefineSnippet{Store-type}{%
@{typeof "AccessType.STORE"}
}%EndSnippet\<close>

syntax (latex output) "_RawDataType" :: 'a ("RawDataType")
translations "(CONST IsaConstructor _RawDataType)" \<leftharpoondown> "CONST DataType.Raw"

text_raw \<open>
\DefineSnippet{RawDataType-type}{%
@{typeof "DataType.Raw"}
}%EndSnippet\<close>

syntax (latex output) "_CapDataType" :: 'a ("CapDataType")
translations "(CONST IsaConstructor _CapDataType)" \<leftharpoondown> "CONST DataType.Cap"

text_raw \<open>
\DefineSnippet{CapDataType-type}{%
@{typeof "DataType.Cap"}
}%EndSnippet\<close>

syntax (latex output) "_RegPCC" :: 'a ("RegPCC")
translations "(CONST IsaConstructor _RegPCC)" \<leftharpoondown> "CONST CapRegister.RegPCC"

text_raw \<open>
\DefineSnippet{RegPCC-type}{%
@{typeof "CapRegister.RegPCC"}
}%EndSnippet\<close>

syntax (latex output) "_RegBranchDelayPCC" :: 'a ("RegBranchDelayPCC")
translations "(CONST IsaConstructor _RegBranchDelayPCC)" \<leftharpoondown> "CONST CapRegister.RegBranchDelayPCC"

text_raw \<open>
\DefineSnippet{RegBranchDelayPCC-type}{%
@{typeof "CapRegister.RegBranchDelayPCC"}
}%EndSnippet\<close>

syntax (latex output) "_RegBranchToPCC" :: 'a ("RegBranchToPCC")
translations "(CONST IsaConstructor _RegBranchToPCC)" \<leftharpoondown> "CONST CapRegister.RegBranchToPCC"

text_raw \<open>
\DefineSnippet{RegBranchToPCC-type}{%
@{typeof "CapRegister.RegBranchToPCC"}
}%EndSnippet\<close>

syntax (latex output) "_RegNormal" :: 'a ("RegNormal")
translations "(CONST IsaConstructor _RegNormal)" \<leftharpoondown> "CONST CapRegister.RegNormal"

text_raw \<open>
\DefineSnippet{RegNormal-type}{%
@{typeof "CapRegister.RegNormal"}
}%EndSnippet\<close>

syntax (latex output) "_RegSpecial" :: 'a ("RegSpecial")
translations "(CONST IsaConstructor _RegSpecial)" \<leftharpoondown> "CONST CapRegister.RegSpecial"

text_raw \<open>
\DefineSnippet{RegSpecial-type}{%
@{typeof "CapRegister.RegSpecial"}
}%EndSnippet\<close>

syntax (latex output) "_LoadDataAction" :: 'a ("LoadDataAction")
translations "(CONST IsaConstructor _LoadDataAction)" \<leftharpoondown> "CONST DomainAction.LoadDataAction"

text_raw \<open>
\DefineSnippet{LoadDataAction-type}{%
@{typeof "DomainAction.LoadDataAction"}
}%EndSnippet\<close>

syntax (latex output) "_StoreDataAction" :: 'a ("StoreDataAction")
translations "(CONST IsaConstructor _StoreDataAction)" \<leftharpoondown> "CONST DomainAction.StoreDataAction"

text_raw \<open>
\DefineSnippet{StoreDataAction-type}{%
@{typeof "DomainAction.StoreDataAction"}
}%EndSnippet\<close>

syntax (latex output) "_RestrictCapAction" :: 'a ("RestrictCapAction")
translations "(CONST IsaConstructor _RestrictCapAction)" \<leftharpoondown> "CONST DomainAction.RestrictCapAction"

text_raw \<open>
\DefineSnippet{RestrictCapAction-type}{%
@{typeof "DomainAction.RestrictCapAction"}
}%EndSnippet\<close>

syntax (latex output) "_LoadCapAction" :: 'a ("LoadCapAction")
translations "(CONST IsaConstructor _LoadCapAction)" \<leftharpoondown> "CONST DomainAction.LoadCapAction"

text_raw \<open>
\DefineSnippet{LoadCapAction-type}{%
@{typeof "DomainAction.LoadCapAction"}
}%EndSnippet\<close>

syntax (latex output) "_StoreCapAction" :: 'a ("StoreCapAction")
translations "(CONST IsaConstructor _StoreCapAction)" \<leftharpoondown> "CONST DomainAction.StoreCapAction"

text_raw \<open>
\DefineSnippet{StoreCapAction-type}{%
@{typeof "DomainAction.StoreCapAction"}
}%EndSnippet\<close>

syntax (latex output) "_SealCapAction" :: 'a ("SealCapAction")
translations "(CONST IsaConstructor _SealCapAction)" \<leftharpoondown> "CONST DomainAction.SealCapAction"

text_raw \<open>
\DefineSnippet{SealCapAction-type}{%
@{typeof "DomainAction.SealCapAction"}
}%EndSnippet\<close>

syntax (latex output) "_UnsealCapAction" :: 'a ("UnsealCapAction")
translations "(CONST IsaConstructor _UnsealCapAction)" \<leftharpoondown> "CONST DomainAction.UnsealCapAction"

text_raw \<open>
\DefineSnippet{UnsealCapAction-type}{%
@{typeof "DomainAction.UnsealCapAction"}
}%EndSnippet\<close>

syntax (latex output) "_RaiseException" :: 'a ("RaiseException")
translations "(CONST IsaConstructor _RaiseException)" \<leftharpoondown> "CONST DomainSwitch.RaiseException"

text_raw \<open>
\DefineSnippet{RaiseException-type}{%
@{typeof "DomainSwitch.RaiseException"}
}%EndSnippet\<close>

syntax (latex output) "_InvokeCapability" :: 'a ("InvokeCapability")
translations "(CONST IsaConstructor _InvokeCapability)" \<leftharpoondown> "CONST DomainSwitch.InvokeCapability"

text_raw \<open>
\DefineSnippet{InvokeCapability-type}{%
@{typeof "DomainSwitch.InvokeCapability"}
}%EndSnippet\<close>

syntax (latex output) "_KeepDomain" :: 'a ("KeepDomain")
translations "(CONST IsaConstructor _KeepDomain)" \<leftharpoondown> "CONST InstructionIntention.KeepDomain"

text_raw \<open>
\DefineSnippet{KeepDomain-type}{%
@{typeof "InstructionIntention.KeepDomain"}
}%EndSnippet\<close>

syntax (latex output) "_SwitchDomain" :: 'a ("SwitchDomain")
translations "(CONST IsaConstructor _SwitchDomain)" \<leftharpoondown> "CONST InstructionIntention.SwitchDomain"

text_raw \<open>
\DefineSnippet{SwitchDomain-type}{%
@{typeof "InstructionIntention.SwitchDomain"}
}%EndSnippet\<close>

syntax (latex output) "_Tag" :: 'a ("Tag")
translations "(CONST IsaField _Tag)" \<leftharpoondown> "CONST Tag"

text_raw \<open>
\DefineSnippet{Tag-type}{%
@{typeof "Tag"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Tag-field-type}{%
@{typeof "Tag x"}
}%EndSnippet\<close>

syntax (latex output) "_Base" :: 'a ("Base")
translations "(CONST IsaField _Base)" \<leftharpoondown> "CONST Base"

text_raw \<open>
\DefineSnippet{Base-type}{%
@{typeof "Base"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Base-field-type}{%
@{typeof "Base x"}
}%EndSnippet\<close>

syntax (latex output) "_Length" :: 'a ("Length")
translations "(CONST IsaField _Length)" \<leftharpoondown> "CONST Length"

text_raw \<open>
\DefineSnippet{Length-type}{%
@{typeof "Length"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Length-field-type}{%
@{typeof "Length x"}
}%EndSnippet\<close>

syntax (latex output) "_Offset" :: 'a ("Offset")
translations "(CONST IsaField _Offset)" \<leftharpoondown> "CONST Offset"

text_raw \<open>
\DefineSnippet{Offset-type}{%
@{typeof "Offset"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Offset-field-type}{%
@{typeof "Offset x"}
}%EndSnippet\<close>

syntax (latex output) "_IsSealed" :: 'a ("IsSealed")
translations "(CONST IsaField _IsSealed)" \<leftharpoondown> "CONST IsSealed"

text_raw \<open>
\DefineSnippet{IsSealed-type}{%
@{typeof "IsSealed"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsSealed-field-type}{%
@{typeof "IsSealed x"}
}%EndSnippet\<close>

syntax (latex output) "_Perms" :: 'a ("Perms")
translations "(CONST IsaField _Perms)" \<leftharpoondown> "CONST Perms"

text_raw \<open>
\DefineSnippet{Perms-type}{%
@{typeof "Perms"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Perms-field-type}{%
@{typeof "Perms x"}
}%EndSnippet\<close>

syntax (latex output) "_UPerms" :: 'a ("UPerms")
translations "(CONST IsaField _UPerms)" \<leftharpoondown> "CONST UPerms"

text_raw \<open>
\DefineSnippet{UPerms-type}{%
@{typeof "UPerms"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UPerms-field-type}{%
@{typeof "UPerms x"}
}%EndSnippet\<close>

syntax (latex output) "_ObjectType" :: 'a ("ObjectType")
translations "(CONST IsaField _ObjectType)" \<leftharpoondown> "CONST ObjectType"

text_raw \<open>
\DefineSnippet{ObjectType-type}{%
@{typeof "ObjectType"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ObjectType-field-type}{%
@{typeof "ObjectType x"}
}%EndSnippet\<close>

syntax (latex output) "_Reserved" :: 'a ("Reserved")
translations "(CONST IsaField _Reserved)" \<leftharpoondown> "CONST Reserved"

text_raw \<open>
\DefineSnippet{Reserved-type}{%
@{typeof "Reserved"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Reserved-field-type}{%
@{typeof "Reserved x"}
}%EndSnippet\<close>

syntax (latex output) "_Mem" :: 'a ("Mem")
translations "(CONST IsaField _Mem)" \<leftharpoondown> "CONST Mem"

text_raw \<open>
\DefineSnippet{Mem-type}{%
@{typeof "Mem"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Mem-field-type}{%
@{typeof "Mem x"}
}%EndSnippet\<close>

syntax (latex output) "_Gpr" :: 'a ("Gpr")
translations "(CONST IsaField _Gpr)" \<leftharpoondown> "CONST Gpr"

text_raw \<open>
\DefineSnippet{Gpr-type}{%
@{typeof "Gpr"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{Gpr-field-type}{%
@{typeof "Gpr x"}
}%EndSnippet\<close>

syntax (latex output) "_LLbit" :: 'a ("LLbit")
translations "(CONST IsaField _LLbit)" \<leftharpoondown> "CONST LLbit"

text_raw \<open>
\DefineSnippet{LLbit-type}{%
@{typeof "LLbit"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LLbit-field-type}{%
@{typeof "LLbit x"}
}%EndSnippet\<close>

syntax (latex output) "_KernelMode" :: 'a ("KernelMode")
translations "(CONST IsaField _KernelMode)" \<leftharpoondown> "CONST KernelMode"

text_raw \<open>
\DefineSnippet{KernelMode-type}{%
@{typeof "KernelMode"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{KernelMode-field-type}{%
@{typeof "KernelMode x"}
}%EndSnippet\<close>

syntax (latex output) "_AccessToCU0" :: 'a ("AccessToCU0")
translations "(CONST IsaField _AccessToCU0)" \<leftharpoondown> "CONST AccessToCU0"

text_raw \<open>
\DefineSnippet{AccessToCU0-type}{%
@{typeof "AccessToCU0"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AccessToCU0-field-type}{%
@{typeof "AccessToCU0 x"}
}%EndSnippet\<close>

syntax (latex output) "_BigEndian" :: 'a ("BigEndian")
translations "(CONST IsaField _BigEndian)" \<leftharpoondown> "CONST BigEndian"

text_raw \<open>
\DefineSnippet{BigEndian-type}{%
@{typeof "BigEndian"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{BigEndian-field-type}{%
@{typeof "BigEndian x"}
}%EndSnippet\<close>

syntax (latex output) "_ReverseEndian" :: 'a ("ReverseEndian")
translations "(CONST IsaField _ReverseEndian)" \<leftharpoondown> "CONST ReverseEndian"

text_raw \<open>
\DefineSnippet{ReverseEndian-type}{%
@{typeof "ReverseEndian"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReverseEndian-field-type}{%
@{typeof "ReverseEndian x"}
}%EndSnippet\<close>

syntax (latex output) "_EXL" :: 'a ("EXL")
translations "(CONST IsaField _EXL)" \<leftharpoondown> "CONST EXL"

text_raw \<open>
\DefineSnippet{EXL-type}{%
@{typeof "EXL"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{EXL-field-type}{%
@{typeof "EXL x"}
}%EndSnippet\<close>

syntax (latex output) "_PC" :: 'a ("PC")
translations "(CONST IsaField _PC)" \<leftharpoondown> "CONST PC"

text_raw \<open>
\DefineSnippet{PC-type}{%
@{typeof "PC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PC-field-type}{%
@{typeof "PC x"}
}%EndSnippet\<close>

syntax (latex output) "_PCC" :: 'a ("PCC")
translations "(CONST IsaField _PCC)" \<leftharpoondown> "CONST PCC"

text_raw \<open>
\DefineSnippet{PCC-type}{%
@{typeof "PCC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PCC-field-type}{%
@{typeof "PCC x"}
}%EndSnippet\<close>

syntax (latex output) "_BranchDelay" :: 'a ("BranchDelay")
translations "(CONST IsaField _BranchDelay)" \<leftharpoondown> "CONST BranchDelay"

text_raw \<open>
\DefineSnippet{BranchDelay-type}{%
@{typeof "BranchDelay"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{BranchDelay-field-type}{%
@{typeof "BranchDelay x"}
}%EndSnippet\<close>

syntax (latex output) "_BranchTo" :: 'a ("BranchTo")
translations "(CONST IsaField _BranchTo)" \<leftharpoondown> "CONST BranchTo"

text_raw \<open>
\DefineSnippet{BranchTo-type}{%
@{typeof "BranchTo"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{BranchTo-field-type}{%
@{typeof "BranchTo x"}
}%EndSnippet\<close>

syntax (latex output) "_BranchDelayPCC" :: 'a ("BranchDelayPCC")
translations "(CONST IsaField _BranchDelayPCC)" \<leftharpoondown> "CONST BranchDelayPCC"

text_raw \<open>
\DefineSnippet{BranchDelayPCC-type}{%
@{typeof "BranchDelayPCC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{BranchDelayPCC-field-type}{%
@{typeof "BranchDelayPCC x"}
}%EndSnippet\<close>

syntax (latex output) "_BranchToPCC" :: 'a ("BranchToPCC")
translations "(CONST IsaField _BranchToPCC)" \<leftharpoondown> "CONST BranchToPCC"

text_raw \<open>
\DefineSnippet{BranchToPCC-type}{%
@{typeof "BranchToPCC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{BranchToPCC-field-type}{%
@{typeof "BranchToPCC x"}
}%EndSnippet\<close>

syntax (latex output) "_GeneralCapReg" :: 'a ("GeneralCapReg")
translations "(CONST IsaField _GeneralCapReg)" \<leftharpoondown> "CONST GeneralCapReg"

text_raw \<open>
\DefineSnippet{GeneralCapReg-type}{%
@{typeof "GeneralCapReg"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GeneralCapReg-field-type}{%
@{typeof "GeneralCapReg x"}
}%EndSnippet\<close>

syntax (latex output) "_SpecialCapReg" :: 'a ("SpecialCapReg")
translations "(CONST IsaField _SpecialCapReg)" \<leftharpoondown> "CONST SpecialCapReg"

text_raw \<open>
\DefineSnippet{SpecialCapReg-type}{%
@{typeof "SpecialCapReg"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SpecialCapReg-field-type}{%
@{typeof "SpecialCapReg x"}
}%EndSnippet\<close>

syntax (latex output) "_IsUnpredictable" :: 'a ("IsUnpredictable")
translations "(CONST IsaField _IsUnpredictable)" \<leftharpoondown> "CONST IsUnpredictable"

text_raw \<open>
\DefineSnippet{IsUnpredictable-type}{%
@{typeof "IsUnpredictable"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsUnpredictable-field-type}{%
@{typeof "IsUnpredictable x"}
}%EndSnippet\<close>

syntax (latex output) "_ExceptionSignalled" :: 'a ("ExceptionSignalled")
translations "(CONST IsaField _ExceptionSignalled)" \<leftharpoondown> "CONST ExceptionSignalled"

text_raw \<open>
\DefineSnippet{ExceptionSignalled-type}{%
@{typeof "ExceptionSignalled"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExceptionSignalled-field-type}{%
@{typeof "ExceptionSignalled x"}
}%EndSnippet\<close>

syntax (latex output) "_SystemRegisterAccess" :: 'a ("SystemRegisterAccess")
translations "(CONST IsaField _SystemRegisterAccess)" \<leftharpoondown> "CONST SystemRegisterAccess"

text_raw \<open>
\DefineSnippet{SystemRegisterAccess-type}{%
@{typeof "SystemRegisterAccess"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SystemRegisterAccess-field-type}{%
@{typeof "SystemRegisterAccess x"}
}%EndSnippet\<close>

syntax (latex output) "_ExecutableAddresses" :: 'a ("ExecutableAddresses")
translations "(CONST IsaField _ExecutableAddresses)" \<leftharpoondown> "CONST ExecutableAddresses"

text_raw \<open>
\DefineSnippet{ExecutableAddresses-type}{%
@{typeof "ExecutableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExecutableAddresses-field-type}{%
@{typeof "ExecutableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_LoadableAddresses" :: 'a ("LoadableAddresses")
translations "(CONST IsaField _LoadableAddresses)" \<leftharpoondown> "CONST LoadableAddresses"

text_raw \<open>
\DefineSnippet{LoadableAddresses-type}{%
@{typeof "LoadableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LoadableAddresses-field-type}{%
@{typeof "LoadableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_CapLoadableAddresses" :: 'a ("CapLoadableAddresses")
translations "(CONST IsaField _CapLoadableAddresses)" \<leftharpoondown> "CONST CapLoadableAddresses"

text_raw \<open>
\DefineSnippet{CapLoadableAddresses-type}{%
@{typeof "CapLoadableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapLoadableAddresses-field-type}{%
@{typeof "CapLoadableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_StorableAddresses" :: 'a ("StorableAddresses")
translations "(CONST IsaField _StorableAddresses)" \<leftharpoondown> "CONST StorableAddresses"

text_raw \<open>
\DefineSnippet{StorableAddresses-type}{%
@{typeof "StorableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StorableAddresses-field-type}{%
@{typeof "StorableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_CapStorableAddresses" :: 'a ("CapStorableAddresses")
translations "(CONST IsaField _CapStorableAddresses)" \<leftharpoondown> "CONST CapStorableAddresses"

text_raw \<open>
\DefineSnippet{CapStorableAddresses-type}{%
@{typeof "CapStorableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapStorableAddresses-field-type}{%
@{typeof "CapStorableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_LocalCapStorableAddresses" :: 'a ("LocalCapStorableAddresses")
translations "(CONST IsaField _LocalCapStorableAddresses)" \<leftharpoondown> "CONST LocalCapStorableAddresses"

text_raw \<open>
\DefineSnippet{LocalCapStorableAddresses-type}{%
@{typeof "LocalCapStorableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LocalCapStorableAddresses-field-type}{%
@{typeof "LocalCapStorableAddresses x"}
}%EndSnippet\<close>

syntax (latex output) "_SealableTypes" :: 'a ("SealableTypes")
translations "(CONST IsaField _SealableTypes)" \<leftharpoondown> "CONST SealableTypes"

text_raw \<open>
\DefineSnippet{SealableTypes-type}{%
@{typeof "SealableTypes"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SealableTypes-field-type}{%
@{typeof "SealableTypes x"}
}%EndSnippet\<close>

syntax (latex output) "_UnsealableTypes" :: 'a ("UnsealableTypes")
translations "(CONST IsaField _UnsealableTypes)" \<leftharpoondown> "CONST UnsealableTypes"

text_raw \<open>
\DefineSnippet{UnsealableTypes-type}{%
@{typeof "UnsealableTypes"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UnsealableTypes-field-type}{%
@{typeof "UnsealableTypes x"}
}%EndSnippet\<close>

syntax (latex output) "_Bit" :: 'a ("Bit")
translations "(CONST IsaDefinition _Bit)" \<leftharpoondown> "CONST Bit"

text_raw \<open>
\DefineSnippet{Bit-type}{%
@{typeof "Bit"}
}%EndSnippet\<close>

syntax (latex output) "_WordToInt" :: 'a ("WordToInt")
translations "(CONST IsaDefinition _WordToInt)" \<leftharpoondown> "CONST WordToInt"

text_raw \<open>
\DefineSnippet{WordToInt-type}{%
@{typeof "WordToInt"}
}%EndSnippet\<close>

syntax (latex output) "_WordToNat" :: 'a ("WordToNat")
translations "(CONST IsaDefinition _WordToNat)" \<leftharpoondown> "CONST WordToNat"

text_raw \<open>
\DefineSnippet{WordToNat-type}{%
@{typeof "WordToNat"}
}%EndSnippet\<close>

syntax (latex output) "_UCast" :: 'a ("UCast")
translations "(CONST IsaDefinition _UCast)" \<leftharpoondown> "CONST UCast"

text_raw \<open>
\DefineSnippet{UCast-type}{%
@{typeof "UCast"}
}%EndSnippet\<close>

syntax (latex output) "_SCast" :: 'a ("SCast")
translations "(CONST IsaDefinition _SCast)" \<leftharpoondown> "CONST SCast"

text_raw \<open>
\DefineSnippet{SCast-type}{%
@{typeof "SCast"}
}%EndSnippet\<close>

syntax (latex output) "_WordCat" :: 'a ("WordCat")
translations "(CONST IsaDefinition _WordCat)" \<leftharpoondown> "CONST WordCat"

text_raw \<open>
\DefineSnippet{WordCat-type}{%
@{typeof "WordCat"}
}%EndSnippet\<close>

syntax (latex output) "_Slice" :: 'a ("Slice")
translations "(CONST IsaDefinition _Slice)" \<leftharpoondown> "CONST Slice"

text_raw \<open>
\DefineSnippet{Slice-type}{%
@{typeof "Slice"}
}%EndSnippet\<close>

syntax (latex output) "_Mask" :: 'a ("Mask")
translations "(CONST IsaDefinition _Mask)" \<leftharpoondown> "CONST Mask"

text_raw \<open>
\DefineSnippet{Mask-type}{%
@{typeof "Mask"}
}%EndSnippet\<close>

syntax (latex output) "_ExtractByte" :: 'a ("ExtractByte")
translations "(CONST IsaDefinition _ExtractByte)" \<leftharpoondown> "CONST ExtractByte"

text_raw \<open>
\DefineSnippet{ExtractByte-type}{%
@{typeof "ExtractByte"}
}%EndSnippet\<close>

syntax (latex output) "_Size" :: 'a ("Size")
translations "(CONST IsaDefinition _Size)" \<leftharpoondown> "CONST Size"

text_raw \<open>
\DefineSnippet{Size-type}{%
@{typeof "Size"}
}%EndSnippet\<close>

syntax (latex output) "_MemSegment" :: 'a ("MemSegment")
translations "(CONST IsaDefinition _MemSegment)" \<leftharpoondown> "CONST MemSegment"

text_raw \<open>
\DefineSnippet{MemSegment-type}{%
@{typeof "MemSegment"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemSegment}{%
@{thm [display, margin = 50] MemSegment_alt}
}%EndSnippet\<close>

syntax (latex output) "_CapBounds" :: 'a ("CapBounds")
translations "(CONST IsaDefinition _CapBounds)" \<leftharpoondown> "CONST CapBounds"

text_raw \<open>
\DefineSnippet{CapBounds-type}{%
@{typeof "CapBounds"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapBounds}{%
@{thm [display, margin = 50] CapBounds_alt}
}%EndSnippet\<close>

syntax (latex output) "_BitsToCap" :: 'a ("BitsToCap")
translations "(CONST IsaDefinition _BitsToCap)" \<leftharpoondown> "CONST BitsToCap"

text_raw \<open>
\DefineSnippet{BitsToCap-type}{%
@{typeof "BitsToCap"}
}%EndSnippet\<close>

syntax (latex output) "_CapToBits" :: 'a ("CapToBits")
translations "(CONST IsaDefinition _CapToBits)" \<leftharpoondown> "CONST CapToBits"

text_raw \<open>
\DefineSnippet{CapToBits-type}{%
@{typeof "CapToBits"}
}%EndSnippet\<close>

syntax (latex output) "_PermitAccessSystemRegisters" :: 'a ("PermitAccessSystemRegisters")
translations "(CONST IsaDefinition _PermitAccessSystemRegisters)" \<leftharpoondown> "CONST PermitAccessSystemRegisters"

text_raw \<open>
\DefineSnippet{PermitAccessSystemRegisters-type}{%
@{typeof "PermitAccessSystemRegisters"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitAccessSystemRegisters}{%
@{thm [display, margin = 50] PermitAccessSystemRegisters_alt}
}%EndSnippet\<close>

syntax (latex output) "_IsInvokable" :: 'a ("IsInvokable")
translations "(CONST IsaDefinition _IsInvokable)" \<leftharpoondown> "CONST IsInvokable"

text_raw \<open>
\DefineSnippet{IsInvokable-type}{%
@{typeof "IsInvokable"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsInvokable}{%
@{thm [display, margin = 50] IsInvokable_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitExecute" :: 'a ("PermitExecute")
translations "(CONST IsaDefinition _PermitExecute)" \<leftharpoondown> "CONST PermitExecute"

text_raw \<open>
\DefineSnippet{PermitExecute-type}{%
@{typeof "PermitExecute"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitExecute}{%
@{thm [display, margin = 50] PermitExecute_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitLoad" :: 'a ("PermitLoad")
translations "(CONST IsaDefinition _PermitLoad)" \<leftharpoondown> "CONST PermitLoad"

text_raw \<open>
\DefineSnippet{PermitLoad-type}{%
@{typeof "PermitLoad"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitLoad}{%
@{thm [display, margin = 50] PermitLoad_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitLoadCapability" :: 'a ("PermitLoadCapability")
translations "(CONST IsaDefinition _PermitLoadCapability)" \<leftharpoondown> "CONST PermitLoadCapability"

text_raw \<open>
\DefineSnippet{PermitLoadCapability-type}{%
@{typeof "PermitLoadCapability"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitLoadCapability}{%
@{thm [display, margin = 50] PermitLoadCapability_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitSeal" :: 'a ("PermitSeal")
translations "(CONST IsaDefinition _PermitSeal)" \<leftharpoondown> "CONST PermitSeal"

text_raw \<open>
\DefineSnippet{PermitSeal-type}{%
@{typeof "PermitSeal"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitSeal}{%
@{thm [display, margin = 50] PermitSeal_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitUnseal" :: 'a ("PermitUnseal")
translations "(CONST IsaDefinition _PermitUnseal)" \<leftharpoondown> "CONST PermitUnseal"

text_raw \<open>
\DefineSnippet{PermitUnseal-type}{%
@{typeof "PermitUnseal"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitUnseal}{%
@{thm [display, margin = 50] PermitUnseal_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitStore" :: 'a ("PermitStore")
translations "(CONST IsaDefinition _PermitStore)" \<leftharpoondown> "CONST PermitStore"

text_raw \<open>
\DefineSnippet{PermitStore-type}{%
@{typeof "PermitStore"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitStore}{%
@{thm [display, margin = 50] PermitStore_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitStoreCapability" :: 'a ("PermitStoreCapability")
translations "(CONST IsaDefinition _PermitStoreCapability)" \<leftharpoondown> "CONST PermitStoreCapability"

text_raw \<open>
\DefineSnippet{PermitStoreCapability-type}{%
@{typeof "PermitStoreCapability"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitStoreCapability}{%
@{thm [display, margin = 50] PermitStoreCapability_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermitStoreLocalCapability" :: 'a ("PermitStoreLocalCapability")
translations "(CONST IsaDefinition _PermitStoreLocalCapability)" \<leftharpoondown> "CONST PermitStoreLocalCapability"

text_raw \<open>
\DefineSnippet{PermitStoreLocalCapability-type}{%
@{typeof "PermitStoreLocalCapability"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermitStoreLocalCapability}{%
@{thm [display, margin = 50] PermitStoreLocalCapability_alt}
}%EndSnippet\<close>

syntax (latex output) "_IsGlobal" :: 'a ("IsGlobal")
translations "(CONST IsaDefinition _IsGlobal)" \<leftharpoondown> "CONST IsGlobal"

text_raw \<open>
\DefineSnippet{IsGlobal-type}{%
@{typeof "IsGlobal"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsGlobal}{%
@{thm [display, margin = 50] IsGlobal_alt}
}%EndSnippet\<close>

syntax (latex output) "_TagOfDataType" :: 'a ("TagOfDataType")
translations "(CONST IsaDefinition _TagOfDataType)" \<leftharpoondown> "CONST TagOfDataType"

text_raw \<open>
\DefineSnippet{TagOfDataType-type}{%
@{typeof "TagOfDataType"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{TagOfDataType}{%
@{thm [display, margin = 50] TagOfDataType_def}
}%EndSnippet\<close>

syntax (latex output) "_MemData" :: 'a ("MemData")
translations "(CONST IsaDefinition _MemData)" \<leftharpoondown> "CONST MemData"

text_raw \<open>
\DefineSnippet{MemData-type}{%
@{typeof "MemData"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemData}{%
@{thm [display, margin = 50] MemData_alt}
}%EndSnippet\<close>

syntax (latex output) "_MemCap" :: 'a ("MemCap")
translations "(CONST IsaDefinition _MemCap)" \<leftharpoondown> "CONST MemCap"

text_raw \<open>
\DefineSnippet{MemCap-type}{%
@{typeof "MemCap"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemCap}{%
@{thm [display, margin = 50] MemCap_alt}
}%EndSnippet\<close>

syntax (latex output) "_MemTag" :: 'a ("MemTag")
translations "(CONST IsaDefinition _MemTag)" \<leftharpoondown> "CONST MemTag"

text_raw \<open>
\DefineSnippet{MemTag-type}{%
@{typeof "MemTag"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemTag}{%
@{thm [display, margin = 50] MemTag_alt}
}%EndSnippet\<close>

syntax (latex output) "_GPR" :: 'a ("GPR")
translations "(CONST IsaDefinition _GPR)" \<leftharpoondown> "CONST GPR"

text_raw \<open>
\DefineSnippet{GPR-type}{%
@{typeof "GPR"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPR}{%
@{thm [display, margin = 50] GPR_alt}
}%EndSnippet\<close>

syntax (latex output) "_KCC" :: 'a ("KCC")
translations "(CONST IsaDefinition _KCC)" \<leftharpoondown> "CONST KCC"

text_raw \<open>
\DefineSnippet{KCC-type}{%
@{typeof "KCC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{KCC}{%
@{thm [display, margin = 50] KCC_alt}
}%EndSnippet\<close>

syntax (latex output) "_EPCC" :: 'a ("EPCC")
translations "(CONST IsaDefinition _EPCC)" \<leftharpoondown> "CONST EPCC"

text_raw \<open>
\DefineSnippet{EPCC-type}{%
@{typeof "EPCC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{EPCC}{%
@{thm [display, margin = 50] EPCC_alt}
}%EndSnippet\<close>

syntax (latex output) "_IDC" :: 'a ("IDC")
translations "(CONST IsaDefinition _IDC)" \<leftharpoondown> "CONST IDC"

text_raw \<open>
\DefineSnippet{IDC-type}{%
@{typeof "IDC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IDC}{%
@{thm [display, margin = 50] IDC_alt}
}%EndSnippet\<close>

syntax (latex output) "_DDC" :: 'a ("DDC")
translations "(CONST IsaDefinition _DDC)" \<leftharpoondown> "CONST DDC"

text_raw \<open>
\DefineSnippet{DDC-type}{%
@{typeof "DDC"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{DDC}{%
@{thm [display, margin = 50] DDC_alt}
}%EndSnippet\<close>

syntax (latex output) "_CapReg" :: 'a ("CapReg")
translations "(CONST IsaDefinition _CapReg)" \<leftharpoondown> "CONST CapReg"

text_raw \<open>
\DefineSnippet{CapReg-type}{%
@{typeof "CapReg"}
}%EndSnippet\<close>

syntax (latex output) "_Cap" :: 'a ("Cap")
translations "(CONST IsaDefinition _Cap)" \<leftharpoondown> "CONST Cap"

text_raw \<open>
\DefineSnippet{Cap-type}{%
@{typeof "Cap"}
}%EndSnippet\<close>

syntax (latex output) "_GetCapAddress" :: 'a ("GetCapAddress")
translations "(CONST IsaDefinition _GetCapAddress)" \<leftharpoondown> "CONST GetCapAddress"

text_raw \<open>
\DefineSnippet{GetCapAddress-type}{%
@{typeof "GetCapAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GetCapAddress}{%
@{thm [display, margin = 50] GetCapAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_ExtendCapAddress" :: 'a ("ExtendCapAddress")
translations "(CONST IsaDefinition _ExtendCapAddress)" \<leftharpoondown> "CONST ExtendCapAddress"

text_raw \<open>
\DefineSnippet{ExtendCapAddress-type}{%
@{typeof "ExtendCapAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExtendCapAddress}{%
@{thm [display, margin = 50] ExtendCapAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_TranslateAddr" :: 'a ("TranslateAddr")
translations "(CONST IsaDefinition _TranslateAddr)" \<leftharpoondown> "CONST TranslateAddr"

text_raw \<open>
\DefineSnippet{TranslateAddr-type}{%
@{typeof "TranslateAddr"}
}%EndSnippet\<close>

syntax (latex output) "_TranslateBounds" :: 'a ("TranslateBounds")
translations "(CONST IsaDefinition _TranslateBounds)" \<leftharpoondown> "CONST TranslateBounds"

text_raw \<open>
\DefineSnippet{TranslateBounds-type}{%
@{typeof "TranslateBounds"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{TranslateBounds}{%
@{thm [display, margin = 50] TranslateBounds_alt}
}%EndSnippet\<close>

syntax (latex output) "_TranslateCapAddresses" :: 'a ("TranslateCapAddresses")
translations "(CONST IsaDefinition _TranslateCapAddresses)" \<leftharpoondown> "CONST TranslateCapAddresses"

text_raw \<open>
\DefineSnippet{TranslateCapAddresses-type}{%
@{typeof "TranslateCapAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{TranslateCapAddresses}{%
@{thm [display, margin = 50] TranslateCapAddresses_alt}
}%EndSnippet\<close>

syntax (latex output) "_ExceptionPCs" :: 'a ("ExceptionPCs")
translations "(CONST IsaDefinition _ExceptionPCs)" \<leftharpoondown> "CONST ExceptionPCs"

text_raw \<open>
\DefineSnippet{ExceptionPCs-type}{%
@{typeof "ExceptionPCs"}
}%EndSnippet\<close>

syntax (latex output) "_EmptyGhostState" :: 'a ("EmptyGhostState")
translations "(CONST IsaDefinition _EmptyGhostState)" \<leftharpoondown> "CONST EmptyGhostState"

text_raw \<open>
\DefineSnippet{EmptyGhostState-type}{%
@{typeof "EmptyGhostState"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{EmptyGhostState}{%
@{thm [display, margin = 50] EmptyGhostState_alt}
}%EndSnippet\<close>

syntax (latex output) "_StateIsValid" :: 'a ("StateIsValid")
translations "(CONST IsaDefinition _StateIsValid)" \<leftharpoondown> "CONST StateIsValid"

text_raw \<open>
\DefineSnippet{StateIsValid-type}{%
@{typeof "StateIsValid"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StateIsValid}{%
@{thm [display, margin = 50] StateIsValid_alt}
}%EndSnippet\<close>

syntax (latex output) "_CapDerivationTargets" :: 'a ("CapDerivationTargets")
translations "(CONST IsaDefinition _CapDerivationTargets)" \<leftharpoondown> "CONST CapDerivationTargets"

text_raw \<open>
\DefineSnippet{CapDerivationTargets-type}{%
@{typeof "CapDerivationTargets"}
}%EndSnippet\<close>

syntax (latex output) "_NextInstruction" :: 'a ("NextInstruction")
translations "(CONST IsaDefinition _NextInstruction)" \<leftharpoondown> "CONST NextInstruction"

text_raw \<open>
\DefineSnippet{NextInstruction-type}{%
@{typeof "NextInstruction"}
}%EndSnippet\<close>

syntax (latex output) "_UnpredictableNext" :: 'a ("UnpredictableNext")
translations "(CONST IsaDefinition _UnpredictableNext)" \<leftharpoondown> "CONST UnpredictableNext"

text_raw \<open>
\DefineSnippet{UnpredictableNext-type}{%
@{typeof "UnpredictableNext"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UnpredictableNext}{%
@{thm [display, margin = 50] UnpredictableNext_alt}
}%EndSnippet\<close>

syntax (latex output) "_LoadDataProp" :: 'a ("LoadDataProp")
translations "(CONST IsaDefinition _LoadDataProp)" \<leftharpoondown> "CONST LoadDataProp"

text_raw \<open>
\DefineSnippet{LoadDataProp-type}{%
@{typeof "LoadDataProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LoadDataProp}{%
@{thm [display, margin = 65] LoadDataProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_StoreDataProp" :: 'a ("StoreDataProp")
translations "(CONST IsaDefinition _StoreDataProp)" \<leftharpoondown> "CONST StoreDataProp"

text_raw \<open>
\DefineSnippet{StoreDataProp-type}{%
@{typeof "StoreDataProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreDataProp}{%
@{thm [display, margin = 60] StoreDataProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_ExecuteProp" :: 'a ("ExecuteProp")
translations "(CONST IsaDefinition _ExecuteProp)" \<leftharpoondown> "CONST ExecuteProp"

text_raw \<open>
\DefineSnippet{ExecuteProp-type}{%
@{typeof "ExecuteProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExecuteProp}{%
@{thm [display, margin = 50] ExecuteProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_LoadCapProp" :: 'a ("LoadCapProp")
translations "(CONST IsaDefinition _LoadCapProp)" \<leftharpoondown> "CONST LoadCapProp"

text_raw \<open>
\DefineSnippet{LoadCapProp-type}{%
@{typeof "LoadCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LoadCapProp}{%
@{thm [display, margin = 50] LoadCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_StoreCapProp" :: 'a ("StoreCapProp")
translations "(CONST IsaDefinition _StoreCapProp)" \<leftharpoondown> "CONST StoreCapProp"

text_raw \<open>
\DefineSnippet{StoreCapProp-type}{%
@{typeof "StoreCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreCapProp}{%
@{thm [display, margin = 55] StoreCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_StoreLocalCapProp" :: 'a ("StoreLocalCapProp")
translations "(CONST IsaDefinition _StoreLocalCapProp)" \<leftharpoondown> "CONST StoreLocalCapProp"

text_raw \<open>
\DefineSnippet{StoreLocalCapProp-type}{%
@{typeof "StoreLocalCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreLocalCapProp}{%
@{thm [display, margin = 50] StoreLocalCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_RestrictCapProp" :: 'a ("RestrictCapProp")
translations "(CONST IsaDefinition _RestrictCapProp)" \<leftharpoondown> "CONST RestrictCapProp"

text_raw \<open>
\DefineSnippet{RestrictCapProp-type}{%
@{typeof "RestrictCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{RestrictCapProp}{%
@{thm [display, margin = 50] RestrictCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_SealCapProp" :: 'a ("SealCapProp")
translations "(CONST IsaDefinition _SealCapProp)" \<leftharpoondown> "CONST SealCapProp"

text_raw \<open>
\DefineSnippet{SealCapProp-type}{%
@{typeof "SealCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SealCapProp}{%
@{thm [display, margin = 50] SealCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_UnsealCapProp" :: 'a ("UnsealCapProp")
translations "(CONST IsaDefinition _UnsealCapProp)" \<leftharpoondown> "CONST UnsealCapProp"

text_raw \<open>
\DefineSnippet{UnsealCapProp-type}{%
@{typeof "UnsealCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UnsealCapProp}{%
@{thm [display, margin = 50] UnsealCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_SystemRegisterProp" :: 'a ("SystemRegisterProp")
translations "(CONST IsaDefinition _SystemRegisterProp)" \<leftharpoondown> "CONST SystemRegisterProp"

text_raw \<open>
\DefineSnippet{SystemRegisterProp-type}{%
@{typeof "SystemRegisterProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SystemRegisterProp}{%
@{thm [display, margin = 50] SystemRegisterProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_InvokeCapProp" :: 'a ("InvokeCapProp")
translations "(CONST IsaDefinition _InvokeCapProp)" \<leftharpoondown> "CONST InvokeCapProp"

text_raw \<open>
\DefineSnippet{InvokeCapProp-type}{%
@{typeof "InvokeCapProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{InvokeCapProp}{%
@{thm [display, margin = 80] InvokeCapProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_ExceptionProp" :: 'a ("ExceptionProp")
translations "(CONST IsaDefinition _ExceptionProp)" \<leftharpoondown> "CONST ExceptionProp"

text_raw \<open>
\DefineSnippet{ExceptionProp-type}{%
@{typeof "ExceptionProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExceptionProp}{%
@{thm [display, margin = 50] ExceptionProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_MemoryInvariant" :: 'a ("MemoryInvariant")
translations "(CONST IsaDefinition _MemoryInvariant)" \<leftharpoondown> "CONST MemoryInvariant"

text_raw \<open>
\DefineSnippet{MemoryInvariant-type}{%
@{typeof "MemoryInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemoryInvariant}{%
@{thm [display, margin = 50] MemoryInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_CapabilityInvariant" :: 'a ("CapabilityInvariant")
translations "(CONST IsaDefinition _CapabilityInvariant)" \<leftharpoondown> "CONST CapabilityInvariant"

text_raw \<open>
\DefineSnippet{CapabilityInvariant-type}{%
@{typeof "CapabilityInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapabilityInvariant}{%
@{thm [display, margin = 50] CapabilityInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_ValidStateProp" :: 'a ("ValidStateProp")
translations "(CONST IsaDefinition _ValidStateProp)" \<leftharpoondown> "CONST ValidStateProp"

text_raw \<open>
\DefineSnippet{ValidStateProp-type}{%
@{typeof "ValidStateProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ValidStateProp}{%
@{thm [display, margin = 50] ValidStateProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_AddressTranslationProp" :: 'a ("AddressTranslationProp")
translations "(CONST IsaDefinition _AddressTranslationProp)" \<leftharpoondown> "CONST AddressTranslationProp"

text_raw \<open>
\DefineSnippet{AddressTranslationProp-type}{%
@{typeof "AddressTranslationProp"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AddressTranslationProp}{%
@{thm [display, margin = 50] AddressTranslationProp_alt}
}%EndSnippet\<close>

syntax (latex output) "_CheriAbstraction" :: 'a ("CheriAbstraction")
translations "(CONST IsaDefinition _CheriAbstraction)" \<leftharpoondown> "CONST CheriAbstraction"

text_raw \<open>
\DefineSnippet{CheriAbstraction-type}{%
@{typeof "CheriAbstraction"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CheriAbstraction}{%
@{thm [display, margin = 50] CheriAbstraction_alt}
}%EndSnippet\<close>

syntax (latex output) "_CAndPermActions" :: 'a ("CAndPermActions")
translations "(CONST IsaDefinition _CAndPermActions)" \<leftharpoondown> "CONST CAndPermActions"

text_raw \<open>
\DefineSnippet{CAndPermActions-type}{%
@{typeof "CAndPermActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CAndPermActions}{%
@{thm [display, margin = 50] CAndPermActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CBuildCapActions" :: 'a ("CBuildCapActions")
translations "(CONST IsaDefinition _CBuildCapActions)" \<leftharpoondown> "CONST CBuildCapActions"

text_raw \<open>
\DefineSnippet{CBuildCapActions-type}{%
@{typeof "CBuildCapActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CBuildCapActions}{%
@{thm [display, margin = 50] CBuildCapActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CClearHiActions" :: 'a ("CClearHiActions")
translations "(CONST IsaDefinition _CClearHiActions)" \<leftharpoondown> "CONST CClearHiActions"

text_raw \<open>
\DefineSnippet{CClearHiActions-type}{%
@{typeof "CClearHiActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CClearHiActions}{%
@{thm [display, margin = 50] CClearHiActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CClearLoActions" :: 'a ("CClearLoActions")
translations "(CONST IsaDefinition _CClearLoActions)" \<leftharpoondown> "CONST CClearLoActions"

text_raw \<open>
\DefineSnippet{CClearLoActions-type}{%
@{typeof "CClearLoActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CClearLoActions}{%
@{thm [display, margin = 50] CClearLoActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CClearTagActions" :: 'a ("CClearTagActions")
translations "(CONST IsaDefinition _CClearTagActions)" \<leftharpoondown> "CONST CClearTagActions"

text_raw \<open>
\DefineSnippet{CClearTagActions-type}{%
@{typeof "CClearTagActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CClearTagActions}{%
@{thm [display, margin = 50] CClearTagActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CCopyTypeActions" :: 'a ("CCopyTypeActions")
translations "(CONST IsaDefinition _CCopyTypeActions)" \<leftharpoondown> "CONST CCopyTypeActions"

text_raw \<open>
\DefineSnippet{CCopyTypeActions-type}{%
@{typeof "CCopyTypeActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CCopyTypeActions}{%
@{thm [display, margin = 50] CCopyTypeActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CFromPtrActions" :: 'a ("CFromPtrActions")
translations "(CONST IsaDefinition _CFromPtrActions)" \<leftharpoondown> "CONST CFromPtrActions"

text_raw \<open>
\DefineSnippet{CFromPtrActions-type}{%
@{typeof "CFromPtrActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CFromPtrActions}{%
@{thm [display, margin = 50] CFromPtrActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CGetPCCActions" :: 'a ("CGetPCCActions")
translations "(CONST IsaDefinition _CGetPCCActions)" \<leftharpoondown> "CONST CGetPCCActions"

text_raw \<open>
\DefineSnippet{CGetPCCActions-type}{%
@{typeof "CGetPCCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CGetPCCActions}{%
@{thm [display, margin = 50] CGetPCCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CGetPCCSetOffsetActions" :: 'a ("CGetPCCSetOffsetActions")
translations "(CONST IsaDefinition _CGetPCCSetOffsetActions)" \<leftharpoondown> "CONST CGetPCCSetOffsetActions"

text_raw \<open>
\DefineSnippet{CGetPCCSetOffsetActions-type}{%
@{typeof "CGetPCCSetOffsetActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CGetPCCSetOffsetActions}{%
@{thm [display, margin = 50] CGetPCCSetOffsetActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CIncOffsetActions" :: 'a ("CIncOffsetActions")
translations "(CONST IsaDefinition _CIncOffsetActions)" \<leftharpoondown> "CONST CIncOffsetActions"

text_raw \<open>
\DefineSnippet{CIncOffsetActions-type}{%
@{typeof "CIncOffsetActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CIncOffsetActions}{%
@{thm [display, margin = 50] CIncOffsetActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CIncOffsetImmediateActions" :: 'a ("CIncOffsetImmediateActions")
translations "(CONST IsaDefinition _CIncOffsetImmediateActions)" \<leftharpoondown> "CONST CIncOffsetImmediateActions"

text_raw \<open>
\DefineSnippet{CIncOffsetImmediateActions-type}{%
@{typeof "CIncOffsetImmediateActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CIncOffsetImmediateActions}{%
@{thm [display, margin = 50] CIncOffsetImmediateActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CJALRActions" :: 'a ("CJALRActions")
translations "(CONST IsaDefinition _CJALRActions)" \<leftharpoondown> "CONST CJALRActions"

text_raw \<open>
\DefineSnippet{CJALRActions-type}{%
@{typeof "CJALRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CJALRActions}{%
@{thm [display, margin = 45] CJALRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CJRActions" :: 'a ("CJRActions")
translations "(CONST IsaDefinition _CJRActions)" \<leftharpoondown> "CONST CJRActions"

text_raw \<open>
\DefineSnippet{CJRActions-type}{%
@{typeof "CJRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CJRActions}{%
@{thm [display, margin = 50] CJRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLCVirtualAddress" :: 'a ("CLCVirtualAddress")
translations "(CONST IsaDefinition _CLCVirtualAddress)" \<leftharpoondown> "CONST CLCVirtualAddress"

text_raw \<open>
\DefineSnippet{CLCVirtualAddress-type}{%
@{typeof "CLCVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLCVirtualAddress}{%
@{thm [display, margin = 50] CLCVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLCPhysicalAddress" :: 'a ("CLCPhysicalAddress")
translations "(CONST IsaDefinition _CLCPhysicalAddress)" \<leftharpoondown> "CONST CLCPhysicalAddress"

text_raw \<open>
\DefineSnippet{CLCPhysicalAddress-type}{%
@{typeof "CLCPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLCPhysicalAddress}{%
@{thm [display, margin = 50] CLCPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLCActions" :: 'a ("CLCActions")
translations "(CONST IsaDefinition _CLCActions)" \<leftharpoondown> "CONST CLCActions"

text_raw \<open>
\DefineSnippet{CLCActions-type}{%
@{typeof "CLCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLCActions}{%
@{thm [display, margin = 45] CLCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLCVirtualAddress" :: 'a ("CLLCVirtualAddress")
translations "(CONST IsaDefinition _CLLCVirtualAddress)" \<leftharpoondown> "CONST CLLCVirtualAddress"

text_raw \<open>
\DefineSnippet{CLLCVirtualAddress-type}{%
@{typeof "CLLCVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLCVirtualAddress}{%
@{thm [display, margin = 50] CLLCVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLCPhysicalAddress" :: 'a ("CLLCPhysicalAddress")
translations "(CONST IsaDefinition _CLLCPhysicalAddress)" \<leftharpoondown> "CONST CLLCPhysicalAddress"

text_raw \<open>
\DefineSnippet{CLLCPhysicalAddress-type}{%
@{typeof "CLLCPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLCPhysicalAddress}{%
@{thm [display, margin = 50] CLLCPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLCActions" :: 'a ("CLLCActions")
translations "(CONST IsaDefinition _CLLCActions)" \<leftharpoondown> "CONST CLLCActions"

text_raw \<open>
\DefineSnippet{CLLCActions-type}{%
@{typeof "CLLCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLCActions}{%
@{thm [display, margin = 45] CLLCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CMOVNActions" :: 'a ("CMOVNActions")
translations "(CONST IsaDefinition _CMOVNActions)" \<leftharpoondown> "CONST CMOVNActions"

text_raw \<open>
\DefineSnippet{CMOVNActions-type}{%
@{typeof "CMOVNActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CMOVNActions}{%
@{thm [display, margin = 50] CMOVNActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CMOVZActions" :: 'a ("CMOVZActions")
translations "(CONST IsaDefinition _CMOVZActions)" \<leftharpoondown> "CONST CMOVZActions"

text_raw \<open>
\DefineSnippet{CMOVZActions-type}{%
@{typeof "CMOVZActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CMOVZActions}{%
@{thm [display, margin = 50] CMOVZActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CReadHwrActions" :: 'a ("CReadHwrActions")
translations "(CONST IsaDefinition _CReadHwrActions)" \<leftharpoondown> "CONST CReadHwrActions"

text_raw \<open>
\DefineSnippet{CReadHwrActions-type}{%
@{typeof "CReadHwrActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CReadHwrActions}{%
@{thm [display, margin = 50] CReadHwrActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CMoveActions" :: 'a ("CMoveActions")
translations "(CONST IsaDefinition _CMoveActions)" \<leftharpoondown> "CONST CMoveActions"

text_raw \<open>
\DefineSnippet{CMoveActions-type}{%
@{typeof "CMoveActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CMoveActions}{%
@{thm [display, margin = 50] CMoveActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCVirtualAddress" :: 'a ("CSCVirtualAddress")
translations "(CONST IsaDefinition _CSCVirtualAddress)" \<leftharpoondown> "CONST CSCVirtualAddress"

text_raw \<open>
\DefineSnippet{CSCVirtualAddress-type}{%
@{typeof "CSCVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCVirtualAddress}{%
@{thm [display, margin = 50] CSCVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCPhysicalAddress" :: 'a ("CSCPhysicalAddress")
translations "(CONST IsaDefinition _CSCPhysicalAddress)" \<leftharpoondown> "CONST CSCPhysicalAddress"

text_raw \<open>
\DefineSnippet{CSCPhysicalAddress-type}{%
@{typeof "CSCPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCPhysicalAddress}{%
@{thm [display, margin = 50] CSCPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCActions" :: 'a ("CSCActions")
translations "(CONST IsaDefinition _CSCActions)" \<leftharpoondown> "CONST CSCActions"

text_raw \<open>
\DefineSnippet{CSCActions-type}{%
@{typeof "CSCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCActions}{%
@{thm [display, margin = 50] CSCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCCVirtualAddress" :: 'a ("CSCCVirtualAddress")
translations "(CONST IsaDefinition _CSCCVirtualAddress)" \<leftharpoondown> "CONST CSCCVirtualAddress"

text_raw \<open>
\DefineSnippet{CSCCVirtualAddress-type}{%
@{typeof "CSCCVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCCVirtualAddress}{%
@{thm [display, margin = 50] CSCCVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCCPhysicalAddress" :: 'a ("CSCCPhysicalAddress")
translations "(CONST IsaDefinition _CSCCPhysicalAddress)" \<leftharpoondown> "CONST CSCCPhysicalAddress"

text_raw \<open>
\DefineSnippet{CSCCPhysicalAddress-type}{%
@{typeof "CSCCPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCCPhysicalAddress}{%
@{thm [display, margin = 50] CSCCPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCCActions" :: 'a ("CSCCActions")
translations "(CONST IsaDefinition _CSCCActions)" \<leftharpoondown> "CONST CSCCActions"

text_raw \<open>
\DefineSnippet{CSCCActions-type}{%
@{typeof "CSCCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCCActions}{%
@{thm [display, margin = 50] CSCCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSealActions" :: 'a ("CSealActions")
translations "(CONST IsaDefinition _CSealActions)" \<leftharpoondown> "CONST CSealActions"

text_raw \<open>
\DefineSnippet{CSealActions-type}{%
@{typeof "CSealActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSealActions}{%
@{thm [display, margin = 50] CSealActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSetBoundsActions" :: 'a ("CSetBoundsActions")
translations "(CONST IsaDefinition _CSetBoundsActions)" \<leftharpoondown> "CONST CSetBoundsActions"

text_raw \<open>
\DefineSnippet{CSetBoundsActions-type}{%
@{typeof "CSetBoundsActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSetBoundsActions}{%
@{thm [display, margin = 55] CSetBoundsActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSetBoundsExactActions" :: 'a ("CSetBoundsExactActions")
translations "(CONST IsaDefinition _CSetBoundsExactActions)" \<leftharpoondown> "CONST CSetBoundsExactActions"

text_raw \<open>
\DefineSnippet{CSetBoundsExactActions-type}{%
@{typeof "CSetBoundsExactActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSetBoundsExactActions}{%
@{thm [display, margin = 50] CSetBoundsExactActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSetBoundsImmediateActions" :: 'a ("CSetBoundsImmediateActions")
translations "(CONST IsaDefinition _CSetBoundsImmediateActions)" \<leftharpoondown> "CONST CSetBoundsImmediateActions"

text_raw \<open>
\DefineSnippet{CSetBoundsImmediateActions-type}{%
@{typeof "CSetBoundsImmediateActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSetBoundsImmediateActions}{%
@{thm [display, margin = 50] CSetBoundsImmediateActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSetOffsetActions" :: 'a ("CSetOffsetActions")
translations "(CONST IsaDefinition _CSetOffsetActions)" \<leftharpoondown> "CONST CSetOffsetActions"

text_raw \<open>
\DefineSnippet{CSetOffsetActions-type}{%
@{typeof "CSetOffsetActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSetOffsetActions}{%
@{thm [display, margin = 50] CSetOffsetActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CUnsealActions" :: 'a ("CUnsealActions")
translations "(CONST IsaDefinition _CUnsealActions)" \<leftharpoondown> "CONST CUnsealActions"

text_raw \<open>
\DefineSnippet{CUnsealActions-type}{%
@{typeof "CUnsealActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CUnsealActions}{%
@{thm [display, margin = 50] CUnsealActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CWriteHwrActions" :: 'a ("CWriteHwrActions")
translations "(CONST IsaDefinition _CWriteHwrActions)" \<leftharpoondown> "CONST CWriteHwrActions"

text_raw \<open>
\DefineSnippet{CWriteHwrActions-type}{%
@{typeof "CWriteHwrActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CWriteHwrActions}{%
@{thm [display, margin = 50] CWriteHwrActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_ERETActions" :: 'a ("ERETActions")
translations "(CONST IsaDefinition _ERETActions)" \<leftharpoondown> "CONST ERETActions"

text_raw \<open>
\DefineSnippet{ERETActions-type}{%
@{typeof "ERETActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ERETActions}{%
@{thm [display, margin = 50] ERETActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyLoadVirtualAddress" :: 'a ("LegacyLoadVirtualAddress")
translations "(CONST IsaDefinition _LegacyLoadVirtualAddress)" \<leftharpoondown> "CONST LegacyLoadVirtualAddress"

text_raw \<open>
\DefineSnippet{LegacyLoadVirtualAddress-type}{%
@{typeof "LegacyLoadVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyLoadVirtualAddress}{%
@{thm [display, margin = 50] LegacyLoadVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyLoadPhysicalAddress" :: 'a ("LegacyLoadPhysicalAddress")
translations "(CONST IsaDefinition _LegacyLoadPhysicalAddress)" \<leftharpoondown> "CONST LegacyLoadPhysicalAddress"

text_raw \<open>
\DefineSnippet{LegacyLoadPhysicalAddress-type}{%
@{typeof "LegacyLoadPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyLoadPhysicalAddress}{%
@{thm [display, margin = 50] LegacyLoadPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyLoadActions" :: 'a ("LegacyLoadActions")
translations "(CONST IsaDefinition _LegacyLoadActions)" \<leftharpoondown> "CONST LegacyLoadActions"

text_raw \<open>
\DefineSnippet{LegacyLoadActions-type}{%
@{typeof "LegacyLoadActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyLoadActions}{%
@{thm [display, margin = 50] LegacyLoadActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LBActions" :: 'a ("LBActions")
translations "(CONST IsaDefinition _LBActions)" \<leftharpoondown> "CONST LBActions"

text_raw \<open>
\DefineSnippet{LBActions-type}{%
@{typeof "LBActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LBActions}{%
@{thm [display, margin = 50] LBActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LBUActions" :: 'a ("LBUActions")
translations "(CONST IsaDefinition _LBUActions)" \<leftharpoondown> "CONST LBUActions"

text_raw \<open>
\DefineSnippet{LBUActions-type}{%
@{typeof "LBUActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LBUActions}{%
@{thm [display, margin = 50] LBUActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LHActions" :: 'a ("LHActions")
translations "(CONST IsaDefinition _LHActions)" \<leftharpoondown> "CONST LHActions"

text_raw \<open>
\DefineSnippet{LHActions-type}{%
@{typeof "LHActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LHActions}{%
@{thm [display, margin = 50] LHActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LHUActions" :: 'a ("LHUActions")
translations "(CONST IsaDefinition _LHUActions)" \<leftharpoondown> "CONST LHUActions"

text_raw \<open>
\DefineSnippet{LHUActions-type}{%
@{typeof "LHUActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LHUActions}{%
@{thm [display, margin = 50] LHUActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LWActions" :: 'a ("LWActions")
translations "(CONST IsaDefinition _LWActions)" \<leftharpoondown> "CONST LWActions"

text_raw \<open>
\DefineSnippet{LWActions-type}{%
@{typeof "LWActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LWActions}{%
@{thm [display, margin = 50] LWActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LWUActions" :: 'a ("LWUActions")
translations "(CONST IsaDefinition _LWUActions)" \<leftharpoondown> "CONST LWUActions"

text_raw \<open>
\DefineSnippet{LWUActions-type}{%
@{typeof "LWUActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LWUActions}{%
@{thm [display, margin = 50] LWUActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LLActions" :: 'a ("LLActions")
translations "(CONST IsaDefinition _LLActions)" \<leftharpoondown> "CONST LLActions"

text_raw \<open>
\DefineSnippet{LLActions-type}{%
@{typeof "LLActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LLActions}{%
@{thm [display, margin = 50] LLActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LDActions" :: 'a ("LDActions")
translations "(CONST IsaDefinition _LDActions)" \<leftharpoondown> "CONST LDActions"

text_raw \<open>
\DefineSnippet{LDActions-type}{%
@{typeof "LDActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LDActions}{%
@{thm [display, margin = 50] LDActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LLDActions" :: 'a ("LLDActions")
translations "(CONST IsaDefinition _LLDActions)" \<leftharpoondown> "CONST LLDActions"

text_raw \<open>
\DefineSnippet{LLDActions-type}{%
@{typeof "LLDActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LLDActions}{%
@{thm [display, margin = 50] LLDActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LWLActions" :: 'a ("LWLActions")
translations "(CONST IsaDefinition _LWLActions)" \<leftharpoondown> "CONST LWLActions"

text_raw \<open>
\DefineSnippet{LWLActions-type}{%
@{typeof "LWLActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LWLActions}{%
@{thm [display, margin = 50] LWLActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LWRActions" :: 'a ("LWRActions")
translations "(CONST IsaDefinition _LWRActions)" \<leftharpoondown> "CONST LWRActions"

text_raw \<open>
\DefineSnippet{LWRActions-type}{%
@{typeof "LWRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LWRActions}{%
@{thm [display, margin = 50] LWRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LDLActions" :: 'a ("LDLActions")
translations "(CONST IsaDefinition _LDLActions)" \<leftharpoondown> "CONST LDLActions"

text_raw \<open>
\DefineSnippet{LDLActions-type}{%
@{typeof "LDLActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LDLActions}{%
@{thm [display, margin = 50] LDLActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LDRActions" :: 'a ("LDRActions")
translations "(CONST IsaDefinition _LDRActions)" \<leftharpoondown> "CONST LDRActions"

text_raw \<open>
\DefineSnippet{LDRActions-type}{%
@{typeof "LDRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LDRActions}{%
@{thm [display, margin = 50] LDRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLoadVirtualAddress" :: 'a ("CLoadVirtualAddress")
translations "(CONST IsaDefinition _CLoadVirtualAddress)" \<leftharpoondown> "CONST CLoadVirtualAddress"

text_raw \<open>
\DefineSnippet{CLoadVirtualAddress-type}{%
@{typeof "CLoadVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLoadVirtualAddress}{%
@{thm [display, margin = 50] CLoadVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLoadPhysicalAddress" :: 'a ("CLoadPhysicalAddress")
translations "(CONST IsaDefinition _CLoadPhysicalAddress)" \<leftharpoondown> "CONST CLoadPhysicalAddress"

text_raw \<open>
\DefineSnippet{CLoadPhysicalAddress-type}{%
@{typeof "CLoadPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLoadPhysicalAddress}{%
@{thm [display, margin = 50] CLoadPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLoadActions" :: 'a ("CLoadActions")
translations "(CONST IsaDefinition _CLoadActions)" \<leftharpoondown> "CONST CLoadActions"

text_raw \<open>
\DefineSnippet{CLoadActions-type}{%
@{typeof "CLoadActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLoadActions}{%
@{thm [display, margin = 50] CLoadActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLxVirtualAddress" :: 'a ("CLLxVirtualAddress")
translations "(CONST IsaDefinition _CLLxVirtualAddress)" \<leftharpoondown> "CONST CLLxVirtualAddress"

text_raw \<open>
\DefineSnippet{CLLxVirtualAddress-type}{%
@{typeof "CLLxVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLxVirtualAddress}{%
@{thm [display, margin = 50] CLLxVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLxPhysicalAddress" :: 'a ("CLLxPhysicalAddress")
translations "(CONST IsaDefinition _CLLxPhysicalAddress)" \<leftharpoondown> "CONST CLLxPhysicalAddress"

text_raw \<open>
\DefineSnippet{CLLxPhysicalAddress-type}{%
@{typeof "CLLxPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLxPhysicalAddress}{%
@{thm [display, margin = 50] CLLxPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CLLxActions" :: 'a ("CLLxActions")
translations "(CONST IsaDefinition _CLLxActions)" \<leftharpoondown> "CONST CLLxActions"

text_raw \<open>
\DefineSnippet{CLLxActions-type}{%
@{typeof "CLLxActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CLLxActions}{%
@{thm [display, margin = 50] CLLxActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyStoreVirtualAddress" :: 'a ("LegacyStoreVirtualAddress")
translations "(CONST IsaDefinition _LegacyStoreVirtualAddress)" \<leftharpoondown> "CONST LegacyStoreVirtualAddress"

text_raw \<open>
\DefineSnippet{LegacyStoreVirtualAddress-type}{%
@{typeof "LegacyStoreVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyStoreVirtualAddress}{%
@{thm [display, margin = 50] LegacyStoreVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyStorePhysicalAddress" :: 'a ("LegacyStorePhysicalAddress")
translations "(CONST IsaDefinition _LegacyStorePhysicalAddress)" \<leftharpoondown> "CONST LegacyStorePhysicalAddress"

text_raw \<open>
\DefineSnippet{LegacyStorePhysicalAddress-type}{%
@{typeof "LegacyStorePhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyStorePhysicalAddress}{%
@{thm [display, margin = 50] LegacyStorePhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_LegacyStoreActions" :: 'a ("LegacyStoreActions")
translations "(CONST IsaDefinition _LegacyStoreActions)" \<leftharpoondown> "CONST LegacyStoreActions"

text_raw \<open>
\DefineSnippet{LegacyStoreActions-type}{%
@{typeof "LegacyStoreActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LegacyStoreActions}{%
@{thm [display, margin = 50] LegacyStoreActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SBActions" :: 'a ("SBActions")
translations "(CONST IsaDefinition _SBActions)" \<leftharpoondown> "CONST SBActions"

text_raw \<open>
\DefineSnippet{SBActions-type}{%
@{typeof "SBActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SBActions}{%
@{thm [display, margin = 50] SBActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SHActions" :: 'a ("SHActions")
translations "(CONST IsaDefinition _SHActions)" \<leftharpoondown> "CONST SHActions"

text_raw \<open>
\DefineSnippet{SHActions-type}{%
@{typeof "SHActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SHActions}{%
@{thm [display, margin = 50] SHActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SWActions" :: 'a ("SWActions")
translations "(CONST IsaDefinition _SWActions)" \<leftharpoondown> "CONST SWActions"

text_raw \<open>
\DefineSnippet{SWActions-type}{%
@{typeof "SWActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SWActions}{%
@{thm [display, margin = 50] SWActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SDActions" :: 'a ("SDActions")
translations "(CONST IsaDefinition _SDActions)" \<leftharpoondown> "CONST SDActions"

text_raw \<open>
\DefineSnippet{SDActions-type}{%
@{typeof "SDActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SDActions}{%
@{thm [display, margin = 50] SDActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SCActions" :: 'a ("SCActions")
translations "(CONST IsaDefinition _SCActions)" \<leftharpoondown> "CONST SCActions"

text_raw \<open>
\DefineSnippet{SCActions-type}{%
@{typeof "SCActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SCActions}{%
@{thm [display, margin = 50] SCActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SCDActions" :: 'a ("SCDActions")
translations "(CONST IsaDefinition _SCDActions)" \<leftharpoondown> "CONST SCDActions"

text_raw \<open>
\DefineSnippet{SCDActions-type}{%
@{typeof "SCDActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SCDActions}{%
@{thm [display, margin = 50] SCDActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SWLActions" :: 'a ("SWLActions")
translations "(CONST IsaDefinition _SWLActions)" \<leftharpoondown> "CONST SWLActions"

text_raw \<open>
\DefineSnippet{SWLActions-type}{%
@{typeof "SWLActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SWLActions}{%
@{thm [display, margin = 50] SWLActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SWRActions" :: 'a ("SWRActions")
translations "(CONST IsaDefinition _SWRActions)" \<leftharpoondown> "CONST SWRActions"

text_raw \<open>
\DefineSnippet{SWRActions-type}{%
@{typeof "SWRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SWRActions}{%
@{thm [display, margin = 50] SWRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SDLActions" :: 'a ("SDLActions")
translations "(CONST IsaDefinition _SDLActions)" \<leftharpoondown> "CONST SDLActions"

text_raw \<open>
\DefineSnippet{SDLActions-type}{%
@{typeof "SDLActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SDLActions}{%
@{thm [display, margin = 50] SDLActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_SDRActions" :: 'a ("SDRActions")
translations "(CONST IsaDefinition _SDRActions)" \<leftharpoondown> "CONST SDRActions"

text_raw \<open>
\DefineSnippet{SDRActions-type}{%
@{typeof "SDRActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SDRActions}{%
@{thm [display, margin = 50] SDRActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CStoreVirtualAddress" :: 'a ("CStoreVirtualAddress")
translations "(CONST IsaDefinition _CStoreVirtualAddress)" \<leftharpoondown> "CONST CStoreVirtualAddress"

text_raw \<open>
\DefineSnippet{CStoreVirtualAddress-type}{%
@{typeof "CStoreVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CStoreVirtualAddress}{%
@{thm [display, margin = 50] CStoreVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CStorePhysicalAddress" :: 'a ("CStorePhysicalAddress")
translations "(CONST IsaDefinition _CStorePhysicalAddress)" \<leftharpoondown> "CONST CStorePhysicalAddress"

text_raw \<open>
\DefineSnippet{CStorePhysicalAddress-type}{%
@{typeof "CStorePhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CStorePhysicalAddress}{%
@{thm [display, margin = 50] CStorePhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CStoreActions" :: 'a ("CStoreActions")
translations "(CONST IsaDefinition _CStoreActions)" \<leftharpoondown> "CONST CStoreActions"

text_raw \<open>
\DefineSnippet{CStoreActions-type}{%
@{typeof "CStoreActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CStoreActions}{%
@{thm [display, margin = 50] CStoreActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCxVirtualAddress" :: 'a ("CSCxVirtualAddress")
translations "(CONST IsaDefinition _CSCxVirtualAddress)" \<leftharpoondown> "CONST CSCxVirtualAddress"

text_raw \<open>
\DefineSnippet{CSCxVirtualAddress-type}{%
@{typeof "CSCxVirtualAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCxVirtualAddress}{%
@{thm [display, margin = 50] CSCxVirtualAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCxPhysicalAddress" :: 'a ("CSCxPhysicalAddress")
translations "(CONST IsaDefinition _CSCxPhysicalAddress)" \<leftharpoondown> "CONST CSCxPhysicalAddress"

text_raw \<open>
\DefineSnippet{CSCxPhysicalAddress-type}{%
@{typeof "CSCxPhysicalAddress"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCxPhysicalAddress}{%
@{thm [display, margin = 50] CSCxPhysicalAddress_alt}
}%EndSnippet\<close>

syntax (latex output) "_CSCxActions" :: 'a ("CSCxActions")
translations "(CONST IsaDefinition _CSCxActions)" \<leftharpoondown> "CONST CSCxActions"

text_raw \<open>
\DefineSnippet{CSCxActions-type}{%
@{typeof "CSCxActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CSCxActions}{%
@{thm [display, margin = 50] CSCxActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_RunActions" :: 'a ("RunActions")
translations "(CONST IsaDefinition _RunActions)" \<leftharpoondown> "CONST RunActions"

text_raw \<open>
\DefineSnippet{RunActions-type}{%
@{typeof "RunActions"}
}%EndSnippet\<close>

syntax (latex output) "_TakeBranchActions" :: 'a ("TakeBranchActions")
translations "(CONST IsaDefinition _TakeBranchActions)" \<leftharpoondown> "CONST TakeBranchActions"

text_raw \<open>
\DefineSnippet{TakeBranchActions-type}{%
@{typeof "TakeBranchActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{TakeBranchActions}{%
@{thm [display, margin = 50] TakeBranchActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_DomainActions" :: 'a ("DomainActions")
translations "(CONST IsaDefinition _DomainActions)" \<leftharpoondown> "CONST DomainActions"

text_raw \<open>
\DefineSnippet{DomainActions-type}{%
@{typeof "DomainActions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{DomainActions}{%
@{thm [display, margin = 50] DomainActions_alt}
}%EndSnippet\<close>

syntax (latex output) "_Next" :: 'a ("Next")
translations "(CONST IsaDefinition _Next)" \<leftharpoondown> "CONST Next"

text_raw \<open>
\DefineSnippet{Next-type}{%
@{typeof "Next"}
}%EndSnippet\<close>

syntax (latex output) "_NextWithGhostState" :: 'a ("NextWithGhostState")
translations "(CONST IsaDefinition _NextWithGhostState)" \<leftharpoondown> "CONST NextWithGhostState"

text_raw \<open>
\DefineSnippet{NextWithGhostState-type}{%
@{typeof "NextWithGhostState"}
}%EndSnippet\<close>

syntax (latex output) "_SemanticsCheriMips" :: 'a ("SemanticsCheriMips")
translations "(CONST IsaDefinition _SemanticsCheriMips)" \<leftharpoondown> "CONST SemanticsCheriMips"

text_raw \<open>
\DefineSnippet{SemanticsCheriMips-type}{%
@{typeof "SemanticsCheriMips"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SemanticsCheriMips}{%
@{thm [display, margin = 60] SemanticsCheriMips_alt}
}%EndSnippet\<close>

syntax (latex output) "_BotGeneralisedPerm" :: 'a ("BotGeneralisedPerm")
translations "(CONST IsaDefinition _BotGeneralisedPerm)" \<leftharpoondown> "CONST BotGeneralisedPerm"

text_raw \<open>
\DefineSnippet{BotGeneralisedPerm-type}{%
@{typeof "BotGeneralisedPerm"}
}%EndSnippet\<close>

syntax (latex output) "_TopGeneralisedPerm" :: 'a ("TopGeneralisedPerm")
translations "(CONST IsaDefinition _TopGeneralisedPerm)" \<leftharpoondown> "CONST TopGeneralisedPerm"

text_raw \<open>
\DefineSnippet{TopGeneralisedPerm-type}{%
@{typeof "TopGeneralisedPerm"}
}%EndSnippet\<close>

syntax (latex output) "_RegisterIsAlwaysAccessible" :: 'a ("RegisterIsAlwaysAccessible")
translations "(CONST IsaDefinition _RegisterIsAlwaysAccessible)" \<leftharpoondown> "CONST RegisterIsAlwaysAccessible"

text_raw \<open>
\DefineSnippet{RegisterIsAlwaysAccessible-type}{%
@{typeof "RegisterIsAlwaysAccessible"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{RegisterIsAlwaysAccessible}{%
@{thm [display, margin = 50] RegisterIsAlwaysAccessible_alt}
}%EndSnippet\<close>

syntax (latex output) "_ReadableLocations" :: 'a ("ReadableLocations")
translations "(CONST IsaDefinition _ReadableLocations)" \<leftharpoondown> "CONST ReadableLocations"

text_raw \<open>
\DefineSnippet{ReadableLocations-type}{%
@{typeof "ReadableLocations"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReadableLocations}{%
@{thm [display, margin = 50] ReadableLocations_alt}
}%EndSnippet\<close>

syntax (latex output) "_StorablePhysAddresses" :: 'a ("StorablePhysAddresses")
translations "(CONST IsaDefinition _StorablePhysAddresses)" \<leftharpoondown> "CONST StorablePhysAddresses"

text_raw \<open>
\DefineSnippet{StorablePhysAddresses-type}{%
@{typeof "StorablePhysAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StorablePhysAddresses}{%
@{thm [display, margin = 50] StorablePhysAddresses_alt}
}%EndSnippet\<close>

syntax (latex output) "_StorablePhysCapAddresses" :: 'a ("StorablePhysCapAddresses")
translations "(CONST IsaDefinition _StorablePhysCapAddresses)" \<leftharpoondown> "CONST StorablePhysCapAddresses"

text_raw \<open>
\DefineSnippet{StorablePhysCapAddresses-type}{%
@{typeof "StorablePhysCapAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StorablePhysCapAddresses}{%
@{thm [display, margin = 50] StorablePhysCapAddresses_alt}
}%EndSnippet\<close>

syntax (latex output) "_GPermOfCap" :: 'a ("GPermOfCap")
translations "(CONST IsaDefinition _GPermOfCap)" \<leftharpoondown> "CONST GPermOfCap"

text_raw \<open>
\DefineSnippet{GPermOfCap-type}{%
@{typeof "GPermOfCap"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap}{%
@{thm [display, margin = 45] GPermOfCap_alt}
}%EndSnippet\<close>

syntax (latex output) "_GPermOfCaps" :: 'a ("GPermOfCaps")
translations "(CONST IsaDefinition _GPermOfCaps)" \<leftharpoondown> "CONST GPermOfCaps"

text_raw \<open>
\DefineSnippet{GPermOfCaps-type}{%
@{typeof "GPermOfCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCaps}{%
@{thm [display, margin = 50] GPermOfCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_ReachableCaps" :: 'a ("ReachableCaps")
translations "(CONST IsaDefinition _ReachableCaps)" \<leftharpoondown> "CONST ReachableCaps"

text_raw \<open>
\DefineSnippet{ReachableCaps-type}{%
@{typeof "ReachableCaps"}
}%EndSnippet\<close>

syntax (latex output) "_TransUsableCaps" :: 'a ("TransUsableCaps")
translations "(CONST IsaDefinition _TransUsableCaps)" \<leftharpoondown> "CONST TransUsableCaps"

text_raw \<open>
\DefineSnippet{TransUsableCaps-type}{%
@{typeof "TransUsableCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{TransUsableCaps}{%
@{thm [display, margin = 50] TransUsableCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_ReachablePermissions" :: 'a ("ReachablePermissions")
translations "(CONST IsaDefinition _ReachablePermissions)" \<leftharpoondown> "CONST ReachablePermissions"

text_raw \<open>
\DefineSnippet{ReachablePermissions-type}{%
@{typeof "ReachablePermissions"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachablePermissions}{%
@{thm [display, margin = 50] ReachablePermissions_alt}
}%EndSnippet\<close>

syntax (latex output) "_FutureStates" :: 'a ("FutureStates")
translations "(CONST IsaDefinition _FutureStates)" \<leftharpoondown> "CONST FutureStates"

text_raw \<open>
\DefineSnippet{FutureStates-type}{%
@{typeof "FutureStates"}
}%EndSnippet\<close>

syntax (latex output) "_KeepsDomain" :: 'a ("KeepsDomain")
translations "(CONST IsaDefinition _KeepsDomain)" \<leftharpoondown> "CONST KeepsDomain"

text_raw \<open>
\DefineSnippet{KeepsDomain-type}{%
@{typeof "KeepsDomain"}
}%EndSnippet\<close>

syntax (latex output) "_SwitchesDomain" :: 'a ("SwitchesDomain")
translations "(CONST IsaDefinition _SwitchesDomain)" \<leftharpoondown> "CONST SwitchesDomain"

text_raw \<open>
\DefineSnippet{SwitchesDomain-type}{%
@{typeof "SwitchesDomain"}
}%EndSnippet\<close>

syntax (latex output) "_IntraDomainTrace" :: 'a ("IntraDomainTrace")
translations "(CONST IsaDefinition _IntraDomainTrace)" \<leftharpoondown> "CONST IntraDomainTrace"

text_raw \<open>
\DefineSnippet{IntraDomainTrace-type}{%
@{typeof "IntraDomainTrace"}
}%EndSnippet\<close>

syntax (latex output) "_InterDomainTrace" :: 'a ("InterDomainTrace")
translations "(CONST IsaDefinition _InterDomainTrace)" \<leftharpoondown> "CONST InterDomainTrace"

text_raw \<open>
\DefineSnippet{InterDomainTrace-type}{%
@{typeof "InterDomainTrace"}
}%EndSnippet\<close>

syntax (latex output) "_MonotonicityReachableCaps" :: 'a ("MonotonicityReachableCaps")
translations "(CONST IsaDefinition _MonotonicityReachableCaps)" \<leftharpoondown> "CONST MonotonicityReachableCaps"

text_raw \<open>
\DefineSnippet{MonotonicityReachableCaps-type}{%
@{typeof "MonotonicityReachableCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MonotonicityReachableCaps}{%
@{thm [display, margin = 50] MonotonicityReachableCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_SameDomainSystemRegInvariant" :: 'a ("SameDomainSystemRegInvariant")
translations "(CONST IsaDefinition _SameDomainSystemRegInvariant)" \<leftharpoondown> "CONST SameDomainSystemRegInvariant"

text_raw \<open>
\DefineSnippet{SameDomainSystemRegInvariant-type}{%
@{typeof "SameDomainSystemRegInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SameDomainSystemRegInvariant}{%
@{thm [display, margin = 50] SameDomainSystemRegInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_DomainCrossSystemRegInvariant" :: 'a ("DomainCrossSystemRegInvariant")
translations "(CONST IsaDefinition _DomainCrossSystemRegInvariant)" \<leftharpoondown> "CONST DomainCrossSystemRegInvariant"

text_raw \<open>
\DefineSnippet{DomainCrossSystemRegInvariant-type}{%
@{typeof "DomainCrossSystemRegInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{DomainCrossSystemRegInvariant}{%
@{thm [display, margin = 50] DomainCrossSystemRegInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_SameDomainMemCapInvariant" :: 'a ("SameDomainMemCapInvariant")
translations "(CONST IsaDefinition _SameDomainMemCapInvariant)" \<leftharpoondown> "CONST SameDomainMemCapInvariant"

text_raw \<open>
\DefineSnippet{SameDomainMemCapInvariant-type}{%
@{typeof "SameDomainMemCapInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SameDomainMemCapInvariant}{%
@{thm [display, margin = 50] SameDomainMemCapInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_DomainCrossMemCapInvariant" :: 'a ("DomainCrossMemCapInvariant")
translations "(CONST IsaDefinition _DomainCrossMemCapInvariant)" \<leftharpoondown> "CONST DomainCrossMemCapInvariant"

text_raw \<open>
\DefineSnippet{DomainCrossMemCapInvariant-type}{%
@{typeof "DomainCrossMemCapInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{DomainCrossMemCapInvariant}{%
@{thm [display, margin = 50] DomainCrossMemCapInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_SameDomainMemoryInvariant" :: 'a ("SameDomainMemoryInvariant")
translations "(CONST IsaDefinition _SameDomainMemoryInvariant)" \<leftharpoondown> "CONST SameDomainMemoryInvariant"

text_raw \<open>
\DefineSnippet{SameDomainMemoryInvariant-type}{%
@{typeof "SameDomainMemoryInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SameDomainMemoryInvariant}{%
@{thm [display, margin = 50] SameDomainMemoryInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_DomainCrossMemoryInvariant" :: 'a ("DomainCrossMemoryInvariant")
translations "(CONST IsaDefinition _DomainCrossMemoryInvariant)" \<leftharpoondown> "CONST DomainCrossMemoryInvariant"

text_raw \<open>
\DefineSnippet{DomainCrossMemoryInvariant-type}{%
@{typeof "DomainCrossMemoryInvariant"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{DomainCrossMemoryInvariant}{%
@{thm [display, margin = 50] DomainCrossMemoryInvariant_alt}
}%EndSnippet\<close>

syntax (latex output) "_PermIsClosed" :: 'a ("PermIsClosed")
translations "(CONST IsaDefinition _PermIsClosed)" \<leftharpoondown> "CONST PermIsClosed"

text_raw \<open>
\DefineSnippet{PermIsClosed-type}{%
@{typeof "PermIsClosed"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{PermIsClosed}{%
@{thm [display, margin = 50] PermIsClosed_alt}
}%EndSnippet\<close>

syntax (latex output) "_CapabilityAligned" :: 'a ("CapabilityAligned")
translations "(CONST IsaDefinition _CapabilityAligned)" \<leftharpoondown> "CONST CapabilityAligned"

text_raw \<open>
\DefineSnippet{CapabilityAligned-type}{%
@{typeof "CapabilityAligned"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapabilityAligned}{%
@{thm [display, margin = 50] CapabilityAligned_alt}
}%EndSnippet\<close>

syntax (latex output) "_AccessibleCaps" :: 'a ("AccessibleCaps")
translations "(CONST IsaDefinition _AccessibleCaps)" \<leftharpoondown> "CONST AccessibleCaps"

text_raw \<open>
\DefineSnippet{AccessibleCaps-type}{%
@{typeof "AccessibleCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AccessibleCaps}{%
@{thm [display, margin = 50] AccessibleCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_UsableCaps" :: 'a ("UsableCaps")
translations "(CONST IsaDefinition _UsableCaps)" \<leftharpoondown> "CONST UsableCaps"

text_raw \<open>
\DefineSnippet{UsableCaps-type}{%
@{typeof "UsableCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UsableCaps}{%
@{thm [display, margin = 50] UsableCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_InvokableCaps" :: 'a ("InvokableCaps")
translations "(CONST IsaDefinition _InvokableCaps)" \<leftharpoondown> "CONST InvokableCaps"

text_raw \<open>
\DefineSnippet{InvokableCaps-type}{%
@{typeof "InvokableCaps"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{InvokableCaps}{%
@{thm [display, margin = 50] InvokableCaps_alt}
}%EndSnippet\<close>

syntax (latex output) "_InvokableAddresses" :: 'a ("InvokableAddresses")
translations "(CONST IsaDefinition _InvokableAddresses)" \<leftharpoondown> "CONST InvokableAddresses"

text_raw \<open>
\DefineSnippet{InvokableAddresses-type}{%
@{typeof "InvokableAddresses"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{InvokableAddresses}{%
@{thm [display, margin = 50] InvokableAddresses_alt}
}%EndSnippet\<close>

syntax (latex output) "_NoSystemRegisterAccess" :: 'a ("NoSystemRegisterAccess")
translations "(CONST IsaDefinition _NoSystemRegisterAccess)" \<leftharpoondown> "CONST NoSystemRegisterAccess"

text_raw \<open>
\DefineSnippet{NoSystemRegisterAccess-type}{%
@{typeof "NoSystemRegisterAccess"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{NoSystemRegisterAccess}{%
@{thm [display, margin = 50] NoSystemRegisterAccess_alt}
}%EndSnippet\<close>

syntax (latex output) "_ContainedCapBounds" :: 'a ("ContainedCapBounds")
translations "(CONST IsaDefinition _ContainedCapBounds)" \<leftharpoondown> "CONST ContainedCapBounds"

text_raw \<open>
\DefineSnippet{ContainedCapBounds-type}{%
@{typeof "ContainedCapBounds"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ContainedCapBounds}{%
@{thm [display, margin = 50] ContainedCapBounds_alt}
}%EndSnippet\<close>

syntax (latex output) "_ContainedObjectTypes" :: 'a ("ContainedObjectTypes")
translations "(CONST IsaDefinition _ContainedObjectTypes)" \<leftharpoondown> "CONST ContainedObjectTypes"

text_raw \<open>
\DefineSnippet{ContainedObjectTypes-type}{%
@{typeof "ContainedObjectTypes"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ContainedObjectTypes}{%
@{thm [display, margin = 50] ContainedObjectTypes_alt}
}%EndSnippet\<close>

syntax (latex output) "_InvokableCapsNotUsable" :: 'a ("InvokableCapsNotUsable")
translations "(CONST IsaDefinition _InvokableCapsNotUsable)" \<leftharpoondown> "CONST InvokableCapsNotUsable"

text_raw \<open>
\DefineSnippet{InvokableCapsNotUsable-type}{%
@{typeof "InvokableCapsNotUsable"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{InvokableCapsNotUsable}{%
@{thm [display, margin = 50] InvokableCapsNotUsable_alt}
}%EndSnippet\<close>

syntax (latex output) "_IsolatedState" :: 'a ("IsolatedState")
translations "(CONST IsaDefinition _IsolatedState)" \<leftharpoondown> "CONST IsolatedState"

text_raw \<open>
\DefineSnippet{IsolatedState-type}{%
@{typeof "IsolatedState"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsolatedState}{%
@{thm [display, margin = 60] IsolatedState_alt}
}%EndSnippet\<close>

syntax (latex output) "_IsolationGuarantees" :: 'a ("IsolationGuarantees")
translations "(CONST IsaDefinition _IsolationGuarantees)" \<leftharpoondown> "CONST IsolationGuarantees"

text_raw \<open>
\DefineSnippet{IsolationGuarantees-type}{%
@{typeof "IsolationGuarantees"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IsolationGuarantees}{%
@{thm [display, margin = 70] IsolationGuarantees_alt}
}%EndSnippet\<close>

syntax (latex output) "_CompartmentIsolation" :: 'a ("CompartmentIsolation")
translations "(CONST IsaDefinition _CompartmentIsolation)" \<leftharpoondown> "CONST CompartmentIsolation"

text_raw \<open>
\DefineSnippet{CompartmentIsolation-type}{%
@{typeof "CompartmentIsolation"}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CompartmentIsolation}{%
@{thm [display, margin = 60] CompartmentIsolation_alt}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapabilityOrder}{%
@{thm [display, margin = 50] CapabilityOrder}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LoadDataInstantiation}{%
@{thm [display, margin = 50] LoadDataInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreDataInstantiation}{%
@{thm [display, margin = 50] StoreDataInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExecuteInstantiation}{%
@{thm [display, margin = 50] ExecuteInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{LoadCapInstantiation}{%
@{thm [display, margin = 50] LoadCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreCapInstantiation}{%
@{thm [display, margin = 50] StoreCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{StoreLocalCapInstantiation}{%
@{thm [display, margin = 50] StoreLocalCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{RestrictCapInstantiation}{%
@{thm [display, margin = 50] RestrictCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SealCapInstantiation}{%
@{thm [display, margin = 50] SealCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{UnsealCapInstantiation}{%
@{thm [display, margin = 50] UnsealCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{SystemRegisterInstantiation}{%
@{thm [display, margin = 50] SystemRegisterInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{InvokeCapInstantiation}{%
@{thm [display, margin = 50] InvokeCapInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ExceptionInstantiation}{%
@{thm [display, margin = 50] ExceptionInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{MemoryInvariantInstantiation}{%
@{thm [display, margin = 50] MemoryInvariantInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CapabilityInvariantInstantiation}{%
@{thm [display, margin = 50] CapabilityInvariantInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ValidStateInstantiation}{%
@{thm [display, margin = 50] ValidStateInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AddressTranslationInstantiation}{%
@{thm [display, margin = 50] AddressTranslationInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{CheriInstantiation}{%
@{thm [display, margin = 50] CheriInstantiation}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-SystemRegisterAccess}{%
@{thm [display, margin = 50] GPermOfCap_SystemRegisterAccess}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-ExecutableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_ExecutableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-LoadableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_LoadableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-CapLoadableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_CapLoadableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-StorableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_StorableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-CapStorableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_CapStorableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-LocalCapStorableAddresses}{%
@{thm [display, margin = 50] GPermOfCap_LocalCapStorableAddresses}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-SealableTypes}{%
@{thm [display, margin = 50] GPermOfCap_SealableTypes}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-UnsealableTypes}{%
@{thm [display, margin = 50] GPermOfCap_UnsealableTypes}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{GPermOfCap-le}{%
@{thm [display, margin = 50] GPermOfCap_le}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachableCaps-Reg}{%
@{thm [display, margin = 50] ReachableCaps_Reg}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachableCaps-Memory}{%
@{thm [display, margin = 40] ReachableCaps_Memory}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachableCaps-Restrict}{%
@{thm [display, margin = 50] ReachableCaps_Restrict}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachableCaps-Seal}{%
@{thm [display, margin = 50] ReachableCaps_Seal}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{ReachableCaps-Unseal}{%
@{thm [display, margin = 50] ReachableCaps_Unseal}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IntraDomainTrace-Nil}{%
@{thm [display, margin = 50] IntraDomainTrace_Nil}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{IntraDomainTrace-Cons}{%
@{thm [display, margin = 50] IntraDomainTrace_Cons}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{FutureStates-Nil}{%
@{thm [display, margin = 50] FutureStates_Nil}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{FutureStates-Cons}{%
@{thm [display, margin = 50] FutureStates_Cons}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesMonotonicityReachableCaps}{%
@{thm [display, margin = 50] AbstractionImpliesMonotonicityReachableCaps}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesSameDomainSystemRegInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesSameDomainSystemRegInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesDomainCrossSystemRegInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesDomainCrossSystemRegInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesSameDomainMemCapInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesSameDomainMemCapInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesDomainCrossMemCapInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesDomainCrossMemCapInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesSameDomainMemoryInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesSameDomainMemoryInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesDomainCrossMemoryInvariant}{%
@{thm [display, margin = 50] AbstractionImpliesDomainCrossMemoryInvariant}
}%EndSnippet\<close>

text_raw \<open>
\DefineSnippet{AbstractionImpliesCompartmentIsolation}{%
@{thm [display, margin = 50] AbstractionImpliesCompartmentIsolation}
}%EndSnippet\<close>

(* Code generation - end snippets *)

(*<*)
end
(*>*)