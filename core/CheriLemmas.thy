(*<*)

(* Author: Kyndylan Nienhuis *)

theory CheriLemmas

imports 
  "CHERI-alt.CheriAltDefs"
  "CheriProofMethods"
begin

(*>*)
section \<open>Simplifications\<close>

subsection \<open>Sizes\<close>

declare CAPBYTEWIDTH_def [simp]
declare UPERMS_def [simp]
declare OTYPEWIDTH_def [simp]
  
type_synonym VirtualAddress = "64 word"
type_synonym PhysicalAddress = "40 word"
type_synonym PhysicalCapAddress = "35 word"
type_synonym RegisterAddress = "5 word"
type_synonym ObjectType = "24 word"

definition GetCapAddress :: "PhysicalAddress \<Rightarrow> PhysicalCapAddress" where
  "GetCapAddress a = slice 5 a"

definition ExtendCapAddress :: "PhysicalCapAddress \<Rightarrow> PhysicalAddress" where
  "ExtendCapAddress a = word_cat a (0::5 word)"

lemma GetCapAddress_ExtendCapAddress_simp [simp]:
  shows "GetCapAddress (ExtendCapAddress a) = a"
unfolding GetCapAddress_def ExtendCapAddress_def
by auto

lemma ExtendCapAddress_GetCapAddress_simp [simp]:
  shows "ExtendCapAddress (GetCapAddress a) = a AND NOT mask 5"
unfolding GetCapAddress_def ExtendCapAddress_def
by auto

subsection \<open>Permissions\<close>

lemma Perms_truncate_simp [simp]:
  fixes p :: Perms
  shows "Perms.truncate p = p"
unfolding Perms.truncate_def
by simp

lemma Perms_truncate_members [simp]:
  shows "Access_System_Registers (Perms.truncate p) = Access_System_Registers p"
    and "Global (Perms.truncate p) = Global p"
    and "Permit_CCall (Perms.truncate p) = Permit_CCall p"
    and "Permit_Execute (Perms.truncate p) = Permit_Execute p"
    and "Permit_Load (Perms.truncate p) = Permit_Load p"
    and "Permit_Load_Capability (Perms.truncate p) = Permit_Load_Capability p"
    and "Permit_Seal (Perms.truncate p) = Permit_Seal p"
    and "Permit_Unseal (Perms.truncate p) = Permit_Unseal p"
    and "Permit_Store (Perms.truncate p) = Permit_Store p"
    and "Permit_Store_Capability (Perms.truncate p) = Permit_Store_Capability p"
    and "Permit_Store_Local_Capability (Perms.truncate p) = Permit_Store_Local_Capability p"
    and "Permit_Set_CID (Perms.truncate p) = Permit_Set_CID p"
    and "Reserved (Perms.truncate p) = Reserved p"
unfolding Perms.truncate_def
by simp_all

lemma nth_reg'Perms:
  shows "reg'Perms p !! n = 
         (if n = 0 then Global p 
          else if n = 1 then Permit_Execute p
          else if n = 2 then Permit_Load p
          else if n = 3 then Permit_Store p
          else if n = 4 then Permit_Load_Capability p
          else if n = 5 then Permit_Store_Capability p
          else if n = 6 then Permit_Store_Local_Capability p
          else if n = 7 then Permit_Seal p
          else if n = 8 then Permit_CCall p
          else if n = 9 then Permit_Unseal p
          else if n = 10 then Access_System_Registers p
          else if n = 11 then Permit_Set_CID p
          else if n \<ge> 12 \<and> n \<le> 31 then Reserved p !! (n - 12)
          else False)"
proof -  
  have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or>
        n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8 \<or> n = 9 \<or>
        n = 10 \<or> n = 11 \<or> (n \<ge> 12 \<and> n \<le> 31) \<or> n > 31"
    by arith
  thus ?thesis
    unfolding reg'Perms_def Let_def
    apply (simp split del: if_splits(1)
                add: test_bit_cat 
                     nth_word_extract
                     nth_ucast
                     word_size
                cong del: weak_cong 
                cong: cong)
    apply (elim disjE)    
    by auto
qed

lemma nth_reg'Perms_concrete [simp]:
  shows "reg'Perms p !! 0 = Global p"
    and "reg'Perms p !! Suc 0 = Permit_Execute p"
    and "reg'Perms p !! 2 = Permit_Load p"
    and "reg'Perms p !! 3 = Permit_Store p"
    and "reg'Perms p !! 4 = Permit_Load_Capability p"
    and "reg'Perms p !! 5 = Permit_Store_Capability p"
    and "reg'Perms p !! 6 = Permit_Store_Local_Capability p"
    and "reg'Perms p !! 7 = Permit_Seal p"
    and "reg'Perms p !! 8 = Permit_CCall p"
    and "reg'Perms p !! 9 = Permit_Unseal p"
    and "reg'Perms p !! 10 = Access_System_Registers p"
    and "reg'Perms p !! 11 = Permit_Set_CID p"
unfolding nth_reg'Perms
by simp_all

lemma reg'Perms_rec'Perms_inv [simp]:
  shows "reg'Perms (rec'Perms w) = w"
unfolding rec'Perms_def Perms.make_def
apply (intro word_eqI)
apply (simp add: nth_reg'Perms)
apply (simp add: word_size)
apply (simp add: nth_word_extract)
apply auto
by arith

(* thm word_cat_bl
thm word_rep_drop
thm slice_take *)

lemma word_cat_slice_11_slice_8_reg'Perms:
  shows "(slice 12 (reg'Perms x)::20 word) = Reserved x"
        (is "?l = ?r")
by (intro word_eqI)
   (auto simp: word_size nth_word_cat nth_slice nth_reg'Perms)

lemma rec'Perms_reg'Perms_inv [simp]:
  shows "rec'Perms (reg'Perms x) = x"
unfolding rec'Perms_def Perms.make_def
by (simp add: nth_reg'Perms 
              ucast_shiftr
              word_cat_slice_11_slice_8_reg'Perms
              word_extract_def
              word_bits_def)

subsection \<open>User permissions\<close>

lemma UPerms_truncate_simp [simp]:
  fixes p :: UPerms
  shows "UPerms.truncate p = p"
unfolding UPerms.truncate_def
by simp

lemma UPerms_truncate_members [simp]:
  shows "soft (UPerms.truncate p) = soft p"
    and "UPerms.Reserved (UPerms.truncate p) = UPerms.Reserved p"
unfolding UPerms.truncate_def
by simp_all

lemma reg'UPerms_rec'UPerms_inv [simp]:
  shows "reg'UPerms (rec'UPerms w) = w"
unfolding rec'UPerms_def reg'UPerms_def UPerms.make_def 
by (intro word_eqI)
   (auto simp add: word_size nth_word_cat nth_word_extract nth_ucast)

lemma rec'UPerms_reg'UPerms_inv [simp]:
  shows "rec'UPerms (reg'UPerms x) = x"
proof (intro UPerms.equality)
  show "soft (rec'UPerms (reg'UPerms x)) = soft x"
    unfolding rec'UPerms_def reg'UPerms_def UPerms.make_def
    unfolding word_extract_def word_bits_def 
    by (simp add: ucast_shiftr)
next
  show "UPerms.Reserved (rec'UPerms (reg'UPerms x)) = UPerms.Reserved x"
    unfolding rec'UPerms_def reg'UPerms_def UPerms.make_def
    unfolding word_extract_def word_bits_def 
    by (intro word_eqI)
       (simp add: ucast_shiftr word_size nth_slice nth_word_cat)
qed simp

subsection \<open>Capabilities\<close>

lemma getBaseAndLength_alt [simp]:
  shows "getBaseAndLength cap = (getBase cap, getLength cap)"
unfolding getBaseAndLength_def getBase_def getLength_def ..

lemma Capability_truncate_simp [simp]:
  fixes cap :: Capability
  shows "Capability.truncate cap = cap"
unfolding Capability.truncate_def
by simp

lemma Capability_truncate_members [simp]:
  shows "base (Capability.truncate cap) = base cap"
    and "length (Capability.truncate cap) = length cap"
    and "cursor (Capability.truncate cap) = cursor cap"
    and "otype (Capability.truncate cap) = otype cap"
    and "perms (Capability.truncate cap) = perms cap"
    and "reserved (Capability.truncate cap) = reserved cap"
    and "sealed (Capability.truncate cap) = sealed cap"
    and "tag (Capability.truncate cap) = tag cap"
    and "uperms (Capability.truncate cap) = uperms cap"
unfolding Capability.truncate_def
by simp_all

lemma NullCap_members [simp]:
  shows "base nullCap = 0"
    and "length nullCap = max_word"
    and "cursor nullCap = 0"
    and "otype nullCap = 0"
    and "perms nullCap = 0"
    and "reserved nullCap = 0"
    and "sealed nullCap = False"
    and "tag nullCap = False"
    and "uperms nullCap = 0"
unfolding nullCap_def
by simp_all
  
lemma NullCap_simps [simp]:
  shows "getTag nullCap = False"
    and "getBase nullCap = 0"
    and "getLength nullCap = max_word"
    and "getSealed nullCap = False"
unfolding getTag_def
  getBase_def
  getLength_def
  getSealed_def
by simp_all

lemma DefaultCap_members [simp]:
  shows "base defaultCap = 0"
    and "length defaultCap = max_word"
    and "cursor defaultCap = 0"
    and "otype defaultCap = 0"
    and "perms defaultCap = max_word"
    and "reserved defaultCap = 0"
    and "sealed defaultCap = False"
    and "tag defaultCap = True"
    and "uperms defaultCap = max_word"
unfolding defaultCap_def
by simp_all
  
lemma DefaultCap_simps [simp]:
  shows "getTag defaultCap"
    and "getBase defaultCap = 0"
    and "getLength defaultCap = max_word"
    and "getSealed defaultCap = False"
unfolding defaultCap_def
  getTag_def
  getBase_def
  getLength_def
  getSealed_def
by simp_all

lemmas getTag_distrib [alt_def_simp] = 
  all_distrib[where h=getTag]

lemma capability_getter_setter [simp]:
  shows "getTag (setTag (cap, v0)) = v0"
    and "getTag (setSealed (cap, v1)) = getTag cap"
    and "getTag (setType (cap, v2)) = getTag cap"
    and "getTag (setOffset (cap, v3)) = getTag cap"
    and "getTag (setPerms (cap, v4)) = getTag cap"
    and "getTag (setUPerms (cap, v5)) = getTag cap"
    and "getTag (setBounds (cap, v6)) = getTag cap"
    and "getSealed (setTag (cap, v0)) = getSealed cap"
    and "getSealed (setSealed (cap, v1)) = v1"
    and "getSealed (setType (cap, v2)) = getSealed cap"
    and "getSealed (setOffset (cap, v3)) = getSealed cap"
    and "getSealed (setPerms (cap, v4)) = getSealed cap"
    and "getSealed (setUPerms (cap, v5)) = getSealed cap"
    and "getSealed (setBounds (cap, v6)) = getSealed cap"
    and "getType (setTag (cap, v0)) = getType cap"
    and "getType (setSealed (cap, v1)) = getType cap"
    and "getType (setType (cap, v2)) = v2"
    and "getType (setOffset (cap, v3)) = getType cap"
    and "getType (setPerms (cap, v4)) = getType cap"
    and "getType (setUPerms (cap, v5)) = getType cap"
    and "getType (setBounds (cap, v6)) = getType cap"
    and "getOffset (setTag (cap, v0)) = getOffset cap"
    and "getOffset (setSealed (cap, v1)) = getOffset cap"
    and "getOffset (setType (cap, v2)) = getOffset cap"
    and "getOffset (setOffset (cap, v3)) = v3"
    and "getOffset (setPerms (cap, v4)) = getOffset cap"
    and "getOffset (setUPerms (cap, v5)) = getOffset cap"
    and "getOffset (setBounds (cap, v6)) = 0"
    and "getPerms (setTag (cap, v0)) = getPerms cap"
    and "getPerms (setSealed (cap, v1)) = getPerms cap"
    and "getPerms (setType (cap, v2)) = getPerms cap"
    and "getPerms (setOffset (cap, v3)) = getPerms cap"
    and "getPerms (setUPerms (cap, v5)) = getPerms cap"
    and "getPerms (setBounds (cap, v6)) = getPerms cap"
    and "getUPerms (setTag (cap, v0)) = getUPerms cap"
    and "getUPerms (setSealed (cap, v1)) = getUPerms cap"
    and "getUPerms (setType (cap, v2)) = getUPerms cap"
    and "getUPerms (setOffset (cap, v3)) = getUPerms cap"
    and "getUPerms (setPerms (cap, v4)) = getUPerms cap"
    and "getUPerms (setBounds (cap, v6)) = getUPerms cap"
    and "getBase (setTag (cap, v0)) = getBase cap"
    and "getBase (setSealed (cap, v1)) = getBase cap"
    and "getBase (setType (cap, v2)) = getBase cap"
    and "getBase (setOffset (cap, v3)) = getBase cap"
    and "getBase (setPerms (cap, v4)) = getBase cap"
    and "getBase (setUPerms (cap, v5)) = getBase cap"
    and "getBase (setBounds (cap, v6)) = getBase cap + getOffset cap"
    and "getLength (setTag (cap, v0)) = getLength cap"
    and "getLength (setSealed (cap, v1)) = getLength cap"
    and "getLength (setType (cap, v2)) = getLength cap"
    and "getLength (setOffset (cap, v3)) = getLength cap"
    and "getLength (setPerms (cap, v4)) = getLength cap"
    and "getLength (setUPerms (cap, v5)) = getLength cap"
    and "getLength (setBounds (cap, v6)) = v6"
    and "reserved (setTag (cap, v0)) = reserved cap"
    and "reserved (setSealed (cap, v1)) = reserved cap"
    and "reserved (setType (cap, v2)) = reserved cap"
    and "reserved (setOffset (cap, v3)) = reserved cap"
    and "reserved (setPerms (cap, v4)) = reserved cap"
    and "reserved (setUPerms (cap, v5)) = reserved cap"
    and "reserved (setBounds (cap, v6)) = reserved cap"
unfolding 
  getTag_def 
  getSealed_def
  getType_def 
  getOffset_def 
  getPerms_def
  getUPerms_def
  getBase_def
  getLength_def
  setTag_def 
  setSealed_def 
  setType_def 
  setOffset_def 
  setPerms_def
  setUPerms_def
  setBounds_def
by simp_all

lemma capability_getPerms_setPerms [simp]:
  shows "getPerms (setPerms (cap, p1)) = rec'Perms (reg'Perms p1 AND mask 15)"
    and "getUPerms (setUPerms (cap, p2)) = rec'UPerms (reg'UPerms p2 AND mask 16)"
unfolding 
  getPerms_def
  getUPerms_def
  setPerms_def
  setUPerms_def
  word_extract_def
  word_bits_def
by simp_all

lemma capability_getPerms_AND_mask [simp]:
  shows "reg'Perms (getPerms cap) AND mask 15 = reg'Perms (getPerms cap)"
unfolding getPerms_def
using test_bit_size[where w="perms cap"]
by (intro word_eqI)
   (auto simp add: alt_def_simp word_size nth_ucast word_ao_nth)

lemma capability_getUPerms_AND_mask [simp]:
  shows "reg'UPerms (getUPerms cap) AND mask 16 = reg'UPerms (getUPerms cap)"
unfolding getUPerms_def
using test_bit_size[where w="uperms cap"]
by (intro word_eqI)
   (auto simp add: alt_def_simp word_size nth_ucast word_ao_nth)

lemma setTag_idem [simp]:
  shows "(setTag (cap, v) = cap) = (getTag cap = v)"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getTag]
  show ?r by auto
qed (simp add: setTag_def getTag_def)

lemma setTag_getTag [simp]:
  shows "setTag (cap, getTag cap) = cap"
by simp

lemma setSealed_idem [simp]:
  shows "(setSealed (cap, v) = cap) = (getSealed cap = v)"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getSealed]
  show ?r by auto
qed (simp add: setSealed_def getSealed_def)

lemma setSealed_getSealed [simp]:
  shows "setSealed (cap, getSealed cap) = cap"
by simp

lemma setType_idem [simp]:
  shows "(setType (cap, v) = cap) = (getType cap = v)"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getType]
  show ?r by auto
qed (simp add: setType_def getType_def)

lemma setType_getType [simp]:
  shows "setType (cap, getType cap) = cap"
by simp

lemma setOffset_idem [simp]:
  shows "(setOffset (cap, v) = cap) = (getOffset cap = v)"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getOffset]
  show ?r by auto
qed (auto simp add: setOffset_def getOffset_def)

lemma setOffset_getOffset [simp]:
  shows "setOffset (cap, getOffset cap) = cap"
by simp

lemma setPerms_idem [simp]:
  shows "(setPerms (cap, v) = cap) = (getPerms cap = rec'Perms (reg'Perms v AND mask 15))"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getPerms]
  show ?r by auto
next
  assume ?r
  from arg_cong[OF this, where f="\<lambda>x. ucast (reg'Perms x):: 15 word"]
  show ?l
    unfolding setPerms_def getPerms_def ucast_def[THEN sym]
    by auto
qed

lemma setPerms_getPerms [simp]:
  shows "setPerms (cap, getPerms cap) = cap"
by simp

lemma setUPerms_idem [simp]:
  shows "(setUPerms (cap, v) = cap) = (getUPerms cap = rec'UPerms (reg'UPerms v AND mask 16))"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getUPerms]
  show ?r by auto
next
  assume ?r
  from arg_cong[OF this, where f="\<lambda>x. ucast (reg'UPerms x):: 16 word"]
  show ?l
    unfolding setUPerms_def getUPerms_def ucast_def[THEN sym]
    by auto
qed

lemma setUPerms_getUPerms [simp]:
  shows "setUPerms (cap, getUPerms cap) = cap"
by simp

lemma setBounds_idem [simp]:
  shows "(setBounds (cap, v) = cap) = (getOffset cap = 0 \<and> getLength cap = v)"
  (is "?l = ?r")
proof
  assume ?l
  from arg_cong[OF this, where f=getOffset]
       arg_cong[OF this, where f=getLength]
  show ?r by auto
next
  assume ?r
  thus ?l
    unfolding setBounds_def getLength_def getOffset_def
    by auto
qed

subsection \<open>Capability-word conversion\<close>

lemma bitsToCaps_members:
  fixes x :: "256 word"
  defines "y \<equiv> x XOR word_cat (max_word::64 word) (0::192 word)"
  shows "tag (bitsToCap x) = False"
    and "length (bitsToCap x) = word_extract 255 192 y"
    and "base (bitsToCap x) = word_extract 191 128 y"
    and "cursor (bitsToCap x) = word_extract 127 64 y"
    and "reserved (bitsToCap x) = word_extract 63 56 y"
    and "otype (bitsToCap x) = word_extract 55 32 y"
    and "uperms (bitsToCap x) = word_extract 31 16 y"
    and "perms (bitsToCap x) = word_extract 15 1 y"
    and "sealed (bitsToCap x) = x !! 0"
unfolding bitsToCap_def
unfolding rec'Capability_def
unfolding Capability.make_def
unfolding reg'Capability_def
unfolding y_def
using test_bit_size[where w="_::256 word"]
by (auto simp: nth_ucast nth_word_cat 
               word_ops_nth_size word_size word_extract_ucast_up)

lemma tag_bitsToCap_simp [simp]:
  shows "getTag (bitsToCap x) = False"
unfolding getTag_def bitsToCaps_members
by simp

lemma capToBits_bitsToCap [simp]:
  shows "capToBits (bitsToCap x) = x"
proof -
  have "word_cat (word_extract 15 (Suc 0) x::15 word) b = 
        (word_extract 15 0 x::16 word)" 
  if "x !! 0 = b !! 0"
  for b :: "1 word" and x :: "256 word"
    using that
    by (intro word_eqI)
       (auto simp del: word_extract_start_zero
             simp: word_size nth_word_cat nth_word_extract)
  thus ?thesis
    unfolding capToBits_def
    unfolding reg'Capability_def
    by (auto simp add: word_bool_alg.xor_assoc
                          word_size word_ops_nth_size nth_word_cat
                          bitsToCaps_members
                          word_cat_word_extract_ucast)
qed

section \<open>Value and state part lemmas\<close>

lemma StatePart_read_onlyI:
  assumes "Commute m (read_state (\<lambda>s. s))"
  shows "StatePart m = (\<lambda>s. s)"
using assms
unfolding Commute_def
by auto

lemma StatePartSimpFromPrePost:
  fixes s :: state
  assumes "\<And>x. PrePost (read_state f' =\<^sub>b return x) m (\<lambda>_. read_state f =\<^sub>b return x)"
  shows "f (StatePart m s) = f' s"
using assms
unfolding PrePost_def
by (simp add: ValueAndStatePart_simp)

method SimpLemmaViaPrePost uses simp = 
  rule StatePartSimpFromPrePost,
  (PrePostNoExplosion simp: simp)

subsection \<open>Generated lemmas\<close>

(* Code generation - start - state and value parts *)

subsubsection \<open>@{const raise'exception}\<close>

text \<open>The term @{term "ValuePart (raise'exception v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setRaise'exception v \<equiv> StatePart (raise'exception v)"

subsubsection \<open>@{const PIC_update}\<close>

text \<open>The term @{term "ValuePart (PIC_update v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setPIC_update v \<equiv> StatePart (PIC_update v)"

subsubsection \<open>@{const PIC_initialise}\<close>

text \<open>The term @{term "ValuePart (PIC_initialise v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setPIC_initialise v \<equiv> StatePart (PIC_initialise v)"

subsubsection \<open>@{const PIC_load}\<close>

abbreviation "getPIC_load v \<equiv> ValuePart (PIC_load v)"

abbreviation "sideEffectsPIC_load v \<equiv> StatePart (PIC_load v)"

subsubsection \<open>@{const PIC_store}\<close>

text \<open>The term @{term "ValuePart (PIC_store v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setPIC_store v \<equiv> StatePart (PIC_store v)"

subsubsection \<open>@{const JTAG_UART_update_interrupt_bit}\<close>

text \<open>The term @{term "ValuePart (JTAG_UART_update_interrupt_bit v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setJTAG_UART_update_interrupt_bit v \<equiv> StatePart (JTAG_UART_update_interrupt_bit v)"

subsubsection \<open>@{const JTAG_UART_load}\<close>

text \<open>The term @{term "ValuePart JTAG_UART_load"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setJTAG_UART_load \<equiv> StatePart JTAG_UART_load"

subsubsection \<open>@{const JTAG_UART_input}\<close>

text \<open>The term @{term "ValuePart (JTAG_UART_input v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setJTAG_UART_input v \<equiv> StatePart (JTAG_UART_input v)"

subsubsection \<open>@{const JTAG_UART_store}\<close>

text \<open>The term @{term "ValuePart (JTAG_UART_store v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setJTAG_UART_store v \<equiv> StatePart (JTAG_UART_store v)"

subsubsection \<open>@{const JTAG_UART_output}\<close>

abbreviation "getJTAG_UART_output \<equiv> ValuePart JTAG_UART_output"

abbreviation "sideEffectsJTAG_UART_output \<equiv> StatePart JTAG_UART_output"

subsubsection \<open>@{const JTAG_UART_initialise}\<close>

text \<open>The term @{term "ValuePart (JTAG_UART_initialise v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setJTAG_UART_initialise v \<equiv> StatePart (JTAG_UART_initialise v)"

subsubsection \<open>@{const gpr}\<close>

abbreviation "getGpr v \<equiv> ValuePart (gpr v)"

lemma gpr_read_only [simp]:
  shows "StatePart (gpr v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_gpr) auto

subsubsection \<open>@{const write'gpr}\<close>

text \<open>The term @{term "ValuePart (write'gpr v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setGpr v \<equiv> StatePart (write'gpr v)"

lemma getGpr_setGpr_simp [simp]:
  shows "getGpr index' (setGpr x s) = (if index' = snd x then fst x else getGpr index' s)"
unfolding gpr_alt_def write'gpr_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const GPR}\<close>

abbreviation "getGPR v \<equiv> ValuePart (GPR v)"

lemma GPR_read_only [simp]:
  shows "StatePart (GPR v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_GPR) auto

(* Code generation - override - write'GPR *)

subsubsection \<open>@{const write'GPR}\<close>

text \<open>The term @{term "ValuePart (write'GPR v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setGPR v \<equiv> StatePart (write'GPR v)"

lemma getGPR_setGPR_simp [simp]:
  shows "getGPR index' (setGPR x s) = 
         (if index' = 0 then 0 
          else if index' = snd x then fst x 
          else getGPR index' s)"
unfolding GPR_alt_def write'GPR_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

(* Code generation - end override *)

subsubsection \<open>@{const UserMode}\<close>

abbreviation "getUserMode \<equiv> ValuePart UserMode"

lemma UserMode_read_only [simp]:
  shows "StatePart UserMode = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_UserMode) auto

subsubsection \<open>@{const SupervisorMode}\<close>

abbreviation "getSupervisorMode \<equiv> ValuePart SupervisorMode"

lemma SupervisorMode_read_only [simp]:
  shows "StatePart SupervisorMode = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_SupervisorMode) auto

subsubsection \<open>@{const KernelMode}\<close>

abbreviation "getKernelMode \<equiv> ValuePart KernelMode"

lemma KernelMode_read_only [simp]:
  shows "StatePart KernelMode = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_KernelMode) auto

subsubsection \<open>@{const BigEndianMem}\<close>

abbreviation "getBigEndianMem \<equiv> ValuePart BigEndianMem"

lemma BigEndianMem_read_only [simp]:
  shows "StatePart BigEndianMem = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_BigEndianMem) auto

subsubsection \<open>@{const ReverseEndian}\<close>

abbreviation "getReverseEndian \<equiv> ValuePart ReverseEndian"

lemma ReverseEndian_read_only [simp]:
  shows "StatePart ReverseEndian = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_ReverseEndian) auto

subsubsection \<open>@{const BigEndianCPU}\<close>

abbreviation "getBigEndianCPU \<equiv> ValuePart BigEndianCPU"

lemma BigEndianCPU_read_only [simp]:
  shows "StatePart BigEndianCPU = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_BigEndianCPU) auto

subsubsection \<open>@{const CheckBranch}\<close>

text \<open>The term @{term "ValuePart CheckBranch"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setCheckBranch \<equiv> StatePart CheckBranch"

subsubsection \<open>@{const BranchNotTaken}\<close>

text \<open>The term @{term "ValuePart BranchNotTaken"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setBranchNotTaken \<equiv> StatePart BranchNotTaken"

subsubsection \<open>@{const BranchLikelyNotTaken}\<close>

text \<open>The term @{term "ValuePart BranchLikelyNotTaken"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setBranchLikelyNotTaken \<equiv> StatePart BranchLikelyNotTaken"

subsubsection \<open>@{const initCoreStats}\<close>

text \<open>The term @{term "ValuePart initCoreStats"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setInitCoreStats \<equiv> StatePart initCoreStats"

subsubsection \<open>@{const printCoreStats}\<close>

abbreviation "getPrintCoreStats \<equiv> ValuePart printCoreStats"

lemma printCoreStats_read_only [simp]:
  shows "StatePart printCoreStats = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_printCoreStats) auto

subsubsection \<open>@{const next_unknown}\<close>

abbreviation "getNext_unknown v \<equiv> ValuePart (next_unknown v)"

abbreviation "sideEffectsNext_unknown v \<equiv> StatePart (next_unknown v)"

subsubsection \<open>@{const PCC}\<close>

abbreviation "getPCC \<equiv> ValuePart PCC"

lemma PCC_read_only [simp]:
  shows "StatePart PCC = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_PCC) auto

subsubsection \<open>@{const write'PCC}\<close>

text \<open>The term @{term "ValuePart (write'PCC v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setPCC v \<equiv> StatePart (write'PCC v)"

lemma getPCC_setPCC_simp [simp]:
  shows "getPCC (setPCC v s) = v"
unfolding PCC_alt_def write'PCC_alt_def
by (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const CAPR}\<close>

abbreviation "getCAPR v \<equiv> ValuePart (CAPR v)"

lemma CAPR_read_only [simp]:
  shows "StatePart (CAPR v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_CAPR) auto

(* Code generation - override - write'CAPR *)

subsubsection \<open>@{const write'CAPR}\<close>

text \<open>The term @{term "ValuePart (write'CAPR v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setCAPR v \<equiv> StatePart (write'CAPR v)"

lemma getCAPR_setCAPR_simp [simp]:
  shows "getCAPR index' (setCAPR x s) = 
         (if index' = 0 then nullCap 
          else if index' = snd x then fst x 
          else getCAPR index' s)"
unfolding CAPR_alt_def write'CAPR_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

(* Code generation - end override *)

subsubsection \<open>@{const SCAPR}\<close>

abbreviation "getSCAPR v \<equiv> ValuePart (SCAPR v)"

lemma SCAPR_read_only [simp]:
  shows "StatePart (SCAPR v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_SCAPR) auto

subsubsection \<open>@{const write'SCAPR}\<close>

text \<open>The term @{term "ValuePart (write'SCAPR v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSCAPR v \<equiv> StatePart (write'SCAPR v)"

lemma getSCAPR_setSCAPR_simp [simp]:
  shows "getSCAPR index' (setSCAPR x s) = (if index' = snd x then fst x else getSCAPR index' s)"
unfolding SCAPR_alt_def write'SCAPR_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

(* Code generation - suffix - RCC *)

abbreviation "getRCC \<equiv> getCAPR 17"

lemma "ValuePart RCC s = getRCC s"
unfolding RCC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'RCC *)

abbreviation "setRCC cap \<equiv> setCAPR (cap, 17)"

lemma "StatePart (write'RCC v) s = setRCC v s"
unfolding write'RCC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - IDC *)

abbreviation "getIDC \<equiv> getCAPR 26"

lemma "ValuePart IDC s = getIDC s"
unfolding IDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'IDC *)

abbreviation "setIDC cap \<equiv> setCAPR (cap, 26)"

lemma "StatePart (write'IDC v) s = setIDC v s"
unfolding write'IDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - DDC *)

abbreviation "getDDC \<equiv> getSCAPR 0"

lemma "ValuePart DDC s = getDDC s"
unfolding DDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'DDC *)

abbreviation "setDDC cap \<equiv> setSCAPR (cap, 0)"

lemma "StatePart (write'DDC v) s = setDDC v s"
unfolding write'DDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - TLSC *)

abbreviation "getTLSC \<equiv> getSCAPR 1"

lemma "ValuePart TLSC s = getTLSC s"
unfolding TLSC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'TLSC *)

abbreviation "setTLSC cap \<equiv> setSCAPR (cap, 1)"

lemma "StatePart (write'TLSC v) s = setTLSC v s"
unfolding write'TLSC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - PTLSC *)

abbreviation "getPTLSC \<equiv> getSCAPR 8"

lemma "ValuePart PTLSC s = getPTLSC s"
unfolding PTLSC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'PTLSC *)

abbreviation "setPTLSC cap \<equiv> setSCAPR (cap, 8)"

lemma "StatePart (write'PTLSC v) s = setPTLSC v s"
unfolding write'PTLSC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - KR1C *)

abbreviation "getKR1C \<equiv> getSCAPR 22"

lemma "ValuePart KR1C s = getKR1C s"
unfolding KR1C_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'KR1C *)

abbreviation "setKR1C cap \<equiv> setSCAPR (cap, 22)"

lemma "StatePart (write'KR1C v) s = setKR1C v s"
unfolding write'KR1C_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - KR2C *)

abbreviation "getKR2C \<equiv> getSCAPR 23"

lemma "ValuePart KR2C s = getKR2C s"
unfolding KR2C_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'KR2C *)

abbreviation "setKR2C cap \<equiv> setSCAPR (cap, 23)"

lemma "StatePart (write'KR2C v) s = setKR2C v s"
unfolding write'KR2C_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - KCC *)

abbreviation "getKCC \<equiv> getSCAPR 29"

lemma "ValuePart KCC s = getKCC s"
unfolding KCC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'KCC *)

abbreviation "setKCC cap \<equiv> setSCAPR (cap, 29)"

lemma "StatePart (write'KCC v) s = setKCC v s"
unfolding write'KCC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - KDC *)

abbreviation "getKDC \<equiv> getSCAPR 30"

lemma "ValuePart KDC s = getKDC s"
unfolding KDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'KDC *)

abbreviation "setKDC cap \<equiv> setSCAPR (cap, 30)"

lemma "StatePart (write'KDC v) s = setKDC v s"
unfolding write'KDC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - EPCC *)

abbreviation "getEPCC \<equiv> getSCAPR 31"

lemma "ValuePart EPCC s = getEPCC s"
unfolding EPCC_alt_def ..

(* Code generation - end suffix *)

(* Code generation - suffix - write'EPCC *)

abbreviation "setEPCC cap \<equiv> setSCAPR (cap, 31)"

lemma "StatePart (write'EPCC v) s = setEPCC v s"
unfolding write'EPCC_alt_def ..

(* Code generation - end suffix *)

subsubsection \<open>@{const SignalException}\<close>

text \<open>The term @{term "ValuePart (SignalException v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalException v \<equiv> StatePart (SignalException v)"

subsubsection \<open>@{const SignalCP2UnusableException}\<close>

text \<open>The term @{term "ValuePart SignalCP2UnusableException"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalCP2UnusableException \<equiv> StatePart SignalCP2UnusableException"

subsubsection \<open>@{const SignalCapException_internal}\<close>

text \<open>The term @{term "ValuePart (SignalCapException_internal v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalCapException_internal v \<equiv> StatePart (SignalCapException_internal v)"

subsubsection \<open>@{const SignalCapException}\<close>

text \<open>The term @{term "ValuePart (SignalCapException v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalCapException v \<equiv> StatePart (SignalCapException v)"

subsubsection \<open>@{const SignalCapException_noReg}\<close>

text \<open>The term @{term "ValuePart (SignalCapException_noReg v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalCapException_noReg v \<equiv> StatePart (SignalCapException_noReg v)"

subsubsection \<open>@{const TLB_direct}\<close>

abbreviation "getTLB_direct v \<equiv> ValuePart (TLB_direct v)"

lemma TLB_direct_read_only [simp]:
  shows "StatePart (TLB_direct v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_TLB_direct) auto

subsubsection \<open>@{const write'TLB_direct}\<close>

text \<open>The term @{term "ValuePart (write'TLB_direct v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setTLB_direct v \<equiv> StatePart (write'TLB_direct v)"

lemma getTLB_direct_setTLB_direct_simp [simp]:
  shows "getTLB_direct index' (setTLB_direct x s) = (if index' = snd x then fst x else getTLB_direct index' s)"
unfolding TLB_direct_alt_def write'TLB_direct_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const TLB_assoc}\<close>

abbreviation "getTLB_assoc v \<equiv> ValuePart (TLB_assoc v)"

lemma TLB_assoc_read_only [simp]:
  shows "StatePart (TLB_assoc v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_TLB_assoc) auto

subsubsection \<open>@{const write'TLB_assoc}\<close>

text \<open>The term @{term "ValuePart (write'TLB_assoc v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setTLB_assoc v \<equiv> StatePart (write'TLB_assoc v)"

lemma getTLB_assoc_setTLB_assoc_simp [simp]:
  shows "getTLB_assoc index' (setTLB_assoc x s) = (if index' = snd x then fst x else getTLB_assoc index' s)"
unfolding TLB_assoc_alt_def write'TLB_assoc_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const LookupTLB}\<close>

abbreviation "getLookupTLB v \<equiv> ValuePart (LookupTLB v)"

lemma LookupTLB_read_only [simp]:
  shows "StatePart (LookupTLB v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_LookupTLB) auto

subsubsection \<open>@{const SignalTLBException_internal}\<close>

text \<open>The term @{term "ValuePart (SignalTLBException_internal v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalTLBException_internal v \<equiv> StatePart (SignalTLBException_internal v)"

subsubsection \<open>@{const SignalTLBException}\<close>

text \<open>The term @{term "ValuePart (SignalTLBException v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalTLBException v \<equiv> StatePart (SignalTLBException v)"

subsubsection \<open>@{const CheckSegment}\<close>

abbreviation "getCheckSegment v \<equiv> ValuePart (CheckSegment v)"

lemma CheckSegment_read_only [simp]:
  shows "StatePart (CheckSegment v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_CheckSegment) auto

subsubsection \<open>@{const check_cca}\<close>

text \<open>The term @{term "ValuePart (check_cca v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setCheck_cca v \<equiv> StatePart (check_cca v)"

subsubsection \<open>@{const TLB_next_random}\<close>

text \<open>The term @{term "ValuePart (TLB_next_random v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setTLB_next_random v \<equiv> StatePart (TLB_next_random v)"

subsubsection \<open>@{const AddressTranslation}\<close>

abbreviation "getAddressTranslation v \<equiv> ValuePart (AddressTranslation v)"

abbreviation "sideEffectsAddressTranslation v \<equiv> StatePart (AddressTranslation v)"

subsubsection \<open>@{const CP0TLBEntry}\<close>

abbreviation "getCP0TLBEntry v \<equiv> ValuePart (CP0TLBEntry v)"

lemma CP0TLBEntry_read_only [simp]:
  shows "StatePart (CP0TLBEntry v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_CP0TLBEntry) auto

subsubsection \<open>@{const SignalTLBCapException}\<close>

text \<open>The term @{term "ValuePart (SignalTLBCapException v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setSignalTLBCapException v \<equiv> StatePart (SignalTLBCapException v)"

subsubsection \<open>@{const printMemStats}\<close>

abbreviation "getPrintMemStats \<equiv> ValuePart printMemStats"

lemma printMemStats_read_only [simp]:
  shows "StatePart printMemStats = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_printMemStats) auto

subsubsection \<open>@{const initMemStats}\<close>

text \<open>The term @{term "ValuePart initMemStats"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setInitMemStats \<equiv> StatePart initMemStats"

subsubsection \<open>@{const stats_data_reads_updt}\<close>

text \<open>The term @{term "ValuePart (stats_data_reads_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_data_reads_updt v \<equiv> StatePart (stats_data_reads_updt v)"

subsubsection \<open>@{const stats_data_writes_updt}\<close>

text \<open>The term @{term "ValuePart (stats_data_writes_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_data_writes_updt v \<equiv> StatePart (stats_data_writes_updt v)"

subsubsection \<open>@{const stats_inst_reads_updt}\<close>

text \<open>The term @{term "ValuePart (stats_inst_reads_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_inst_reads_updt v \<equiv> StatePart (stats_inst_reads_updt v)"

subsubsection \<open>@{const stats_valid_cap_reads_updt}\<close>

text \<open>The term @{term "ValuePart (stats_valid_cap_reads_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_valid_cap_reads_updt v \<equiv> StatePart (stats_valid_cap_reads_updt v)"

subsubsection \<open>@{const stats_valid_cap_writes_updt}\<close>

text \<open>The term @{term "ValuePart (stats_valid_cap_writes_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_valid_cap_writes_updt v \<equiv> StatePart (stats_valid_cap_writes_updt v)"

subsubsection \<open>@{const stats_invalid_cap_reads_updt}\<close>

text \<open>The term @{term "ValuePart (stats_invalid_cap_reads_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_invalid_cap_reads_updt v \<equiv> StatePart (stats_invalid_cap_reads_updt v)"

subsubsection \<open>@{const stats_invalid_cap_writes_updt}\<close>

text \<open>The term @{term "ValuePart (stats_invalid_cap_writes_updt v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setStats_invalid_cap_writes_updt v \<equiv> StatePart (stats_invalid_cap_writes_updt v)"

subsubsection \<open>@{const MEM}\<close>

abbreviation "getMEM v \<equiv> ValuePart (MEM v)"

lemma MEM_read_only [simp]:
  shows "StatePart (MEM v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_MEM) auto

subsubsection \<open>@{const write'MEM}\<close>

text \<open>The term @{term "ValuePart (write'MEM v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setMEM v \<equiv> StatePart (write'MEM v)"

lemma getMEM_setMEM_simp [simp]:
  shows "getMEM index' (setMEM x s) = (if index' = snd x then fst x else getMEM index' s)"
unfolding MEM_alt_def write'MEM_alt_def
by (cases x) (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const InitMEM}\<close>

text \<open>The term @{term "ValuePart InitMEM"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setInitMEM \<equiv> StatePart InitMEM"

subsubsection \<open>@{const ReadData}\<close>

abbreviation "getReadData v \<equiv> ValuePart (ReadData v)"

abbreviation "sideEffectsReadData v \<equiv> StatePart (ReadData v)"

subsubsection \<open>@{const WriteData}\<close>

text \<open>The term @{term "ValuePart (WriteData v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setWriteData v \<equiv> StatePart (WriteData v)"

subsubsection \<open>@{const ReadInst}\<close>

abbreviation "getReadInst v \<equiv> ValuePart (ReadInst v)"

abbreviation "sideEffectsReadInst v \<equiv> StatePart (ReadInst v)"

subsubsection \<open>@{const ReadCap}\<close>

abbreviation "getReadCap v \<equiv> ValuePart (ReadCap v)"

abbreviation "sideEffectsReadCap v \<equiv> StatePart (ReadCap v)"

subsubsection \<open>@{const WriteCap}\<close>

text \<open>The term @{term "ValuePart (WriteCap v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setWriteCap v \<equiv> StatePart (WriteCap v)"

subsubsection \<open>@{const AdjustEndian}\<close>

abbreviation "getAdjustEndian v \<equiv> ValuePart (AdjustEndian v)"

abbreviation "sideEffectsAdjustEndian v \<equiv> StatePart (AdjustEndian v)"

subsubsection \<open>@{const initMemAccessStats}\<close>

text \<open>The term @{term "ValuePart initMemAccessStats"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setInitMemAccessStats \<equiv> StatePart initMemAccessStats"

subsubsection \<open>@{const printMemAccessStats}\<close>

abbreviation "getPrintMemAccessStats \<equiv> ValuePart printMemAccessStats"

lemma printMemAccessStats_read_only [simp]:
  shows "StatePart printMemAccessStats = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_printMemAccessStats) auto

subsubsection \<open>@{const getVirtualAddress}\<close>

abbreviation "getGetVirtualAddress v \<equiv> ValuePart (getVirtualAddress v)"

lemma getVirtualAddress_read_only [simp]:
  shows "StatePart (getVirtualAddress v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_getVirtualAddress) auto

subsubsection \<open>@{const LoadMemoryCap}\<close>

abbreviation "getLoadMemoryCap v \<equiv> ValuePart (LoadMemoryCap v)"

abbreviation "sideEffectsLoadMemoryCap v \<equiv> StatePart (LoadMemoryCap v)"

subsubsection \<open>@{const LoadMemory}\<close>

abbreviation "getLoadMemory v \<equiv> ValuePart (LoadMemory v)"

abbreviation "sideEffectsLoadMemory v \<equiv> StatePart (LoadMemory v)"

subsubsection \<open>@{const LoadCap}\<close>

abbreviation "getLoadCap v \<equiv> ValuePart (LoadCap v)"

abbreviation "sideEffectsLoadCap v \<equiv> StatePart (LoadCap v)"

subsubsection \<open>@{const StoreMemoryCap}\<close>

abbreviation "getStoreMemoryCap v \<equiv> ValuePart (StoreMemoryCap v)"

abbreviation "sideEffectsStoreMemoryCap v \<equiv> StatePart (StoreMemoryCap v)"

subsubsection \<open>@{const StoreMemory}\<close>

abbreviation "getStoreMemory v \<equiv> ValuePart (StoreMemory v)"

abbreviation "sideEffectsStoreMemory v \<equiv> StatePart (StoreMemory v)"

subsubsection \<open>@{const StoreCap}\<close>

abbreviation "getStoreCap v \<equiv> ValuePart (StoreCap v)"

abbreviation "sideEffectsStoreCap v \<equiv> StatePart (StoreCap v)"

subsubsection \<open>@{const Fetch}\<close>

abbreviation "getFetch \<equiv> ValuePart Fetch"

abbreviation "sideEffectsFetch \<equiv> StatePart Fetch"

subsubsection \<open>@{const CP0R}\<close>

abbreviation "getCP0R v \<equiv> ValuePart (CP0R v)"

abbreviation "sideEffectsCP0R v \<equiv> StatePart (CP0R v)"

subsubsection \<open>@{const write'CP0R}\<close>

text \<open>The term @{term "ValuePart (write'CP0R v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setCP0R v \<equiv> StatePart (write'CP0R v)"

subsubsection \<open>@{const resetStats}\<close>

text \<open>The term @{term "ValuePart resetStats"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setResetStats \<equiv> StatePart resetStats"

subsubsection \<open>@{const HI}\<close>

abbreviation "getHI \<equiv> ValuePart HI"

abbreviation "sideEffectsHI \<equiv> StatePart HI"

subsubsection \<open>@{const write'HI}\<close>

text \<open>The term @{term "ValuePart (write'HI v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setHI v \<equiv> StatePart (write'HI v)"

lemma getHI_setHI_simp [simp]:
  shows "getHI (setHI v s) = v"
unfolding HI_alt_def write'HI_alt_def
by (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const LO}\<close>

abbreviation "getLO \<equiv> ValuePart LO"

abbreviation "sideEffectsLO \<equiv> StatePart LO"

subsubsection \<open>@{const write'LO}\<close>

text \<open>The term @{term "ValuePart (write'LO v)"} is simplified to @{term "\<lambda>_. ()"}.\<close>

abbreviation "setLO v \<equiv> StatePart (write'LO v)"

lemma getLO_setLO_simp [simp]:
  shows "getLO (setLO v s) = v"
unfolding LO_alt_def write'LO_alt_def
by (simp add: ValuePart_bind StatePart_bind)

subsubsection \<open>@{const special_register_accessible}\<close>

abbreviation "getSpecial_register_accessible v \<equiv> ValuePart (special_register_accessible v)"

lemma special_register_accessible_read_only [simp]:
  shows "StatePart (special_register_accessible v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_special_register_accessible) auto

subsubsection \<open>@{const log_instruction}\<close>

abbreviation "getLog_instruction v \<equiv> ValuePart (log_instruction v)"

lemma log_instruction_read_only [simp]:
  shows "StatePart (log_instruction v) = (\<lambda>s. s)"
by (intro StatePart_read_onlyI Commute_log_instruction) auto

(* Code generation - end *)

subsection \<open>Manual lemmas\<close>

subsubsection \<open>@{const getExceptionSignalled}\<close>

lemma getExceptionSignalled_simps [simp]:
  shows "getExceptionSignalled (BranchToPCC_update x_BranchToPCC s) = getExceptionSignalled s"
    and "getExceptionSignalled (BranchDelayPCC_update x_BranchDelayPCC s) = getExceptionSignalled s"
    and "getExceptionSignalled (the_MEM_update x_the_MEM s) = getExceptionSignalled s"
    and "getExceptionSignalled (setPCC x_PCC s) = getExceptionSignalled s"
    and "getExceptionSignalled (setCAPR x_CAPR s) = getExceptionSignalled s"
    and "getExceptionSignalled (setSCAPR x_SCAPR s) = getExceptionSignalled s"
    and "getExceptionSignalled (setMEM x_MEM s) = getExceptionSignalled s"
    and "getExceptionSignalled (setBranchTo x_BranchTo s) = getExceptionSignalled s"
    and "getExceptionSignalled (setBranchDelay x_BranchDelay s) = getExceptionSignalled s"
    and "getExceptionSignalled (exception_update x_exception s) = getExceptionSignalled s"
by (rule Commute_read_state_update_stateE, Commute)+

text \<open>The following two patterns regularly occur.\<close>

lemma if_exception_signalled_simp [simp]:
  shows "bind (read_state getExceptionSignalled)
              (\<lambda>ex. if ex then read_state getExceptionSignalled \<or>\<^sub>b m else m') = 
         bind (read_state getExceptionSignalled)
              (\<lambda>ex. if ex then return True else m')"
by (intro monad_eqI)
   (auto simp: ValueAndStatePart_simp)

lemma if_not_exception_signalled_simp [simp]:
  shows "bind (read_state getExceptionSignalled)
              (\<lambda>ex. if \<not> ex then m else read_state getExceptionSignalled \<or>\<^sub>b m') = 
         bind (read_state getExceptionSignalled)
              (\<lambda>ex. if \<not> ex then m else return True)"
by (intro monad_eqI)
   (auto simp: ValueAndStatePart_simp)

subsubsection \<open>@{const getBranchTo}\<close>

lemma getBranchTo_simps [simp]:
  shows "getBranchTo (BranchToPCC_update x_BranchToPCC s) = getBranchTo s"
    and "getBranchTo (BranchDelayPCC_update x_BranchDelayPCC s) = getBranchTo s"
    and "getBranchTo (the_MEM_update x_the_MEM s) = getBranchTo s"
    and "getBranchTo (setPCC x_PCC s) = getBranchTo s"
    and "getBranchTo (setCAPR x_CAPR s) = getBranchTo s"
    and "getBranchTo (setSCAPR x_SCAPR s) = getBranchTo s"
    and "getBranchTo (setMEM x_MEM s) = getBranchTo s"
    and "getBranchTo (setBranchDelay x_BranchDelay s) = getBranchTo s"
    and "getBranchTo (exception_update x_exception s) = getBranchTo s"
    and "getBranchTo (setExceptionSignalled x_ExceptionSignalled s) = getBranchTo s"
by (rule Commute_read_state_update_stateE, Commute)+

subsubsection \<open>@{const getBranchDelay}\<close>

lemma getBranchDelay_simps [simp]:
  shows "getBranchDelay (BranchToPCC_update x_BranchToPCC s) = getBranchDelay s"
    and "getBranchDelay (BranchDelayPCC_update x_BranchDelayPCC s) = getBranchDelay s"
    and "getBranchDelay (setPCC x_PCC s) = getBranchDelay s"
    and "getBranchDelay (setCAPR x_CAPR s) = getBranchDelay s"
    and "getBranchDelay (setSCAPR x_SCAPR s) = getBranchDelay s"
    and "getBranchDelay (setMEM x_MEM s) = getBranchDelay s"
    and "getBranchDelay (the_MEM_update x_the_MEM s) = getBranchDelay s"
    and "getBranchDelay (setBranchTo x_BranchTo s) = getBranchDelay s"
    and "getBranchDelay (exception_update x_exception s) = getBranchDelay s"
    and "getBranchDelay (setExceptionSignalled x_ExceptionSignalled s) = getBranchDelay s"
by (rule Commute_read_state_update_stateE, Commute)+

subsubsection \<open>@{const BranchToPCC}\<close>

lemma BranchToPCC_simps [simp]:
  shows "BranchToPCC (BranchDelayPCC_update x_BranchDelayPCC s) = BranchToPCC s"
    and "BranchToPCC (the_MEM_update x_the_MEM s) = BranchToPCC s"
    and "BranchToPCC (setPCC x_PCC s) = BranchToPCC s"
    and "BranchToPCC (setCAPR x_CAPR s) = BranchToPCC s"
    and "BranchToPCC (setSCAPR x_SCAPR s) = BranchToPCC s"
    and "BranchToPCC (setMEM x_MEM s) = BranchToPCC s"
    and "BranchToPCC (setBranchTo x_BranchTo s) = BranchToPCC s"
    and "BranchToPCC (setBranchDelay x_BranchDelay s) = BranchToPCC s"
    and "BranchToPCC (exception_update x_exception s) = BranchToPCC s"
    and "BranchToPCC (setExceptionSignalled x_ExceptionSignalled s) = BranchToPCC s"
    and "BranchToPCC (c_state_update x_c_state s) = BranchToPCC s"
by (rule Commute_read_state_update_stateE, Commute)+

subsubsection \<open>@{const BranchDelayPCC}\<close>

lemma BranchDelayPCC_simps [simp]:
  shows "BranchDelayPCC (BranchToPCC_update x_BranchToPCC s) = BranchDelayPCC s"
    and "BranchDelayPCC (setPCC x_PCC s) = BranchDelayPCC s"
    and "BranchDelayPCC (setCAPR x_CAPR s) = BranchDelayPCC s"
    and "BranchDelayPCC (setSCAPR x_SCAPR s) = BranchDelayPCC s"
    and "BranchDelayPCC (setMEM x_MEM s) = BranchDelayPCC s"
    and "BranchDelayPCC (the_MEM_update x_the_MEM s) = BranchDelayPCC s"
    and "BranchDelayPCC (setBranchTo x_BranchTo s) = BranchDelayPCC s"
    and "BranchDelayPCC (setBranchDelay x_BranchDelay s) = BranchDelayPCC s"
    and "BranchDelayPCC (exception_update x_exception s) = BranchDelayPCC s"
    and "BranchDelayPCC (setExceptionSignalled x_ExceptionSignalled s) = BranchDelayPCC s"
    and "BranchDelayPCC (c_state_update x_c_state s) = BranchDelayPCC s"
by (rule Commute_read_state_update_stateE, Commute)+

subsubsection \<open>@{const PCC}\<close>

lemma getPCC_simps [simp]:
  shows "getPCC (BranchToPCC_update x_BranchToPCC s) = getPCC s"
    and "getPCC (BranchDelayPCC_update x_BranchDelayPCC s) = getPCC s"
    and "getPCC (setCAPR x_CAPR s) = getPCC s"
    and "getPCC (setSCAPR x_SCAPR s) = getPCC s"
    and "getPCC (setMEM x_MEM s) = getPCC s"
    and "getPCC (the_MEM_update x_the_MEM s) = getPCC s"
    and "getPCC (setBranchTo x_BranchTo s) = getPCC s"
    and "getPCC (setBranchDelay x_BranchDelay s) = getPCC s"
    and "getPCC (exception_update x_exception s) = getPCC s"
    and "getPCC (setExceptionSignalled x_ExceptionSignalled s) = getPCC s"
    and "getPCC (c_state_update x_c_state s) = getPCC s"
by (rule Commute_read_state_update_stateE, Commute)+

subsubsection \<open>@{const GPR}\<close>

lemma getGPR_simps [simp]:
  shows "getGPR cd (BranchToPCC_update x_BranchToPCC s) = getGPR cd s"
    and "getGPR cd (BranchDelayPCC_update x_BranchDelayPCC s) = getGPR cd s"
    and "getGPR cd (setPCC x_PCC s) = getGPR cd s"
    and "getGPR cd (setCAPR x_SGPR s) = getGPR cd s"
    and "getGPR cd (setSCAPR x_SGPR s) = getGPR cd s"
    and "getGPR cd (setMEM x_MEM s) = getGPR cd s"
    and "getGPR cd (the_MEM_update x_the_MEM s) = getGPR cd s"
    and "getGPR cd (setBranchTo x_BranchTo s) = getGPR cd s"
    and "getGPR cd (setBranchDelay x_BranchDelay s) = getGPR cd s"
    and "getGPR cd (exception_update x_exception s) = getGPR cd s"
    and "getGPR cd (setExceptionSignalled x_ExceptionSignalled s) = getGPR cd s"
    and "getGPR cd (c_state_update x_c_state s) = getGPR cd s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getGPR_zero [simp]:
  shows "getGPR 0 s = 0"
unfolding GPR_alt_def
by simp

lemma Commute_getGPR_setGPR [Commute_compositeI]:
  assumes "cd \<noteq> cd'"
  shows "Commute (GPR cd) (write'GPR (cap, cd'))"
using assms
unfolding Commute_def
by simp

subsubsection \<open>@{const CAPR}\<close>

lemma getCAPR_simps [simp]:
  shows "getCAPR cd (BranchToPCC_update x_BranchToPCC s) = getCAPR cd s"
    and "getCAPR cd (BranchDelayPCC_update x_BranchDelayPCC s) = getCAPR cd s"
    and "getCAPR cd (setPCC x_PCC s) = getCAPR cd s"
    and "getCAPR cd (setSCAPR x_SCAPR s) = getCAPR cd s"
    and "getCAPR cd (setMEM x_MEM s) = getCAPR cd s"
    and "getCAPR cd (the_MEM_update x_the_MEM s) = getCAPR cd s"
    and "getCAPR cd (setBranchTo x_BranchTo s) = getCAPR cd s"
    and "getCAPR cd (setBranchDelay x_BranchDelay s) = getCAPR cd s"
    and "getCAPR cd (exception_update x_exception s) = getCAPR cd s"
    and "getCAPR cd (setExceptionSignalled x_ExceptionSignalled s) = getCAPR cd s"
    and "getCAPR cd (c_state_update x_c_state s) = getCAPR cd s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getCAPR_zero [simp]:
  shows "getCAPR 0 s = nullCap"
unfolding CAPR_alt_def
by simp

lemma Commute_getCAPR_setCAPR [Commute_compositeI]:
  assumes "cd \<noteq> cd'"
  shows "Commute (CAPR cd) (write'CAPR (cap, cd'))"
using assms
unfolding Commute_def
by simp

subsubsection \<open>@{const SCAPR}\<close>

lemma getSCAPR_simps [simp]:
  shows "getSCAPR cd (BranchToPCC_update x_BranchToPCC s) = getSCAPR cd s"
    and "getSCAPR cd (BranchDelayPCC_update x_BranchDelayPCC s) = getSCAPR cd s"
    and "getSCAPR cd (setPCC x_PCC s) = getSCAPR cd s"
    and "getSCAPR cd (setCAPR x_CAPR s) = getSCAPR cd s"
    and "getSCAPR cd (setMEM x_MEM s) = getSCAPR cd s"
    and "getSCAPR cd (the_MEM_update x_the_MEM s) = getSCAPR cd s"
    and "getSCAPR cd (setBranchTo x_BranchTo s) = getSCAPR cd s"
    and "getSCAPR cd (setBranchDelay x_BranchDelay s) = getSCAPR cd s"
    and "getSCAPR cd (exception_update x_exception s) = getSCAPR cd s"
    and "getSCAPR cd (setExceptionSignalled x_ExceptionSignalled s) = getSCAPR cd s"
    and "getSCAPR cd (c_state_update x_c_state s) = getSCAPR cd s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma Commute_getSCAPR_setSCAPR [Commute_compositeI]:
  assumes "cd \<noteq> cd'"
  shows "Commute (SCAPR cd) (write'SCAPR (cap, cd'))"
using assms
unfolding Commute_def
by simp

subsubsection \<open>@{const MEM}\<close>

lemma getMEM_simps [simp]:
  shows "getMEM a (BranchToPCC_update x_BranchToPCC s) = getMEM a s"
    and "getMEM a (BranchDelayPCC_update x_BranchDelayPCC s) = getMEM a s"
    and "getMEM a (setPCC x_PCC s) = getMEM a s"
    and "getMEM a (setCAPR x_CAPR s) = getMEM a s"
    and "getMEM a (setSCAPR x_SCAPR s) = getMEM a s"
    and "getMEM a (setBranchTo x_BranchTo s) = getMEM a s"
    and "getMEM a (setBranchDelay x_BranchDelay s) = getMEM a s"
    and "getMEM a (exception_update x_exception s) = getMEM a s"
    and "getMEM a (setExceptionSignalled x_ExceptionSignalled s) = getMEM a s"
    and "getMEM a (c_state_update x_c_state s) = getMEM a s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getMEM_update_the_MEM [simp]:
  shows "getMEM a (the_MEM_update f s) = f (the_MEM s) a"
unfolding MEM_alt_def
by (simp add: ValuePart_bind)

subsubsection \<open>@{const the_MEM}\<close>

lemma the_MEM_simps [simp]:
  shows "the_MEM (BranchToPCC_update x_BranchToPCC s) = the_MEM s"
    and "the_MEM (BranchDelayPCC_update x_BranchDelayPCC s) = the_MEM s"
    and "the_MEM (setPCC x_PCC s) = the_MEM s"
    and "the_MEM (setCAPR x_CAPR s) = the_MEM s"
    and "the_MEM (setSCAPR x_SCAPR s) = the_MEM s"
    and "the_MEM (setBranchTo x_BranchTo s) = the_MEM s"
    and "the_MEM (setBranchDelay x_BranchDelay s) = the_MEM s"
    and "the_MEM (exception_update x_exception s) = the_MEM s"
    and "the_MEM (setExceptionSignalled x_ExceptionSignalled s) = the_MEM s"
    and "the_MEM (c_state_update x_c_state s) = the_MEM s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma the_MEM_setMEM [simp]:
  shows "the_MEM (setMEM v s) = (the_MEM s)(snd v := fst v)"
unfolding write'MEM_alt_def
by (cases v) (simp add: StatePart_bind)

subsubsection \<open>@{const KernelMode}\<close>

lemma getKernelMode_simps [simp]:
  shows "getKernelMode (BranchToPCC_update x_BranchToPCC s) = getKernelMode s"
    and "getKernelMode (BranchDelayPCC_update x_BranchDelayPCC s) = getKernelMode s"
    and "getKernelMode (the_MEM_update x_the_MEM s) = getKernelMode s"
    and "getKernelMode (setPCC x_PCC s) = getKernelMode s"
    and "getKernelMode (setCAPR x_CAPR s) = getKernelMode s"
    and "getKernelMode (setSCAPR x_SCAPR s) = getKernelMode s"
    and "getKernelMode (setMEM x_MEM s) = getKernelMode s"
    and "getKernelMode (setBranchTo x_BranchTo s) = getKernelMode s"
    and "getKernelMode (setBranchDelay x_BranchDelay s) = getKernelMode s"
    and "getKernelMode (exception_update x_exception s) = getKernelMode s"
    and "getKernelMode (setExceptionSignalled x_ExceptionSignalled s) = getKernelMode s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getKernelMode_setCP0StatusEXL_True [simp]:
  shows "getKernelMode (setCP0StatusEXL True s) = True"
unfolding KernelMode_alt_def
by (simp add: ValuePart_bind)

lemma getKernelMode_setCP0StatusEXL_False [elim!]:
  assumes "getKernelMode (setCP0StatusEXL False s)"
  shows "getKernelMode s"
using assms
unfolding KernelMode_alt_def
by (auto simp add: ValueAndStatePart_simp)

lemma getKernelMode_setCP0StatusERL_True [simp]:
  shows "getKernelMode (setCP0StatusERL True s) = True"
unfolding KernelMode_alt_def
by (simp add: ValuePart_bind)

lemma getKernelMode_setCP0StatusERL_False [elim!]:
  assumes "getKernelMode (setCP0StatusERL False s)"
  shows "getKernelMode s"
using assms
unfolding KernelMode_alt_def
by (auto simp add: ValueAndStatePart_simp)

subsubsection \<open>@{const raise'exception}\<close>

lemma raise'exception_getExceptionSignalled [simp]:
  shows "getExceptionSignalled (StatePart (raise'exception v) s) = getExceptionSignalled s"
by SimpLemmaViaPrePost

lemma raise'exception_exception:
  shows "exception (StatePart (raise'exception v) s) = 
         (let old_ex = exception s in if old_ex = NoException then v else old_ex)"
unfolding raise'exception_alt_def
by (simp add: StatePart_bind)

subsubsection \<open>@{const check_cca}\<close>

lemma check_cca_getExceptionSignalled [simp]:
  shows "getExceptionSignalled (StatePart (check_cca v) s) = getExceptionSignalled s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const next_unknown}\<close>

lemma next_unknown_getExceptionSignalled [simp]:
  shows "getExceptionSignalled (StatePart (next_unknown v) s) = getExceptionSignalled s"
by SimpLemmaViaPrePost

lemma next_unknown_exception [simp]:
  shows "exception (StatePart (next_unknown v) s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalException}\<close>

lemma setSignalException_simps [simp]:
  shows "getMEM a (setSignalException ex s) = getMEM a s"
    and "the_MEM (setSignalException ex s) = the_MEM s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma setSignalException_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalException v) s) = True"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_exception [simp]:
  shows "exception (setSignalException v s) = exception s"
by SimpLemmaViaPrePost

lemma setSignalException_BranchTo [simp]:
  shows "getBranchTo ((setSignalException v) s) = None"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_BranchDelay [simp]:
  shows "getBranchDelay ((setSignalException v) s) = None"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_BranchToPCC [simp]:
  shows "BranchToPCC ((setSignalException v) s) = None"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_BranchDelayPCC [simp]:
  shows "BranchDelayPCC ((setSignalException v) s) = None"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_getPCC [simp]:
  shows "getPCC ((setSignalException v) s) = getKCC s"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_getCAPR [simp]:
  shows "getCAPR cd ((setSignalException v) s) = getCAPR cd s"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_ExcCode [simp]:
  shows "CauseRegister.ExcCode (Cause (getCP0 ((setSignalException v) s))) = ExceptionCode v"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

lemma setSignalException_CP0Status [simp]:
  shows "Status (getCP0 ((setSignalException v) s)) = Status (getCP0 s)\<lparr>EXL := True\<rparr>"
unfolding SignalException_alt_def
by SimpLemmaViaPrePost

definition SignalExceptionSCAPR where
  "SignalExceptionSCAPR \<equiv> 
   (\<lambda>cd s. if cd = 31 \<and> \<not> EXL (Status (getCP0 s))
           then setOffset (getPCC s, getPC s) 
           else getSCAPR cd s)"

lemma Commute_LegitimateCaps [Commute_compositeI]:
  assumes "Commute (read_state getCP0) m"
      and "Commute (read_state getPC) m"
      and "Commute (read_state getPCC) m"
      and "Commute (read_state (getSCAPR cd)) m"
  shows "Commute (read_state (SignalExceptionSCAPR cd)) m"
using assms
unfolding SignalExceptionSCAPR_def Commute_def
by auto

lemma setSignalException_getSCAPR [simp]:
  shows "getSCAPR cd ((setSignalException v) s) = SignalExceptionSCAPR cd s"
unfolding SignalException_alt_def SignalExceptionSCAPR_def
unfolding canRepOffset_def
-- \<open>The following takes a long time.\<close>
by SimpLemmaViaPrePost
   (auto split: if_splits(1))

definition VectorBaseSignalExceptionPC :: "state \<Rightarrow> 64 word" where
  "VectorBaseSignalExceptionPC s \<equiv> 
   if BEV (Status (getCP0 s)) then 18446744072631616000 else 18446744071562067968"

definition VectorOffsetSignalExceptionPC :: "ExceptionType \<Rightarrow> state \<Rightarrow> 30 word" where
  "VectorOffsetSignalExceptionPC v s \<equiv> 
   if (v = XTLBRefillL \<or> v = XTLBRefillS) \<and> \<not> EXL (Status (getCP0 s)) then 128 
   else if v = C2E \<and> (CapCause.ExcCode (capcause s) = 5 \<or> CapCause.ExcCode (capcause s) = 6) then 640 
   else 384"

definition SignalExceptionPC where
  "SignalExceptionPC v s \<equiv> 
   let vectorBase = VectorBaseSignalExceptionPC s;
       vectorOffset = VectorOffsetSignalExceptionPC v s in
   word_cat ((slice 30 vectorBase)::34 word) (ucast vectorBase + vectorOffset) - 
   getBase (getKCC s)"

lemma setSignalException_getPC [simp]:
  shows "getPC ((setSignalException v) s) = SignalExceptionPC v s"
unfolding SignalException_alt_def 
  SignalExceptionPC_def 
  VectorBaseSignalExceptionPC_def 
  VectorOffsetSignalExceptionPC_def
  canRepOffset_def
unfolding Let_def
-- \<open>The following takes a long time.\<close> 
by (SimpLemmaViaPrePost simp: if_bool_simps)

definition ExceptionPCs where
  "ExceptionPCs \<equiv> 
   let vectorBases :: 64 word set = {18446744072631616000, 18446744071562067968};
   vectorOffsets :: 30 word set = {128, 384, 640} in
   {word_cat ((slice 30 vectorBase)::34 word) (ucast vectorBase + vectorOffset) |
    vectorBase vectorOffset. vectorBase \<in> vectorBases \<and> vectorOffset \<in> vectorOffsets}"

lemma getPC_SignalExecption_in_ExceptionPCs [intro!, simp]:
  shows "getBase (getKCC s) + SignalExceptionPC v s \<in> ExceptionPCs"
proof -
  have "VectorBaseSignalExceptionPC s \<in> {18446744072631616000, 18446744071562067968}"
    unfolding VectorBaseSignalExceptionPC_def by simp
  moreover have "VectorOffsetSignalExceptionPC v s \<in> {128, 384, 640}"
    unfolding VectorOffsetSignalExceptionPC_def by simp
  ultimately show ?thesis
    unfolding SignalExceptionPC_def ExceptionPCs_def Let_def
    by auto
qed

subsubsection \<open>@{const SignalCP2UnusableException}\<close>

lemma setSignalCP2UnusableException_getExceptionSignalled [simp]:
  shows "getExceptionSignalled (setSignalCP2UnusableException s) = True"
unfolding SignalCP2UnusableException_alt_def
by (simp add: StatePart_bind)

lemma setSignalCP2UnusableException_exception [simp]:
  shows "exception (setSignalCP2UnusableException s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalCapException_internal}\<close>

lemma setSignalCapException_internal_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalCapException_internal v) s) = True"
unfolding SignalCapException_internal_alt_def
by (cases v) (simp add: StatePart_bind)

lemma setSignalCapException_internal_exception [simp]:
  shows "exception (setSignalCapException_internal v s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalCapException}\<close>

lemma setSignalCapException_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalCapException v) s) = True"
unfolding SignalCapException_alt_def
by (cases v) (simp add: StatePart_bind)

lemma setSignalCapException_exception [simp]:
  shows "exception (setSignalCapException v s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalCapException_noReg}\<close>

lemma setSignalCapException_noReg_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalCapException_noReg v) s) = True"
unfolding SignalCapException_noReg_alt_def
by simp

lemma setSignalCapException_noReg_exception [simp]:
  shows "exception (setSignalCapException_noReg v s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalTLBException}\<close>

lemma setSignalTLBException_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalTLBException v) s) = True"
unfolding SignalTLBException_alt_def Let_def
by (cases v) (simp add: ValuePart_bind StatePart_bind)

lemma setSignalTLBException_exception [simp]:
  shows "exception (setSignalTLBException v s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const SignalTLBCapException}\<close>

lemma setSignalTLBCapException_getExceptionSignalled [simp]:
  shows "getExceptionSignalled ((setSignalTLBCapException v) s) = True"
unfolding SignalTLBCapException_alt_def Let_def
by (cases v) (simp add: ValuePart_bind StatePart_bind)

lemma setSignalTLBCapException_exception [simp]:
  shows "exception (setSignalTLBCapException v s) = exception s"
by SimpLemmaViaPrePost

subsubsection \<open>@{const CheckSegment}\<close>

lemma getCheckSegment_setExceptionSignalled [simp]:
  "getCheckSegment v (setExceptionSignalled v' s) = getCheckSegment v s"
proof -
  have "Commute (CheckSegment v) (update_state (setExceptionSignalled v'))"
    by Commute
  thus ?thesis
    unfolding Commute_def
    by simp
qed

lemma getCheckSegment_exception [simp]:
  "getCheckSegment v (exception_update v' s) = getCheckSegment v s"
proof -
  have "Commute (CheckSegment v) (update_state (exception_update v'))"
    by Commute
  thus ?thesis
    unfolding Commute_def
    by simp
qed

subsubsection \<open>@{const LookupTLB}\<close>

lemma getLookupTLB_setExceptionSignalled [simp]:
  "getLookupTLB v (setExceptionSignalled v' s) = getLookupTLB v s"
proof -
  have "Commute (LookupTLB v) (update_state (setExceptionSignalled v'))"
    by Commute
  thus ?thesis
    unfolding Commute_def
    by simp
qed

lemma getLookupTLB_exception [simp]:
  "getLookupTLB v (exception_update v' s) = getLookupTLB v s"
proof -
  have "Commute (LookupTLB v) (update_state (exception_update v'))"
    by Commute
  thus ?thesis
    unfolding Commute_def
    by simp
qed

subsubsection \<open>@{const AdjustEndian}\<close>

lemma AdjustEndian_Doubleword [simp]:
  shows "AdjustEndian (DOUBLEWORD, addr) = return addr"
unfolding AdjustEndian_alt_def DOUBLEWORD_def
by simp

lemma AdjustEndian_slice:
  assumes "fst v \<in> {0, 1, 3, 7}"
  shows "(slice 3 (getAdjustEndian v s)::37 word) = slice 3 (snd v)"
using assms
unfolding AdjustEndian_alt_def
by (cases v)
   (auto simp: ValueAndStatePart_simp slice_xor)

subsubsection \<open>@{const updateDwordInRaw}\<close>

lemma extract_byte_updateDwordInRaw:
  shows "extract_byte index (updateDwordInRaw (addr', val, msk, old_blob)) = 
         (if 32 \<le> index then 0
          else if of_nat (index div 8) = (ucast addr':: 2 word) then 
            extract_byte index old_blob AND NOT extract_byte (index mod 8) msk 
            OR extract_byte (index mod 8) val AND extract_byte (index mod 8) msk
          else extract_byte index old_blob)"
proof -
  have twoWord: "x = 3" if "x \<noteq> 0" "x \<noteq> 1" "x \<noteq> 2" for x :: "2 word"
    proof -
      obtain x' where x: "x = of_nat x'" and "x' < 4"
        by (cases x) auto
      hence "x' = 0 \<or> x' = 1 \<or> x' = 2 \<or> x' = 3"
        by auto
      thus ?thesis
        using that x
        by auto
    qed
  have "(of_nat (index div 8) = n) \<longleftrightarrow> (unat n * 8 \<le> index \<and> index < (unat n + 1) * 8)" 
  if "index < 32" for n :: "2 word" 
    using that
    by (auto simp: unat_of_nat unat_arith_simps)
  note [simp] = this[where n=0, simplified] 
                     this[where n=1, simplified] 
                     this[where n=2, simplified] 
                     this[where n=3, simplified]
  have [simp]: "index mod 8 = index - 8" if "8 \<le> index" "index < 16"
    using that mod_less le_mod_geq
    by auto
  have [simp]: "index mod 8 = index - 16" if "16 \<le> index" "index < 24"
    using that mod_less le_mod_geq
    by auto
  have [simp]: "index mod 8 = index - 24" if "24 \<le> index" "index < 32"
    using that mod_less le_mod_geq
    by auto
  have [simp]: "extract_byte (index - 24) x = 0" if "32 \<le> index" for x :: "64 word"
    using that by (auto intro: extract_byte_outside_bounds)
  note extract_byte_word_extract_fixed =
    extract_byte_word_extract[where m'=32]
    extract_byte_word_extract[where m'=24]
    extract_byte_word_extract[where m'=16]
  show ?thesis
    unfolding updateDwordInRaw_def
    by (auto simp: not_le 
                   not_less
                   le_diff_conv2
                   if_distrib[where f="extract_byte _"]
                   extract_byte_word_and
                   extract_byte_word_or
                   extract_byte_word_not
                   extract_byte_ucast
                   extract_byte_word_cat
                   extract_byte_word_extract_fixed  
             intro: twoWord)
qed

subsubsection \<open>@{const isAligned}\<close>

lemma isAlignedI [simp, intro!]:
  shows "isAligned (vAddr, 0)"
unfolding isAligned_def
by simp

lemma isAligned_max_length:
  assumes "isAligned (vAddr, accessLength)"
  shows "unat vAddr mod 8 + unat accessLength < 8"
proof -
  have "ucast vAddr + accessLength = 
        (ucast vAddr AND accessLength) + (ucast vAddr OR accessLength)"
    by simp
  also have "... = ucast vAddr OR accessLength"
    using assms
    unfolding isAligned_def ucast_def
    by simp
  finally have "ucast vAddr \<le> ucast vAddr + accessLength"
    by (simp add: le_word_or2)
  note unat_plus_simple[THEN iffD1, OF this]
  note unat_add_lem[THEN iffD2, OF this]
  thus ?thesis
    by (simp add: unat_and_mask)
qed

subsubsection \<open>@{const special_register_accessible}\<close>

lemma special_register_accessible_zero [simp]:
  "getSpecial_register_accessible 0 s"
unfolding special_register_accessible_alt_def
by simp

lemma special_register_accessible_one [simp]:
  "getSpecial_register_accessible 1 s"
unfolding special_register_accessible_alt_def
by simp

section \<open>Order over capabilities\<close>

text \<open>In this theory we define an order over capabilities.\<close>

subsection \<open>Bitwise operations over permissions\<close>

instantiation Perms_ext :: (Inf) Inf
begin

definition Inf_Perms_ext :: "'a Perms_scheme set \<Rightarrow> 'a Perms_scheme" where
  "Inf_Perms_ext s = Perms.extend (rec'Perms (bitwise_Inf (reg'Perms ` Perms.truncate ` s)))
                                  (Inf (Perms.more ` s))"

instance .. 

end

instantiation Perms_ext :: (Sup) Sup
begin

definition Sup_Perms_ext :: "'a Perms_scheme set \<Rightarrow> 'a Perms_scheme" where
  "Sup_Perms_ext s = Perms.extend (rec'Perms (bitwise_Sup (reg'Perms ` Perms.truncate ` s)))
                                  (Sup (Perms.more ` s))"

instance .. 

end

subsection \<open>Order over system permissions\<close>

instantiation "Perms_ext" :: (order) order

begin

definition less_eq_Perms_ext :: "'a Perms_scheme \<Rightarrow> 'a Perms_scheme \<Rightarrow> bool" where 
  "less_eq_Perms_ext p1 p2 \<equiv> 
     bitwise_less_eq (reg'Perms (Perms.truncate p1)) (reg'Perms (Perms.truncate p2)) \<and>
     Perms.more p1 \<le> Perms.more p2"

definition less_Perms_ext :: "'a Perms_scheme \<Rightarrow> 'a Perms_scheme \<Rightarrow> bool" where
  "less_Perms_ext p1 p2 \<equiv> p1 \<le> p2 \<and> \<not>(p2 \<le> p1)"

instance proof
  fix x y :: "'a Perms_scheme"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_Perms_ext_def ..
next
  fix x :: "'a Perms_scheme"
  show "x \<le> x"
    unfolding less_eq_Perms_ext_def
    by simp
next
  fix x y z :: "'a Perms_scheme"
  assume "x \<le> y" "y \<le> z"
  thus "x \<le> z"
    unfolding less_eq_Perms_ext_def
    by auto
next
  fix x y :: "'a Perms_scheme"
  assume as: "x \<le> y" "y \<le> x" 
  hence more_eq: "Perms.more x = Perms.more y"
    unfolding less_eq_Perms_ext_def by auto    
  have "reg'Perms (Perms.truncate x) = reg'Perms (Perms.truncate y)"
    using as 
    unfolding less_eq_Perms_ext_def
    by auto
  from arg_cong[OF this, where f=rec'Perms]
  have "Perms.truncate x = Perms.truncate y"
    by simp
  thus "x = y"
    unfolding Perms.truncate_def
    using more_eq
    by (intro Perms.equality) simp_all
qed

end

lemma less_eq_Perms_ext_alt:
  shows "p1 \<le> p2 = ((Global p1 \<longrightarrow> Global p2) \<and>
                    (Permit_CCall p1 \<longrightarrow> Permit_CCall p2) \<and>
                    (Permit_Execute p1 \<longrightarrow> Permit_Execute p2) \<and>
                    (Permit_Load p1 \<longrightarrow> Permit_Load p2) \<and>
                    (Permit_Store p1 \<longrightarrow> Permit_Store p2) \<and>
                    (Permit_Load_Capability p1 \<longrightarrow> Permit_Load_Capability p2) \<and>
                    (Permit_Store_Capability p1 \<longrightarrow> Permit_Store_Capability p2) \<and>
                    (Permit_Store_Local_Capability p1 \<longrightarrow> Permit_Store_Local_Capability p2) \<and>
                    (Permit_Seal p1 \<longrightarrow> Permit_Seal p2) \<and>
                    (Permit_Unseal p1 \<longrightarrow> Permit_Unseal p2) \<and>
                    (Access_System_Registers p1 \<longrightarrow> Access_System_Registers p2) \<and>
                    (Permit_Set_CID p1 \<longrightarrow> Permit_Set_CID p2) \<and>
                    (\<forall>i < 20. Reserved p1 !! i \<longrightarrow> Reserved p2 !! i) \<and>
                    (Perms.more p1 \<le> Perms.more p2))" (is "?l = ?r")
proof
  assume "?l"
  hence more_leq: "Perms.more p1 \<le> Perms.more p2"
    unfolding less_eq_Perms_ext_def by simp
  have *: "reg'Perms (Perms.truncate p1) !! i \<longrightarrow> reg'Perms (Perms.truncate p2) !! i" 
  if "i < 32" for i
    using that `?l`
    unfolding less_eq_Perms_ext_def bitwise_less_eq_def
    by auto
  have "\<forall>i<20. Perms.Reserved p1 !! i \<longrightarrow> Perms.Reserved p2 !! i"
    proof (intro allI impI)
      fix i::nat
      assume "i < 20" and as: "Perms.Reserved p1 !! i"
      thus "Perms.Reserved p2 !! i"
        using *[of "i + 12"] as 
        unfolding nth_reg'Perms
        by simp
    qed
  thus "?r"
    using *[of 0] *[of 1] *[of 2] *[of 3] *[of 4] *[of 5] 
          *[of 6] *[of 7] *[of 8] *[of 9] *[of 10] *[of 11]
    using more_leq
    by simp
next
  assume "?r"
  thus "?l"
    unfolding less_eq_Perms_ext_def bitwise_less_eq_def nth_reg'Perms
    by simp
qed

lemma less_eq_Perms_update [simp]:
  shows "p\<lparr>Access_System_Registers := b\<rparr> \<le> p = (b \<longrightarrow> Access_System_Registers p)"
    and "p\<lparr>Global := b\<rparr> \<le> p = (b \<longrightarrow> Global p)"
    and "p\<lparr>Permit_Execute := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Execute p)"
    and "p\<lparr>Permit_Load := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Load p)"
    and "p\<lparr>Permit_Load_Capability := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Load_Capability p)"
    and "p\<lparr>Permit_Seal := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Seal p)"
    and "p\<lparr>Permit_Unseal := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Unseal p)"
    and "p\<lparr>Permit_Store := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Store p)"
    and "p\<lparr>Permit_Store_Capability := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Store_Capability p)"
    and "p\<lparr>Permit_Store_Local_Capability := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Store_Local_Capability p)"
    and "p\<lparr>Permit_Set_CID := b\<rparr> \<le> p = (b \<longrightarrow> Permit_Set_CID p)"
unfolding less_eq_Perms_ext_alt
by simp_all

lemma less_eq_Perms_def:
  fixes p q :: Perms
  shows "p \<le> q = bitwise_less_eq (reg'Perms p) (reg'Perms q)"
unfolding less_eq_Perms_ext_def
by simp

lemma rec'Perms_zero_leq [simp]:
  shows "rec'Perms 0 \<le> p"
unfolding less_eq_Perms_ext_def
by simp

lemma rec'Perms_AND_leq [simp]:
  shows "rec'Perms (p AND q) \<le> rec'Perms p"
    and "rec'Perms (q AND p) \<le> rec'Perms p"
unfolding less_eq_Perms_ext_def
by simp_all

text {* The following rules are unsafe *}

lemmas rec'Perms_AND_leq_forget_right =
  order_trans[OF rec'Perms_AND_leq(1)]

lemmas rec'Perms_AND_leq_forget_left =
  order_trans[OF rec'Perms_AND_leq(2)]

subsection \<open>Order over user permissions\<close>

instantiation "UPerms_ext" :: (order) order

begin

definition less_eq_UPerms_ext :: "'a UPerms_scheme \<Rightarrow> 'a UPerms_scheme \<Rightarrow> bool" where 
  "less_eq_UPerms_ext p1 p2 \<equiv> 
     bitwise_less_eq (reg'UPerms (UPerms.truncate p1)) (reg'UPerms (UPerms.truncate p2)) \<and>
     UPerms.more p1 \<le> UPerms.more p2"

definition less_UPerms_ext :: "'a UPerms_scheme \<Rightarrow> 'a UPerms_scheme \<Rightarrow> bool" where
  "less_UPerms_ext p1 p2 \<equiv> p1 \<le> p2 \<and> \<not>(p2 \<le> p1)"

instance proof
  fix x y :: "'a UPerms_scheme"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_UPerms_ext_def ..
next
  fix x :: "'a UPerms_scheme"
  show "x \<le> x"
    unfolding less_eq_UPerms_ext_def
    by simp
next
  fix x y z :: "'a UPerms_scheme"
  assume "x \<le> y" "y \<le> z"
  thus "x \<le> z"
    unfolding less_eq_UPerms_ext_def
    by auto
next
  fix x y :: "'a UPerms_scheme"
  assume as: "x \<le> y" "y \<le> x" 
  hence more_eq: "UPerms.more x = UPerms.more y"
    unfolding less_eq_UPerms_ext_def by auto    
  have "reg'UPerms (UPerms.truncate x) = reg'UPerms (UPerms.truncate y)"
    using as 
    unfolding less_eq_UPerms_ext_def
    by auto
  from arg_cong[OF this, where f=rec'UPerms]
  have "UPerms.truncate x = UPerms.truncate y"
    by simp
  thus "x = y"
    unfolding UPerms.truncate_def
    using more_eq
    by (intro UPerms.equality) simp_all
qed

end

lemma less_eq_UPerms_def:
  fixes p q :: UPerms
  shows "p \<le> q = bitwise_less_eq (reg'UPerms p) (reg'UPerms q)"
unfolding less_eq_UPerms_ext_def
by simp

lemma rec'UPerms_zero_leq [simp]:
  shows "rec'UPerms 0 \<le> p"
unfolding less_eq_UPerms_ext_def
by simp

lemma rec'UPerms_AND_leq [simp]:
  shows "rec'UPerms (p AND q) \<le> rec'UPerms p"
    and "rec'UPerms (q AND p) \<le> rec'UPerms p"
unfolding less_eq_UPerms_ext_def
by simp_all

text {* The following rules are unsafe *}

lemmas rec'UPerms_AND_leq_forget_right =
  order_trans[OF rec'UPerms_AND_leq(1)]

lemmas rec'UPerms_AND_leq_forget_left =
  order_trans[OF rec'UPerms_AND_leq(2)]

subsection \<open>Order over memory regions\<close>

definition CapabilityWraps :: "Capability \<Rightarrow> bool" where
  "CapabilityWraps cap \<equiv> (uint (getBase cap) + uint (getLength cap) > 2 ^ 64)"

text {* The following defines the region of memory specified by a base and length. *}

definition MemSegment :: "('a::len) word \<Rightarrow> 'a word \<Rightarrow> 'a word set" where
  "MemSegment b l = 
   (if uint b + uint l \<le> 2 ^ LENGTH('a) 
    then {b + i |i. i < l} else UNIV)"

abbreviation "MemSegmentCap cap \<equiv> MemSegment (getBase cap) (getLength cap)"

lemma MemSegment_zero [simp]:
  shows "MemSegment b 0 = {}"
unfolding MemSegment_def
by simp

lemma MemSegment_first [simp]:
  shows "(x \<in> MemSegment x l) = (l \<noteq> 0)"
unfolding MemSegment_def
by (auto simp: word_gt_0)

lemma MemSegment_member_simp:
  fixes x :: "'a::len word"
  shows "(x \<in> MemSegment b l) = 
         (uint b + uint l \<le> 2 ^ LENGTH('a)  \<longrightarrow> x - b < l)" 
  (is "?l \<longleftrightarrow> ?r\<^sub>1 \<longrightarrow> ?r\<^sub>2")
proof (intro iffI)
  assume ?l
  thus "?r\<^sub>1 \<longrightarrow> ?r\<^sub>2"
    unfolding MemSegment_def
    by (auto simp: if_distrib)
next
  assume "?r\<^sub>1 \<longrightarrow> ?r\<^sub>2"
  show ?l
    proof (cases ?r\<^sub>1)
      case True
      hence ?r\<^sub>2
        using `?r\<^sub>1 \<longrightarrow> ?r\<^sub>2` by simp
      hence "\<exists>i. x = b + i \<and> i < l"
        by (intro exI[where x="x - b"]) auto
      thus ?thesis 
        unfolding MemSegment_def
        by auto
    next
      case False
      thus ?thesis 
        unfolding MemSegment_def
        by auto
    qed
qed

lemma MemSegment_memberI [intro]:
  fixes x :: "'a::len word"
  assumes "uint b + uint l \<le> 2 ^ LENGTH('a) \<Longrightarrow> x - b < l"
  shows "x \<in> MemSegment b l"
using assms
unfolding MemSegment_member_simp
by simp

lemma MemSegment_memberE [elim]:
  fixes x :: "'a::len word"
  assumes "x \<in> MemSegment b l"
      and "uint b + uint l \<le> 2 ^ LENGTH('a)"
  shows "x - b < l"
using assms
unfolding MemSegment_member_simp
by simp

lemma MemSegment_memberI_65word:
  fixes x b l :: "64 word" and y :: "65 word"
  assumes "(ucast x::65 word) + y \<le> ucast b + ucast l"
      and "b \<le> x"
      and "1 \<le> y" "y < 2 ^ 64"
  shows "x \<in> MemSegment b l"
proof -
  define y' :: "64 word" where "y' = ucast y"    
  have "uint y mod 2 ^ 64 = uint y"
    using `1 \<le> y` `y < 2 ^ 64`
    unfolding word_less_def word_le_def
    using int_mod_eq'
    by auto
  hence y_def: "y = ucast y'"
    unfolding y'_def
    by (simp add: and_mask_mod_2p)
  have "uint x + uint y \<le> uint b + uint l"
    using assms 
    unfolding y_def word_le_def uint_word_of_int
    by simp
  hence "uint x < uint b + uint l"
    using `1 \<le> y`
    unfolding y_def word_le_def
    by simp
  hence "x - b < l"
    using `b \<le> x`
    unfolding uint_minus_simple_alt word_less_def
    by auto
  thus ?thesis by auto
qed

lemma MemSegment_subsetI:
  fixes b b' l l' :: "('a::len) word"
  assumes shorter: "uint (b - b') + uint l \<le> uint l'"
  shows "MemSegment b l \<subseteq> MemSegment b' l'"
proof (cases "uint b + uint l \<le> 2 ^ LENGTH('a)")
  case True
  let ?d = "b - b'"
  have "b + i - b' < l'" if "i < l" for i
    using that
    proof -
      fix i
      assume "i < l"
      have "?d + i < l'"
        using uint_add_le[of ?d i] `i < l` shorter
        unfolding word_less_def
        by auto
      have "b + i - b' = b - b' + i" by auto
      thus "b + i - b' < l'"
        using `?d + i < l'` by arith
    qed  
  hence "b + i \<in> MemSegment b' l'" if "i < l" for i
    using that 
    unfolding MemSegment_member_simp
    by auto
  thus "MemSegment b l \<subseteq> MemSegment b' l'"
    using True
    unfolding MemSegment_def
    by auto
next
  case False
  hence "2 ^ LENGTH('a) < uint b' + uint l'"
    using shorter uint_sub_ge[where x=b and y=b']
    by auto
  thus ?thesis 
    unfolding MemSegment_def by auto
qed

lemma aligned_MemSegment_member:
  fixes a b :: "'a::len word"
  assumes "a AND NOT mask n = b AND NOT mask n"
      and "n < LENGTH('a)"
  shows "a \<in> MemSegment (b AND NOT mask n) (2 ^ n)"
proof -
  have "a - (a AND NOT mask n) < 2 ^ n"
    using assms(2)
    by (simp add: and_mask_less')    
  hence "a - (b AND NOT mask n) < 2 ^ n"
    using assms(1) by simp
  thus ?thesis by auto
qed

subsection \<open>Order over capabilities\<close>

instantiation "Capability_ext" :: (preorder) preorder

begin

definition less_eq_Capability :: "Capability \<Rightarrow> Capability \<Rightarrow> bool" where 
  "less_eq_Capability cap\<^sub>1 cap\<^sub>2 \<equiv>
     (\<not> getTag cap\<^sub>1) \<or>
     (cap\<^sub>1 = cap\<^sub>2) \<or>
     ((\<not> getSealed cap\<^sub>1) \<and>
      (\<not> getSealed cap\<^sub>2) \<and>
      (getTag cap\<^sub>2) \<and>
      (MemSegmentCap cap\<^sub>1 \<subseteq> MemSegmentCap cap\<^sub>2) \<and>
      (getPerms cap\<^sub>1 \<le> getPerms cap\<^sub>2) \<and>
      (getUPerms cap\<^sub>1 \<le> getUPerms cap\<^sub>2) \<and>
      (getType cap\<^sub>1 = getType cap\<^sub>2) \<and>
      (reserved cap\<^sub>1 = reserved cap\<^sub>2))"

lemma less_eq_Capability_refl [simp]:
  shows "less_eq_Capability cap cap"
unfolding less_eq_Capability_def
by simp

lemma less_eq_Capability_trans:
  assumes "less_eq_Capability x y"
      and "less_eq_Capability y z"
  shows "less_eq_Capability x z"
using assms
unfolding less_eq_Capability_def
by auto

definition less_eq_Capability_ext :: "'a Capability_scheme \<Rightarrow> 'a Capability_scheme \<Rightarrow> bool" where 
  "less_eq_Capability_ext cap\<^sub>1 cap\<^sub>2 \<equiv> 
     (less_eq_Capability (Capability.truncate cap\<^sub>1) (Capability.truncate cap\<^sub>2)) \<and>
     (Capability.more cap\<^sub>1 \<le> Capability.more cap\<^sub>2)"

definition less_Capability_ext :: "'a Capability_scheme \<Rightarrow> 'a Capability_scheme \<Rightarrow> bool" where
  "less_Capability_ext cap\<^sub>1 cap\<^sub>2 \<equiv> cap\<^sub>1 \<le> cap\<^sub>2 \<and> \<not>(cap\<^sub>2 \<le> cap\<^sub>1)"

instance proof
  fix x y :: "'a Capability_scheme"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_Capability_ext_def ..
next
  fix x :: "'a Capability_scheme"
  show "x \<le> x"
    unfolding less_eq_Capability_ext_def
    by simp
next
  fix x y z :: "'a Capability_scheme"
  assume assms: "x \<le> y" "y \<le> z"
  thus "x \<le> z"
    using order_trans less_eq_Capability_trans
    unfolding less_eq_Capability_ext_def
    by metis
qed

end

(* lemma less_eq_Capability_ext_no_extension:
  fixes cap\<^sub>1 cap\<^sub>2 :: Capability
  shows "cap\<^sub>1 \<le> cap\<^sub>2 = less_eq_Capability cap\<^sub>1 cap\<^sub>2"
unfolding less_eq_Capability_ext_def
by simp *)

subsubsection \<open>@{const nullCap}}\<close>

lemma noTag_le [elim!]:
  assumes "\<not> getTag cap"
  shows "cap \<le> cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def 
by simp

lemma nullCap_le [simp]:
  shows "nullCap \<le> cap'"
by (intro noTag_le) simp

lemma bitsToCap_le [simp]:
  shows "bitsToCap x \<le> cap"
by (intro noTag_le) simp

lemma setOffset_nullCap_le [simp]:
  shows "setOffset (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma setBounds_nullCap_le [simp]:
  shows "setBounds (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma setPerms_nullCap_le [simp]:
  shows "setPerms (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma setUPerms_nullCap_le [simp]:
  shows "setUPerms (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma setSealed_nullCap_le [simp]:
  shows "setSealed (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma setType_nullCap_le [simp]:
  shows "setType (nullCap, v) \<le> cap"
by (intro noTag_le) simp

lemma if_nullCap_le [simp]:
  shows "(if b then nullCap else cap) \<le> cap' =
         (if b then True else cap \<le> cap')"
    and "(if b then cap else nullCap) \<le> cap' =
         (if b then cap \<le> cap' else True)"
by auto

subsubsection \<open>Setter introductions\<close>

lemma setTag_le [intro!, simp]:
  shows "setTag (cap, False) \<le> cap'"
by (intro noTag_le) simp

lemma setOffset_le:
  shows "(setOffset (cap, v) \<le> cap) =
         (\<not> getTag cap \<or> \<not> getSealed cap \<or> getOffset cap = v)"
proof (cases "setOffset (cap, v) = cap")
  case True
  from arg_cong[OF this, where f=getOffset]
  show ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
next
  case False
  thus ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
qed

lemma setBounds_le:
  shows "(setBounds (cap, v) \<le> cap) =
         (\<not> getTag cap \<or> 
          (if getSealed cap then getOffset cap = 0 \<and> getLength cap = v
           else MemSegment (getBase cap + getOffset cap) v \<subseteq> 
                MemSegment (getBase cap) (getLength cap)))"
proof (cases "setBounds (cap, v) = cap")
  case True
  from arg_cong[OF this, where f=getBase]
       arg_cong[OF this, where f=getLength]
  show ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
next
  case False
  thus ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
qed

lemma setPerms_le:
  shows "(setPerms (cap, p) \<le> cap) =
         (\<not> getTag cap \<or> 
          (if getSealed cap then getPerms cap = rec'Perms (reg'Perms p AND mask 15)
           else rec'Perms (reg'Perms p AND mask 15) \<le> getPerms cap))"
proof (cases "setPerms (cap, p) = cap")
  case True
  from arg_cong[OF this, where f=getPerms]
  show ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
next
  case False
  thus ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
qed

lemma setUPerms_le:
  shows "(setUPerms (cap, p) \<le> cap) =
         (\<not> getTag cap \<or> 
          (if getSealed cap then getUPerms cap = rec'UPerms (reg'UPerms p AND mask 16)
           else rec'UPerms (reg'UPerms p AND mask 16) \<le> getUPerms cap))"
proof (cases "setUPerms (cap, p) = cap")
  case True
  from arg_cong[OF this, where f=getUPerms]
  show ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
next
  case False
  thus ?thesis 
    unfolding less_eq_Capability_ext_def less_eq_Capability_def 
    by auto
qed

subsubsection \<open>Eliminations\<close>

lemma less_eq_CapabilityE_IsSealed:
  assumes "cap \<le> cap'"
      and "getTag cap"
      and "getSealed cap"
  shows "cap = cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto
                                    
lemma less_eq_CapabilityE_MemSegment [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "MemSegmentCap cap \<subseteq> MemSegmentCap cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemma MemSegmentGreaterCap [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
      and "a \<in> MemSegmentCap cap"
  shows "a \<in> MemSegmentCap cap'"
using less_eq_CapabilityE_MemSegment[OF assms(1, 2)] assms(3)
by auto

lemma less_eq_CapabilityE_getPerms [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "getPerms cap \<le> getPerms cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemma less_eq_CapabilityE_getUPerms [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "getUPerms cap \<le> getUPerms cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemma less_eq_CapabilityE_getTag [elim!]:
  assumes "cap \<le> cap'"
  shows "getTag cap \<longrightarrow> getTag cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemma TagOfGreaterCap [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "getTag cap'"
using less_eq_CapabilityE_getTag[OF assms(1)] assms(2)
by auto

lemma less_eq_CapabilityE_getType [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "getType cap = getType cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemmas less_eq_CapabilityE_getType_sym [elim] = 
  less_eq_CapabilityE_getType[THEN sym]

lemma less_eq_CapabilityE_getSealed [elim]:
  assumes "cap \<le> cap'"
      and "getTag cap"
  shows "getSealed cap = getSealed cap'"
using assms
unfolding less_eq_Capability_ext_def less_eq_Capability_def
by auto

lemmas less_eq_CapabilityE_getSealed_sym [elim] = 
  less_eq_CapabilityE_getSealed[THEN sym]

section \<open>Capability locations\<close>

text \<open>In this section we introduce a uniform way to access capabilities from different parts of the
state.\<close>

subsection \<open>\<open>getBranchDelayPccCap\<close>\<close>

definition getBranchDelayPccCap :: "state \<Rightarrow> Capability" where
  "getBranchDelayPccCap s \<equiv>
     (case BranchDelayPCC s of 
        None \<Rightarrow> nullCap
      | Some (_, cap) \<Rightarrow> cap)"

lemma Commute_getBranchDelayPccCap [Commute_compositeI]:
  assumes "Commute (read_state BranchDelayPCC) m"
  shows "Commute (read_state getBranchDelayPccCap) m"
unfolding getBranchDelayPccCap_def
using assms
by auto

lemma getBranchDelayPccCap_simps [simp]:
  shows "getBranchDelayPccCap (BranchToPCC_update x_BranchToPCC s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (the_MEM_update x_the_MEM s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setPCC x_PCC s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setCAPR x_CAPR s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setSCAPR x_SCAPR s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setMEM x_MEM s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setBranchTo x_BranchTo s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setBranchDelay x_BranchDelay s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (exception_update x_exception s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (setExceptionSignalled x_ExceptionSignalled s) = getBranchDelayPccCap s"
    and "getBranchDelayPccCap (c_state_update x_c_state s) = getBranchDelayPccCap s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getBranchDelayPccCap_setBranchDelayPCC [simp]:
  shows "getBranchDelayPccCap (s\<lparr>BranchDelayPCC := v\<rparr>) = 
         (case v of None \<Rightarrow> nullCap 
                  | Some (addr, cap) \<Rightarrow> cap)"
unfolding getBranchDelayPccCap_def
by simp

lemma getBranchDelayPccCap_setSignalException [simp]:
  shows "getBranchDelayPccCap (setSignalException v s) = nullCap"
unfolding getBranchDelayPccCap_def
by simp

subsection \<open>\<open>getBranchToPccCap\<close>\<close>

definition getBranchToPccCap :: "state \<Rightarrow> Capability" where
  "getBranchToPccCap s \<equiv>
     (case BranchToPCC s of 
        None \<Rightarrow> nullCap
      | Some (_, cap) \<Rightarrow> cap)"

lemma Commute_getBranchToPccCap [Commute_compositeI]:
  assumes "Commute (read_state BranchToPCC) m"
  shows "Commute (read_state getBranchToPccCap) m"
unfolding getBranchToPccCap_def
using assms
by auto

lemma getBranchToPccCap_simps [simp]:
  shows "getBranchToPccCap (BranchDelayPCC_update x_BranchDelayPCC s) = getBranchToPccCap s"
    and "getBranchToPccCap (the_MEM_update x_the_MEM s) = getBranchToPccCap s"
    and "getBranchToPccCap (setPCC x_PCC s) = getBranchToPccCap s"
    and "getBranchToPccCap (setCAPR x_CAPR s) = getBranchToPccCap s"
    and "getBranchToPccCap (setSCAPR x_SCAPR s) = getBranchToPccCap s"
    and "getBranchToPccCap (setMEM x_MEM s) = getBranchToPccCap s"
    and "getBranchToPccCap (setBranchTo x_BranchTo s) = getBranchToPccCap s"
    and "getBranchToPccCap (setBranchDelay x_BranchDelay s) = getBranchToPccCap s"
    and "getBranchToPccCap (exception_update x_exception s) = getBranchToPccCap s"
    and "getBranchToPccCap (setExceptionSignalled x_ExceptionSignalled s) = getBranchToPccCap s"
    and "getBranchToPccCap (c_state_update x_c_state s) = getBranchToPccCap s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getBranchToPccCap_setBranchToPCC [simp]:
  shows "getBranchToPccCap (s\<lparr>BranchToPCC := v\<rparr>) =
         (case v of None \<Rightarrow> nullCap 
                  | Some (addr, cap) \<Rightarrow> cap)"
unfolding getBranchToPccCap_def
by simp

lemma getBranchToPccCap_setSignalException [simp]:
  shows "getBranchToPccCap (setSignalException v s) = nullCap"
unfolding getBranchToPccCap_def
by simp

subsection \<open>\<open>getMemCap\<close>\<close>

definition getMemCap :: "PhysicalCapAddress \<Rightarrow> state \<Rightarrow> Capability" where
  "getMemCap a s \<equiv>
   (case getMEM a s of Cap cap \<Rightarrow> cap | Raw x \<Rightarrow> bitsToCap x)"

lemma Commute_getMemCap [Commute_compositeI]:
  assumes "Commute (read_state (getMEM a)) m"
  shows "Commute (read_state (getMemCap a)) m"
unfolding getMemCap_def
using assms
by auto

lemma getMemCap_simps [simp]:
  shows "getMemCap a (BranchToPCC_update x_BranchToPCC s) = getMemCap a s"
    and "getMemCap a (BranchDelayPCC_update x_BranchDelayPCC s) = getMemCap a s"
    and "getMemCap a (setPCC x_PCC s) = getMemCap a s"
    and "getMemCap a (setCAPR x_CAPR s) = getMemCap a s"
    and "getMemCap a (setSCAPR x_SCAPR s) = getMemCap a s"
    and "getMemCap a (setBranchTo x_BranchTo s) = getMemCap a s"
    and "getMemCap a (setBranchDelay x_BranchDelay s) = getMemCap a s"
    and "getMemCap a (exception_update x_exception s) = getMemCap a s"
    and "getMemCap a (setExceptionSignalled x_ExceptionSignalled s) = getMemCap a s"
    and "getMemCap a (c_state_update x_c_state s) = getMemCap a s"
    and "getMemCap a (setStats_valid_cap_writes_updt x_Stats_valid s) = getMemCap a s"
    and "getMemCap a (setStats_invalid_cap_writes_updt x_Stats_invalid s) = getMemCap a s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getMemCap_setSignalException [simp]:
  shows "getMemCap a (setSignalException v s) = getMemCap a s"
unfolding getMemCap_def
by simp

lemma getMemCap_setMem [simp]:
  shows "getMemCap a (setMEM (val, a') s) = 
         (if a' = a 
          then (case val of Raw x \<Rightarrow> bitsToCap x | Cap cap \<Rightarrow> cap) 
          else getMemCap a s)"
unfolding getMemCap_def
by simp

lemma getMemCap_theMEM_update [simp]:
  shows "getMemCap a (s\<lparr>the_MEM := f\<rparr>) = 
         (case f a of Raw x \<Rightarrow> bitsToCap x | Cap cap \<Rightarrow> cap)"
unfolding getMemCap_def
by simp

lemma getMemCap_setWriteCap [simp]:
  shows "getMemCap a (setWriteCap (a', cap) s) = 
         (if a' = a then cap else getMemCap a s)"
unfolding WriteCap_alt_def
by (simp add: ValueAndStatePart_simp)

lemma getMemCap_getMEM [elim!]:
  assumes "getMEM a s = getMEM a s'"
  shows "getMemCap a s = getMemCap a s'"
using assms
unfolding getMemCap_def
by simp

lemma getReadCap_simp [simp]:
  shows "getReadCap a s = getMemCap a s"
unfolding ReadCap_alt_def getMemCap_def
by (simp add: ValueAndStatePart_simp)

subsection \<open>Capability registers\<close>

datatype CapRegister = 
    RegPCC
  | RegBranchDelayPCC
  | RegBranchToPCC
  | RegGeneral RegisterAddress
  | RegSpecial RegisterAddress

lemmas Commute_CapRegisterI [Commute_compositeI] =
  CapRegister.splits(1)[where P="\<lambda>x. Commute x n", THEN iffD2] for n

lemmas ValuePart_CapRegister [ValueAndStatePart_simp] =
  CapRegister.case_distrib[where h="\<lambda>x. ValuePart x _"]

lemmas StatePart_CapRegister [ValueAndStatePart_simp] =
  CapRegister.case_distrib[where h="\<lambda>x. StatePart x _"]

fun IsGeneralRegister where
  "IsGeneralRegister (RegGeneral cd) = True" |
  "IsGeneralRegister x = False"

fun IsSpecialRegister where
  "IsSpecialRegister (RegSpecial cd) = True" |
  "IsSpecialRegister x = False"

definition getCapReg :: "CapRegister \<Rightarrow> state \<Rightarrow> Capability" where
  "getCapReg \<equiv> 
   (\<lambda>loc s. case loc of 
      RegPCC \<Rightarrow> getPCC s 
    | RegBranchDelayPCC \<Rightarrow> getBranchDelayPccCap s
    | RegBranchToPCC \<Rightarrow> getBranchToPccCap s
    | RegGeneral cd \<Rightarrow> getCAPR cd s
    | RegSpecial cd \<Rightarrow> getSCAPR cd s)"

lemma getCapReg_loc_simps [simp]:
  shows "getCapReg RegPCC = getPCC"
    and "getCapReg RegBranchDelayPCC = getBranchDelayPccCap"
    and "getCapReg RegBranchToPCC = getBranchToPccCap"
    and "getCapReg (RegGeneral cd) = getCAPR cd"
    and "getCapReg (RegSpecial cd) = getSCAPR cd"
unfolding getCapReg_def
by simp_all

lemma Commute_getCapReg [Commute_compositeI]:
  assumes "Commute (read_state getPCC) m"
      and "Commute (read_state getBranchDelayPccCap) m"
      and "Commute (read_state getBranchToPccCap) m"
      and "\<And>cd. Commute (read_state (getCAPR cd)) m"
      and "\<And>cd. Commute (read_state (getSCAPR cd)) m"
  shows "Commute (read_state (getCapReg loc)) m"
using assms
by (cases loc) simp_all

lemma getCapReg_simps [simp]:
  shows "getCapReg loc (setBranchTo x_BranchTo s) = getCapReg loc s"
    and "getCapReg loc (setBranchDelay x_BranchDelay s) = getCapReg loc s"
    and "getCapReg loc (exception_update x_exception s) = getCapReg loc s"
    and "getCapReg loc (setExceptionSignalled x_ExceptionSignalled s) = getCapReg loc s"
    and "getCapReg loc (c_state_update x_c_state s) = getCapReg loc s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getCapReg_setPCC_simp [simp]:
  shows "getCapReg loc (setPCC cap s) = 
         (if loc = RegPCC then cap else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setBranchDelayPCC_None_simp [simp]:
  shows "getCapReg loc (s\<lparr>BranchDelayPCC := None\<rparr>) = 
         (if loc = RegBranchDelayPCC then nullCap else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setBranchDelayPCC_Some_simp [simp]:
  shows "getCapReg loc (s\<lparr>BranchDelayPCC := Some v\<rparr>) = 
         (if loc = RegBranchDelayPCC then snd v else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setBranchToPCC_None_simp [simp]:
  shows "getCapReg loc (s\<lparr>BranchToPCC := None\<rparr>) = 
         (if loc = RegBranchToPCC then nullCap else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setBranchToPCC_Some_simp [simp]:
  shows "getCapReg loc (s\<lparr>BranchToPCC := Some v\<rparr>) = 
         (if loc = RegBranchToPCC then snd v else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setCAPR_simp [simp]:
  shows "getCapReg loc (setCAPR v s) = 
         (if loc = RegGeneral (snd v) \<and> snd v \<noteq> 0 then fst v else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setSCAPR_simp [simp]:
  shows "getCapReg loc (setSCAPR v s) = 
         (if loc = RegSpecial (snd v) then fst v else getCapReg loc s)"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setMEM_Raw_simp [simp]:
  shows "getCapReg loc (setMEM (Raw x, a) s) = getCapReg loc s"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_setMEM_Cap_simp [simp]:
  shows "getCapReg loc (setMEM (Cap cap, a) s) = getCapReg loc s"
unfolding getCapReg_def
by (cases loc) simp_all

lemma getCapReg_theMEM_update_simp [simp]:
  shows "getCapReg loc (s\<lparr>the_MEM := f\<rparr>) = getCapReg loc s"
unfolding getCapReg_def
by (cases loc) simp_all

subsection \<open>Capability locations\<close>
  
datatype CapLocation = 
    LocReg CapRegister
  | LocMem PhysicalCapAddress

lemmas Commute_CapLocationI [Commute_compositeI] =
  CapLocation.splits(1)[where P="\<lambda>x. Commute x n", THEN iffD2] for n

lemmas ValuePart_CapLocation [ValueAndStatePart_simp] =
  CapLocation.case_distrib[where h="\<lambda>x. ValuePart x _"]

lemmas StatePart_CapLocation [ValueAndStatePart_simp] =
  CapLocation.case_distrib[where h="\<lambda>x. StatePart x _"]
      
definition getCap :: "CapLocation \<Rightarrow> state \<Rightarrow> Capability" where
  "getCap \<equiv> 
   (\<lambda>loc s. case loc of 
      LocReg r \<Rightarrow> getCapReg r s
    | LocMem addr \<Rightarrow> getMemCap addr s)"

lemma getCap_loc_simps [simp]:
  shows "getCap (LocReg r) = getCapReg r"
    and "getCap (LocMem a) = getMemCap a"
unfolding getCap_def
by simp_all

lemma Commute_getCap [Commute_compositeI]:
  assumes "\<And>r. Commute (read_state (getCapReg r)) m"
      and "\<And>a. Commute (read_state (getMemCap a)) m"
  shows "Commute (read_state (getCap loc)) m"
using assms
by (cases loc) simp_all

lemma getCap_simps [simp]:
  shows "getCap loc (setBranchTo x_BranchTo s) = getCap loc s"
    and "getCap loc (setBranchDelay x_BranchDelay s) = getCap loc s"
    and "getCap loc (exception_update x_exception s) = getCap loc s"
    and "getCap loc (setExceptionSignalled x_ExceptionSignalled s) = getCap loc s"
    and "getCap loc (c_state_update x_c_state s) = getCap loc s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getCap_setPCC_simp [simp]:
  shows "getCap loc (setPCC cap s) = 
         (if loc = LocReg RegPCC then cap else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setBranchDelayPCC_None_simp [simp]:
  shows "getCap loc (s\<lparr>BranchDelayPCC := None\<rparr>) = 
         (if loc = LocReg RegBranchDelayPCC then nullCap else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setBranchDelayPCC_Some_simp [simp]:
  shows "getCap loc (s\<lparr>BranchDelayPCC := Some v\<rparr>) = 
         (if loc = LocReg RegBranchDelayPCC then snd v else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setBranchToPCC_None_simp [simp]:
  shows "getCap loc (s\<lparr>BranchToPCC := None\<rparr>) = 
         (if loc = LocReg RegBranchToPCC then nullCap else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setBranchToPCC_Some_simp [simp]:
  shows "getCap loc (s\<lparr>BranchToPCC := Some v\<rparr>) = 
         (if loc = LocReg RegBranchToPCC then snd v else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setCAPR_simp [simp]:
  shows "getCap loc (setCAPR v s) = 
         (if loc = LocReg (RegGeneral (snd v)) \<and> snd v \<noteq> 0 then fst v else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setMEM_Raw_simp [simp]:
  shows "getCap loc (setMEM (Raw x, a) s) = 
         (if loc = LocMem a then bitsToCap x else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_setMEM_Cap_simp [simp]:
  shows "getCap loc (setMEM (Cap cap, a) s) = 
         (if loc = LocMem a then cap else getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

lemma getCap_theMEM_update_simp [simp]:
  shows "getCap loc (s\<lparr>the_MEM := f\<rparr>) = 
         (case loc of LocMem a \<Rightarrow> (case f a of Raw x \<Rightarrow> bitsToCap x 
                                             | Cap cap \<Rightarrow> cap)
                    | _ \<Rightarrow> getCap loc s)"
unfolding getCap_def
by (cases loc) simp_all

subsection \<open>Accessibility\<close>

definition RegisterIsAccessible where
  "RegisterIsAccessible r \<equiv>
   case r of RegSpecial cd \<Rightarrow> special_register_accessible cd
           | _ \<Rightarrow> return True"

abbreviation "getRegisterIsAccessible r \<equiv> ValuePart (RegisterIsAccessible r)"

lemma RegisterIsAccessible_simps [simp]:
  shows "RegisterIsAccessible RegPCC = return True"
    and "RegisterIsAccessible RegBranchDelayPCC = return True"
    and "RegisterIsAccessible RegBranchToPCC = return True"
    and "RegisterIsAccessible (RegGeneral cd) = return True"
    and "RegisterIsAccessible (RegSpecial cd) = special_register_accessible cd"
unfolding RegisterIsAccessible_def
by simp_all

lemma RegisterIsAccessible_StatePart [simp]:
  shows "StatePart (RegisterIsAccessible r) s = s"
unfolding RegisterIsAccessible_def
by (cases r) (auto simp: ValueAndStatePart_simp)

lemma Commute_RegisterIsAccessible [Commute_compositeI]:
  assumes "\<And>cd. Commute (special_register_accessible cd) m"
  shows "Commute (RegisterIsAccessible r) m"
unfolding RegisterIsAccessible_def
by (Commute intro: assms)

section \<open>Memory accessors\<close>

subsection \<open>\<open>getMemData\<close>\<close>

definition getMemData :: "PhysicalAddress \<Rightarrow> state \<Rightarrow> 8 word" where
  "getMemData a s \<equiv>
     let upper = slice (log2 CAPBYTEWIDTH) a in
     let lower = a AND mask (log2 CAPBYTEWIDTH) in
     let big_endian = lower XOR mask 3 in 
     extract_byte (unat big_endian) 
                  (case getMEM upper s of Cap cap \<Rightarrow> capToBits cap 
                                        | Raw x \<Rightarrow> x)"

lemma Commute_getMemData [Commute_compositeI]:
  assumes "Commute (read_state (getMEM (slice (log2 CAPBYTEWIDTH) a))) m"
  shows "Commute (read_state (getMemData a)) m"
unfolding getMemData_def
using assms
by auto

lemma getMemData_simps [simp]:
  shows "getMemData a (BranchToPCC_update x_BranchToPCC s) = getMemData a s"
    and "getMemData a (BranchDelayPCC_update x_BranchDelayPCC s) = getMemData a s"
    and "getMemData a (setPCC x_PCC s) = getMemData a s"
    and "getMemData a (setCAPR x_CAPR s) = getMemData a s"
    and "getMemData a (setSCAPR x_SCAPR s) = getMemData a s"
    and "getMemData a (setBranchTo x_BranchTo s) = getMemData a s"
    and "getMemData a (setBranchDelay x_BranchDelay s) = getMemData a s"
    and "getMemData a (exception_update x_exception s) = getMemData a s"
    and "getMemData a (setExceptionSignalled x_ExceptionSignalled s) = getMemData a s"
    and "getMemData a (c_state_update x_c_state s) = getMemData a s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getMemData_setSignalException [simp]:
  shows "getMemData a (setSignalException v s) = getMemData a s"
unfolding getMemData_def
by simp

lemma getMemData_getMEM:
  assumes "getMEM (slice (log2 CAPBYTEWIDTH) a) s = getMEM (slice (log2 CAPBYTEWIDTH) a) s'"
  shows "getMemData a s = getMemData a s'"
using assms
unfolding getMemData_def
by simp

lemma getMemData_getMemCap:
  shows "getMemData a s =
     (let upper = slice (log2 CAPBYTEWIDTH) a in
      let lower = a AND mask (log2 CAPBYTEWIDTH) in
      let big_endian = lower XOR mask 3 in 
      extract_byte (unat big_endian) (capToBits (getMemCap upper s)))"
unfolding getMemData_def getMemCap_def
unfolding DataType.case_distrib[where h=capToBits]
by strong_cong_simp

subsection \<open>\<open>getMemTag\<close>\<close>

definition getMemTag :: "PhysicalCapAddress \<Rightarrow> state \<Rightarrow> bool" where
  "getMemTag a s \<equiv> getTag (getMemCap a s)"

lemma Commute_getMemTag [Commute_compositeI]:
  assumes "Commute (read_state (getMemCap a)) m"
  shows "Commute (read_state (getMemTag a)) m"
unfolding getMemTag_def
using assms
by auto

lemma getMemTag_simps [simp]:
  shows "getMemTag a (BranchToPCC_update x_BranchToPCC s) = getMemTag a s"
    and "getMemTag a (BranchDelayPCC_update x_BranchDelayPCC s) = getMemTag a s"
    and "getMemTag a (setPCC x_PCC s) = getMemTag a s"
    and "getMemTag a (setCAPR x_CAPR s) = getMemTag a s"
    and "getMemTag a (setSCAPR x_SCAPR s) = getMemTag a s"
    and "getMemTag a (setBranchTo x_BranchTo s) = getMemTag a s"
    and "getMemTag a (setBranchDelay x_BranchDelay s) = getMemTag a s"
    and "getMemTag a (exception_update x_exception s) = getMemTag a s"
    and "getMemTag a (setExceptionSignalled x_ExceptionSignalled s) = getMemTag a s"
    and "getMemTag a (c_state_update x_c_state s) = getMemTag a s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getMemTag_setSignalException [simp]:
  shows "getMemTag a (setSignalException v s) = getMemTag a s"
unfolding getMemTag_def
by simp

lemma getMemTag_getMEM [elim!]:
  assumes "getMEM a s = getMEM a s'"
  shows "getMemTag a s = getMemTag a s'"
using getMemCap_getMEM[OF assms]
unfolding getMemTag_def
by simp

section \<open>Unpredictable behaviour\<close>

text \<open>The L3 model sets a flag in the state when unpredictable behaviour occurs, but it does not
define the semantics of unpredictable behaviour. We define the semantics in this theory, based
on the specification in the CHERI ISA.\<close>

subsection \<open>\<open>Unpredictable\<close> flag\<close>

definition isUnpredictable where
  "isUnpredictable \<equiv> \<lambda>s. exception s \<noteq> NoException"

lemma Commute_isUnpredictable [Commute_compositeI]:
  assumes "Commute (read_state exception) m"
  shows "Commute (read_state isUnpredictable) m"
unfolding isUnpredictable_def
using assms
by auto

lemma isUnpredictable_simps [simp]:
  shows "isUnpredictable (BranchToPCC_update x_BranchToPCC s) = isUnpredictable s"
    and "isUnpredictable (BranchDelayPCC_update x_BranchDelayPCC s) = isUnpredictable s"
    and "isUnpredictable (setPCC x_PCC s) = isUnpredictable s"
    and "isUnpredictable (setCAPR x_CAPR s) = isUnpredictable s"
    and "isUnpredictable (setSCAPR x_SCAPR s) = isUnpredictable s"
    and "isUnpredictable (setMEM x_MEM s) = isUnpredictable s"
    and "isUnpredictable (the_MEM_update x_the_MEM s) = isUnpredictable s"
    and "isUnpredictable (setBranchTo x_BranchTo s) = isUnpredictable s"
    and "isUnpredictable (setBranchDelay x_BranchDelay s) = isUnpredictable s"
    and "isUnpredictable (c_state_update x_c_state s) = isUnpredictable s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma isUnpredictable_raise'exception [simp]:
  shows "isUnpredictable (StatePart (raise'exception (UNPREDICTABLE v)) s)"
unfolding isUnpredictable_def raise'exception_exception Let_def
by simp

lemma isUnpredictable_exception_update [simp]:
  shows "isUnpredictable (s\<lparr>exception := v\<rparr>) = (v \<noteq> NoException)"
unfolding isUnpredictable_def
by simp

lemma isUnpredictable_setExceptionSignalled [simp]:
  shows "isUnpredictable (setExceptionSignalled v s) = isUnpredictable s"
unfolding isUnpredictable_def
by simp

subsection \<open>@{term MakePartial}\<close>

definition MakePartial :: "(state \<Rightarrow> 'a \<times> state) \<Rightarrow> state \<Rightarrow> 'a option \<times> state" where
  "MakePartial m \<equiv> 
   bind m
        (\<lambda>v. bind (read_state getExceptionSignalled)
        (\<lambda>ex. bind (read_state isUnpredictable)
        (\<lambda>unpred. return (if ex \<or> unpred then None else Some v))))"

lemma ValuePartMakePartial_from_PrePost:
  assumes "\<And>x. PrePost (return x =\<^sub>b read_state f)
                        m
                        (\<lambda>v. bind (read_state getExceptionSignalled)
                                  (\<lambda>ex. bind (read_state isUnpredictable)
                                  (\<lambda>unpred. return (x = (if ex \<or> unpred then None else Some v)))))"
  shows "ValuePart (MakePartial m) = f"
proof 
  fix s :: state
  show "ValuePart (MakePartial m) s = f s"
    using assms[where x="f s", THEN PrePostE[where s=s]]
    unfolding MakePartial_def
    by (simp add: ValueAndStatePart_simp)
qed

lemma ValuePartMakePartial_defined:
  assumes not_ex: "\<not> getExceptionSignalled (StatePart m s)"
      and not_unpred: "\<not> isUnpredictable (StatePart m s)"
  shows "ValuePart (MakePartial m) s = Some (ValuePart m s)"
using not_ex not_unpred
unfolding MakePartial_def  
unfolding monad_def Let_def ValuePart_def StatePart_def
by strong_cong_simp

section \<open>Address translation\<close>

lemma check_cca_isUnpredictable:
  shows "isUnpredictable (StatePart (check_cca v) s) =
         (v = 0 \<or> v = 1 \<or> v = 7 \<or> isUnpredictable s)"
unfolding check_cca_alt_def
by simp

lemma AddressTranslation_isUnpredictable:
  shows "IsInvariant (read_state isUnpredictable) (AddressTranslation v)"
unfolding AddressTranslation_alt_def 
by (PrePost simp: check_cca_isUnpredictable)

lemma AddressTranslation_getExceptionSignalled:
  shows "IsInvariant (read_state getExceptionSignalled) (AddressTranslation v)"
unfolding AddressTranslation_alt_def
by PrePost

lemma DefinedAddressTranslation_read_only_aux:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b
                    read_state isUnpredictable \<or>\<^sub>b
                    p)
                   (AddressTranslation v)"
unfolding AddressTranslation_alt_def check_cca_alt_def
by PrePost

lemma DefinedAddressTranslation_read_only:
  assumes "\<not> getExceptionSignalled (StatePart (AddressTranslation v) s)"
      and "\<not> isUnpredictable (StatePart (AddressTranslation v) s)"
  shows "StatePart (AddressTranslation v) s = s"
using assms
using DefinedAddressTranslation_read_only_aux[
        where p="read_state (\<lambda>s'. s' = s)" and v=v,
        THEN PrePostE[where s=s]]
by (simp add: ValueAndStatePart_simp)

subsection \<open>@{term PartialAddressTranslation}\<close>

definition AddressTranslationPartial where
  "AddressTranslationPartial v \<equiv> MakePartial (AddressTranslation v)"

abbreviation "getAddressTranslationPartial v \<equiv> ValuePart (AddressTranslationPartial v)"

text \<open>The following should be a schematic goal where the entire right side of the equation is the
schematic variable. But, for some reason, auto cannot figure out how to instantiate \<open>?x\<close> if it tries
to prove \<open>?x s = term\<close> where \<open>term\<close> contains occurrences of \<open>s\<close>. So for the moment we spell it out
for auto, and hope that we can remove this at some point.\<close>

lemma getAddressTranslationPartial_alt_def:
  shows "getAddressTranslationPartial a = 
         (\<lambda>s. (case a of (x1, x2) \<Rightarrow> 
               case getCheckSegment x1 s of (x1a, x2a) \<Rightarrow> 
               if x2a 
               then case x1a 
                    of None \<Rightarrow> (case getLookupTLB (slice 62 x1, slice 13 x1) s 
                                of [] \<Rightarrow> None
                                | [x1a] \<Rightarrow> (case checkMask (TLBEntry.Mask (snd x1a)) 
                                            of None \<Rightarrow> None
                                             | Some x \<Rightarrow> (case if x1 !! x 
                                                               then (S1 (snd x1a), L1 (snd x1a), PFN1 (snd x1a), C1 (snd x1a), D1 (snd x1a), V1 (snd x1a))
                                                               else (S0 (snd x1a), L0 (snd x1a), PFN0 (snd x1a), C0 (snd x1a), D0 (snd x1a), V0 (snd x1a)) 
                                                          of (x1b, x1c, x1d, x1e, x1f, x2a) \<Rightarrow> 
                                                          if x2a 
                                                          then if \<not> x1f \<and> x2 = STORE then None
                                                               else if x1e = 0 \<or> x1e = 1 \<or> x1e = 7 then None
                                                               else if getExceptionSignalled s \<or> isUnpredictable s then None
                                                               else Some ((ucast x1d AND ucast (word_cat (65535::16 word) (NOT TLBEntry.Mask (snd x1a))::28 word) << 12) OR
                                                                           ucast x1 AND ucast (word_cat (TLBEntry.Mask (snd x1a)) (4095::12 word)::24 word),
                                                                          x1e, x1b, x1c)
                                                          else None))
                                | x1a # x1 # x \<Rightarrow> Map.empty x)
                    | Some (x1, x2a) \<Rightarrow> if x2a = 0 \<or> x2a = 1 \<or> x2a = 7 then None 
                                        else if getExceptionSignalled s \<or> isUnpredictable s then None 
                                        else Some (x1, x2a, False, False)
               else None))"
unfolding AddressTranslationPartial_def AddressTranslation_alt_def check_cca_alt_def
by (intro ValuePartMakePartial_from_PrePost)
   (PrePost simp: all_distrib[where h="\<lambda>x. _ = x", THEN sym])

lemma Commute_getAddressTranslationPartial [Commute_compositeI]:
  assumes "\<And>v. Commute (read_state (getCheckSegment v)) m"
      and "\<And>v. Commute (read_state (getLookupTLB v)) m"
      and "\<And>v. Commute (read_state getExceptionSignalled) m"
      and "\<And>v. Commute (read_state isUnpredictable) m"
  shows "Commute (read_state (getAddressTranslationPartial a)) m"
using assms
unfolding getAddressTranslationPartial_alt_def Commute_def
by (strong_cong_simp add: ValueAndStatePart_simp)

lemma getAddressTranslationPartial_defined:
  assumes "\<not> getExceptionSignalled (StatePart (AddressTranslation v) s)"
      and "\<not> isUnpredictable (StatePart (AddressTranslation v) s)"
  shows "getAddressTranslationPartial v s = Some (ValuePart (AddressTranslation v) s)"
unfolding AddressTranslationPartial_def
using ValuePartMakePartial_defined assms
by metis

subsection \<open>@{term getPhysicalAddress}\<close>

definition PhysicalAddress :: 
  "VirtualAddress \<times> AccessType \<Rightarrow> state \<Rightarrow> PhysicalAddress option \<times> state" where
  "PhysicalAddress v \<equiv> 
   bind (read_state (getAddressTranslationPartial v))
        (\<lambda>x. return (case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fst y)))"

abbreviation "getPhysicalAddress v \<equiv> ValuePart (PhysicalAddress v)"

lemma PhysicalAddress_read_only [simp]:
  shows "StatePart (PhysicalAddress v) = (\<lambda>s. s)"
unfolding PhysicalAddress_def
by (simp add: ValueAndStatePart_simp) 

lemma Commute_PhysicalAddress [Commute_compositeI]:
  assumes "\<And>v. Commute (read_state (getAddressTranslationPartial v)) m"
  shows "Commute (PhysicalAddress a) m"
using assms
unfolding PhysicalAddress_def Commute_def
by (strong_cong_simp add: ValueAndStatePart_simp)

lemma getPhysicalAddress_simps [simp]:
  shows "getPhysicalAddress v (BranchToPCC_update x_BranchToPCC s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (BranchDelayPCC_update x_BranchDelayPCC s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (the_MEM_update x_the_MEM s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setPCC x_PCC s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setCAPR x_CAPR s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setSCAPR x_SCAPR s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setMEM x_MEM s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setBranchTo x_BranchTo s) = getPhysicalAddress v s"
    and "getPhysicalAddress v (setBranchDelay x_BranchDelay s) = getPhysicalAddress v s"
by (rule Commute_read_state_update_stateE, Commute)+

lemma getPhysicalAddress_defined:
  assumes "\<not> getExceptionSignalled (StatePart (AddressTranslation v) s)"
      and "\<not> isUnpredictable (StatePart (AddressTranslation v) s)"
  shows "getPhysicalAddress v s = Some (fst (ValuePart (AddressTranslation v) s))"
unfolding PhysicalAddress_def
using getAddressTranslationPartial_defined[OF assms]
by (simp add: ValueAndStatePart_simp)

definition getPhysicalAddressFunc :: "state \<Rightarrow> VirtualAddress \<times> AccessType \<Rightarrow> 
                                      PhysicalAddress option" where
  "getPhysicalAddressFunc s \<equiv> \<lambda>v. getPhysicalAddress v s"

lemma Commute_getPhysicalAddressFunc [Commute_compositeI]: 
  assumes "\<And>a. Commute (read_state (getPhysicalAddress a)) m"
  shows "Commute (read_state getPhysicalAddressFunc) m"
using assms
unfolding getPhysicalAddressFunc_def Commute_def
by auto

subsection \<open>@{term getPhysicalAddresses}\<close>

definition getPhysicalAddresses :: "VirtualAddress set \<Rightarrow> AccessType \<Rightarrow> 
                                    state \<Rightarrow> PhysicalAddress set" where
  "getPhysicalAddresses vAddrs t s \<equiv> 
   {pAddr. \<exists>vAddr \<in> vAddrs. getPhysicalAddress (vAddr, t) s = Some pAddr}"

lemma Commute_getPhysicalAddresses [Commute_compositeI]: 
  assumes "\<And>a. Commute (read_state (getPhysicalAddress (a, t))) m"
  shows "Commute (read_state (getPhysicalAddresses addrs t)) m"
using assms
unfolding getPhysicalAddresses_def Commute_def
by auto

lemma getPhysicalAddressesI [intro?]:
  assumes "getPhysicalAddress (virtualAddress, t) s = Some a"
      and "virtualAddress \<in> addrs"
  shows "a \<in> getPhysicalAddresses addrs t s"
using assms
unfolding getPhysicalAddresses_def
by auto

lemma getPhysicalAddressesE [elim]:
  assumes "a \<in> getPhysicalAddresses addrs t s"
  obtains virtualAddress 
    where "getPhysicalAddress (virtualAddress, t) s = Some a"
      and "virtualAddress \<in> addrs" 
using assms
unfolding getPhysicalAddresses_def
by auto

lemma getPhysicalAddresses_le:
  assumes "addrs \<subseteq> addrs'"
  shows "getPhysicalAddresses addrs t s \<subseteq> getPhysicalAddresses addrs' t s"
using assms
unfolding getPhysicalAddresses_def
by auto

lemmas getPhysicalAddresses_le_subsetD [elim] =
  subsetD[OF getPhysicalAddresses_le]

lemma getPhysicalAddresses_distrib_union:
  shows "getPhysicalAddresses (addrs \<union> addrs') t s =
         (getPhysicalAddresses addrs t s \<union> getPhysicalAddresses addrs' t s)"
unfolding getPhysicalAddresses_def
by auto

lemma getPhysicalAddresses_distrib_Union:
  shows "getPhysicalAddresses (\<Union>addrsSet) t s =
         (\<Union>addrs\<in>addrsSet. getPhysicalAddresses addrs t s)"
unfolding getPhysicalAddresses_def
by auto

lemma getPhysicalAddresses_eqI_getPhysicalAddress:
  assumes "\<And>a. getPhysicalAddress a s' = getPhysicalAddress a s"
  shows "getPhysicalAddresses addrs t s' = getPhysicalAddresses addrs t s"
using assms
unfolding getPhysicalAddresses_def
by simp

subsection \<open>@{const PrePost} of @{const AddressTranslation}\<close>

lemma PrePost_AddressTranslation:
  defines "h \<equiv> read_state getExceptionSignalled \<or>\<^sub>b read_state isUnpredictable"
  assumes "IsInvariant p (AddressTranslation v)"
  shows "PrePost (bind (read_state (getPhysicalAddress v)) (case_option p q))
                 (AddressTranslation v)
                 (\<lambda>x. (\<not>\<^sub>b h \<or>\<^sub>b p) \<and>\<^sub>b (h \<or>\<^sub>b q (fst x)))" 
  (is "PrePost ?pre _ ?post")
proof (intro PrePostI)
  fix s
  assume "ValuePart ?pre s"
  thus "ValuePart (bind (AddressTranslation v) ?post) s"
    using PrePostE[OF assms(2), where s=s]
    using DefinedAddressTranslation_read_only[where v=v and s=s]
    unfolding h_def 
    unfolding PhysicalAddress_def AddressTranslationPartial_def MakePartial_def
    by (auto simp: ValueAndStatePart_simp 
             split: option.splits
             dest!: if_split[where P="\<lambda>x. x = _", THEN iffD1])
qed

lemma PrePost_DefinedAddressTranslation:
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b 
                  read_state isUnpredictable \<or>\<^sub>b 
                  bind (read_state (getPhysicalAddress v))
                       (\<lambda>a. case a of None \<Rightarrow> return True 
                                    | Some x \<Rightarrow> p x))
                 (AddressTranslation v)
                 (\<lambda>x. read_state getExceptionSignalled \<or>\<^sub>b 
                      read_state isUnpredictable \<or>\<^sub>b 
                      p (fst x))"
by (rule PrePostIE[OF 
             PrePost_weakest_pre_disj[OF 
                 PrePost_AddressTranslation[where v=v and p="return True" and q=p]
                 PrePost_weakest_pre_disj[OF 
                      AddressTranslation_isUnpredictable
                      AddressTranslation_getExceptionSignalled]]])
   (auto simp: ValueAndStatePart_simp cong: cong)

subsection \<open>Lower and upper bits\<close>

lemma CheckSegment_ucast12:
  assumes "getCheckSegment addr s = (Some (addr', x), y)"
  shows "(ucast addr'::12 word) = ucast addr"
using assms
unfolding CheckSegment_alt_def 
by (auto simp: ValueAndStatePart_simp ucast_minus_down
         dest!: if_split[where P="\<lambda>x. x = _", THEN iffD1])

lemma CheckSegment_and_not_mask:
  shows "getCheckSegment (vAddr AND NOT mask 12) s =
         (case getCheckSegment vAddr s 
            of (None, b) \<Rightarrow> (None, b)
             | (Some (addr, x), b) \<Rightarrow> (Some (addr AND NOT mask 12, x), b))"
proof -
  have *: "(word_cat (x::11 word) (0::29 word)::40 word) AND NOT mask 12 = 
           word_cat (x::11 word) (0::29 word)" for x
    by (intro word_eqI) (simp add: word_size nth_word_cat word_ops_nth_size)
  have [simp]: "(1097901015040::40 word) AND NOT mask 12 = 1097901015040"
    using *[where x=2045]
    unfolding word_cat_def bin_cat_def
    by simp
  have [simp]: "(1097364144128::40 word) AND NOT mask 12 = 1097364144128"
    using *[where x=2044]
    unfolding word_cat_def bin_cat_def
    by simp
  show ?thesis
    unfolding CheckSegment_alt_def
    using not_mask_eq_minus[where x="ucast vAddr::40 word" and y=1097901015040 and n=12]
    using not_mask_eq_minus[where x="ucast vAddr::40 word" and y=1097364144128 and n=12]
    by (strong_cong_simp add:
          ValueAndStatePart_simp
          slice_and slice_not 
          ucast_and ucast_not
          all_distrib[where h="\<lambda>x. case x of (x, y) \<Rightarrow> _ x y"]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=1099511627776]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=4611686018427387904]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=4611687117939015680]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=13835058055282163712]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=13835059152646307840]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=18446744072098938880]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=18446744072635809792]
          less_left_and_not_mask[where x=vAddr and 'b=12 and y=18446744073172680704]
          le_right_and_not_mask[where y=vAddr and 'b=12 and x=4611686018427387904]
          le_right_and_not_mask[where y=vAddr and 'b=12 and x=9223372036854775808]
          le_right_and_not_mask[where y=vAddr and 'b=12 and x=18446744071562067968]
          le_right_and_not_mask[where y=vAddr and 'b=12 and x=18446744072635809792])
qed

lemma getPhysicalAddress_ucast12:
  assumes "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
  shows "(ucast pAddr::12 word) = ucast vAddr"
proof -
  have [simp]: "(4095::12 word) = mask 12"
    unfolding mask_def by simp
  have "Some pAddr = getPhysicalAddress (vAddr, accessType) s \<longrightarrow>
        (ucast pAddr::12 word) = ucast vAddr"
    unfolding PhysicalAddress_def getAddressTranslationPartial_alt_def
    by (strong_cong_simp
             add: ValueAndStatePart_simp
                  ucast_or ucast_and ucast_shiftr ucast_shiftl
                  all_distrib[where h="\<lambda>x. Some _ = x \<longrightarrow> _"]
                  all_distrib[where h="\<lambda>x. case x of None \<Rightarrow> True | Some y \<Rightarrow> _ y"])
       (auto intro: CheckSegment_ucast12)
  thus ?thesis
    using assms by simp
qed 

lemma getPhysicalAddress_vAddr_and_mask_12:
  assumes "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
  shows "vAddr AND mask 12 = ucast pAddr AND mask 12"
proof (intro word_eqI impI, unfold word_size)
  fix n
  assume "n < LENGTH(64)"
  thus "(vAddr AND mask 12) !! n = ((ucast pAddr::64 word) AND mask 12) !! n"
    using test_bit_cong[where x=n, OF getPhysicalAddress_ucast12[OF assms]]
    by (auto simp: nth_ucast word_ao_nth word_size)
qed

lemma getPhysicalAddress_pAddr_and_mask_12:
  assumes "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
  shows "pAddr AND mask 12 = ucast vAddr AND mask 12"
proof (intro word_eqI impI, unfold word_size)
  fix n
  assume "n < LENGTH(40)"
  thus "(pAddr AND mask 12) !! n = ((ucast vAddr::40 word) AND mask 12) !! n"
    using test_bit_cong[where x=n, OF getPhysicalAddress_ucast12[OF assms]]
    by (auto simp: nth_ucast word_ao_nth word_size)
qed

lemma getPhysicalAddress_and_not_mask:
  shows "getPhysicalAddress (vAddr AND NOT mask 12, accessType) s = 
         (case getPhysicalAddress (vAddr, accessType) s 
            of None \<Rightarrow> None
             | Some pAddr \<Rightarrow> Some (pAddr AND NOT mask 12))"
proof -
  have [simp]:  "(case checkMask x of None \<Rightarrow> f
                                    | Some i \<Rightarrow> if (w AND NOT mask 12) !! i then g else h) =
                 (case checkMask x of None \<Rightarrow> f
                                    | Some i \<Rightarrow> if w !! i then g else h)"
  for x and f g h :: 'a and w :: "'b::len word"
    proof (cases "checkMask x")
      case (Some i)
      hence "12 \<le> i"
        unfolding checkMask_def
        by (auto split: if_splits)
      hence "(w AND NOT mask 12) !! i = w !! i"
        using test_bit_size[where w=w and n=i]
        by (auto simp: word_ops_nth_size word_ao_nth word_size)
      thus ?thesis 
        using Some
        by simp
    qed simp
  have [simp]: "(x AND NOT mask 12) AND y = (x AND y) AND NOT mask 12" for x y :: "'b::len word"
    by (metis bitwise_semilattice_inf.inf_assoc word_bool_alg.conj.commute)
  show ?thesis
    unfolding PhysicalAddress_def getAddressTranslationPartial_alt_def
    by (strong_cong_simp add: 
              ValueAndStatePart_simp
              slice_and slice_not 
              ucast_and ucast_not 
              CheckSegment_and_not_mask[where vAddr=vAddr and s=s]
              all_distrib[where h="\<lambda>x. case x of (x, y) \<Rightarrow> _ x y"]
              all_distrib[where h="\<lambda>x. case x of None \<Rightarrow> _ | Some y \<Rightarrow> _ y"]
              word_bool_alg.conj_disj_distrib2[where x="NOT mask 12"]
              word_bool_alg.conj_assoc[where x="NOT mask 12"])
       (auto split: option.splits prod.splits)
qed

lemma getPhysicalAddress_split:
  shows "getPhysicalAddress (vAddr, accessType) s = 
         (case getPhysicalAddress (vAddr AND NOT mask 12, accessType) s 
            of None \<Rightarrow> None
             | Some pAddr \<Rightarrow> Some (pAddr OR (ucast vAddr AND mask 12)))"
proof (cases "getPhysicalAddress (vAddr, accessType) s")
  case None
  thus ?thesis 
    unfolding getPhysicalAddress_and_not_mask
    by (auto split: option.splits)
next
  case (Some pAddr)
  have "ucast vAddr AND mask 12 = pAddr AND mask 12"
    using getPhysicalAddress_ucast12[OF Some, THEN test_bit_cong]
    by (intro word_eqI) (auto simp: word_size word_ao_nth nth_ucast)
  thus ?thesis
    using Some
    unfolding getPhysicalAddress_and_not_mask
    by (auto split: option.splits)
qed

subsection \<open>Translate nearby addresses\<close>

lemma TranslateNearbyAddress:
  fixes vAddr :: VirtualAddress
  fixes pAddr' :: PhysicalAddress
  fixes accessLength :: "65 word"
  assumes v_upper: "ucast vAddr + accessLength \<le> ucast (getBase cap) + ucast (getLength cap)"
      and v_lower: "getBase cap \<le> vAddr"
      and length: "1 \<le> accessLength" "accessLength \<le> 32"
      and alignment: "unat vAddr mod 32 + unat accessLength \<le> 32"
      and pAddr: "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
      and pAddr': "pAddr' \<in> MemSegment pAddr (ucast accessLength)"
  obtains vAddr' where
    "getPhysicalAddress (vAddr', accessType) s = Some pAddr'" and
    "vAddr' \<in> MemSegmentCap cap"
proof -

  -- \<open>We rewrite @{term accessLength} to a smaller length word.\<close>
  define accessLength' :: "5 word" where "accessLength' = ucast (accessLength - 1)"
  have accessLength_alt: "accessLength = ucast accessLength' + 1"
    using less_mask_eq[where x="accessLength - 1" and n=5] length
    using uint_minus_simple_alt[where x=accessLength and y=1]
    unfolding accessLength'_def
    unfolding word_less_def word_le_def 
    by auto

  -- \<open>We prove that adding @{term accessLength'} to @{term pAddr} does not cross an alignment 
      boundary.\<close>
  have "uint pAddr mod 32 + uint accessLength' < 32"
    proof -
      have "unat pAddr mod 32 + unat accessLength' < 32"
        using alignment
        using arg_cong[where f="\<lambda>x. unat (ucast x::5 word)", 
                       OF getPhysicalAddress_ucast12[OF pAddr]]
        unfolding accessLength_alt
        by (simp add: unat_and_mask)
      from transfer_int_nat_relations(2)[THEN iffD2, OF this]
      show ?thesis 
        unfolding uint_nat
        by (simp add: zmod_int)
    qed

  -- \<open>Therefore \<open>pAddr + accessLength'\<close> does not wrap.\<close>
  have pAddr_no_wrap: "uint pAddr + uint accessLength' < 2 ^ LENGTH(40)"
    proof -
      have "uint pAddr div 32 \<le> 34359738367"
        using word_and_mask_and_not_mask_size[where n=5 and m=40 and x=pAddr, simplified]
        unfolding word_le_def
        by (auto simp: uint_and_not_mask)
      from this[THEN mult_left_mono[where c=32], THEN add_left_mono[where c="uint pAddr mod 32"]]
      have "uint pAddr \<le> 2 ^ 40 - 32 + uint pAddr mod 32"
        by simp
      thus ?thesis
        using `uint pAddr mod 32 + uint accessLength' < 32`
        unfolding word_le_def
        by auto
    qed

  -- \<open>We rewrite @{term pAddr'} as @{term pAddr} plus a delta.\<close>
  define pDelta where "pDelta \<equiv> pAddr' - pAddr"
  have pAddr'_alt: "pAddr' = pAddr + pDelta"
    unfolding pDelta_def by simp

  -- \<open>We prove an upper bound of @{term pDelta}.\<close>
  have pDelta_upper: "pDelta \<le> ucast accessLength'"
    proof -
      have "pDelta < ucast accessLength' + 1"
        using MemSegment_memberE[OF pAddr'] pAddr_no_wrap
        unfolding pDelta_def accessLength_alt
        by (simp add: uint_and_mask)
      thus ?thesis
        using inc_le leD le_less_linear 
        by blast
    qed

  -- \<open>Therefore bits 12...39 of @{term pDelta} are zero.\<close>
  have pDelta_upper [simp]: "pDelta AND NOT mask 12 = 0" and
       pDelta_lower [simp]: "pDelta AND mask 12 = pDelta"
    proof -
      have "pDelta \<le> mask 5"
        using uint_lt[where w=accessLength'] pDelta_upper
        unfolding word_le_def
        unfolding mask_def
        by auto
      from le_and_not_mask[where n=12, OF this]
      show "pDelta AND NOT mask 12 = 0" by simp
      thus "pDelta AND mask 12 = pDelta"
        unfolding word_minus_word_and_not_mask[THEN sym]
        by (simp del: word_minus_word_and_not_mask)
  qed

  -- \<open>We prove that adding @{term pDelta} to @{term pAddr} does not cross an alignment 
      boundary.\<close>
  have "uint pAddr mod 32 + uint pDelta < 32"
    using `pDelta \<le> ucast accessLength'` 
    using `uint pAddr mod 32 + uint accessLength' < 32`
    unfolding word_le_def
    by simp

  -- \<open>Therefore, adding their lowest 12 bits does not overflow.\<close>
  have pAddr_plus_pDelta_mask12: "(pAddr AND mask 12) + (pDelta AND mask 12) \<le> mask 12"
    proof -
      have [simp]: "(4064::40 word) AND mask 12 = 4064"
        unfolding mask_def by simp
      have [simp]: "pAddr AND mask 5 \<le> (pAddr AND mask 5) + 4064"
        using plus_word_and_mask_no_wrap[where x="pAddr AND mask 5" and y=4064 and n=12]
        by simp
      have [simp]: "uint ((pAddr AND mask 5) + 4064) = uint pAddr mod 32 + 4064"
        by (simp add: uint_plus_simple uint_and_mask)
      have "(pAddr AND mask 12) = 
            ((pAddr AND mask 12) AND NOT mask 5) + ((pAddr AND mask 12) AND mask 5)"
        by (simp del: word_and_mask_and_mask)
      also have "... \<le> (pAddr AND mask 5) + 4064"
        using word_plus_mono_right[where x="pAddr AND mask 5",
                OF word_and_mask_and_not_mask_size[where n=5 and m=12 and x=pAddr, simplified]]
        by (auto simp: add.commute[where a="(pAddr AND mask 12) AND NOT mask 5" 
                                     and b="pAddr AND mask 5"])
      finally have "uint (pAddr AND mask 12) + uint (pDelta AND mask 12) < 2 ^ 12"
        unfolding word_le_def
        using `uint pAddr mod 32 + uint pDelta < 32` add_left_mono
        by (auto simp add: uint_and_mask)
      thus ?thesis
        unfolding word_le_def
        by (simp del: pDelta_lower add: uint_mask)
    qed

  -- \<open>We prove equalities of the lower and upper bits of @{term pAddr'}.\<close>
  have pAddr'_not_mask: "pAddr' AND NOT mask 12 = pAddr AND NOT mask 12"
    unfolding pAddr'_alt word_plus_and_not_mask[OF pAddr_plus_pDelta_mask12]
    by simp
  have pAddr'_mask: "pAddr' AND mask 12 = (pAddr AND mask 12) + pDelta"
    unfolding pAddr'_alt word_plus_and_mask[OF pAddr_plus_pDelta_mask12]
    by simp

  -- \<open>We prove a lower bound for the lower bits of @{term pAddr'}.\<close>
  have pAddr'_mask_lower: "pAddr AND mask 12 \<le> pAddr' AND mask 12"
    using plus_word_and_mask_no_wrap[where x=pAddr and y=pDelta and n=12]
    unfolding pAddr'_mask
    by simp

  -- \<open>We define \<open>vAddr'\<close>.\<close>
  define vAddr' where "vAddr' \<equiv> (vAddr AND NOT mask 12) OR (ucast pAddr' AND mask 12)"
  have vAddr'_alt: "vAddr' = (vAddr AND NOT mask 12) + (ucast pAddr' AND mask 12)"
    unfolding vAddr'_def
    unfolding word_plus_and_or[where x="vAddr AND NOT mask 12", THEN sym]
    by simp

  -- \<open>We prove that @{term vAddr'} translates to @{term pAddr'}.\<close>
  have vAddr'_trans: "getPhysicalAddress (vAddr', accessType) s = Some pAddr'"
    proof -
      have "getPhysicalAddress (vAddr AND NOT mask 12, accessType) s = 
            Some (pAddr AND NOT mask 12)"
        unfolding getPhysicalAddress_and_not_mask 
        using pAddr
        by auto
      thus ?thesis
        unfolding getPhysicalAddress_split[where vAddr=vAddr'] 
        unfolding vAddr'_def 
        by (auto simp: ucast_and ucast_or ucast_not 
                       pAddr'_not_mask[THEN sym]
                       word_bool_alg.conj.assoc
                       word_bool_alg.conj_disj_distrib2
                 split: option.splits)
    qed

  -- \<open>We prove a lower bound of @{term vAddr'}.\<close>
  have vAddr'_lower: "getBase cap \<le> vAddr'"
    proof -
      have "vAddr = (vAddr AND NOT mask 12) + (ucast pAddr AND mask 12)"
        using getPhysicalAddress_vAddr_and_mask_12[where pAddr=pAddr, THEN sym] pAddr
        by simp
      also have "... \<le> (vAddr AND NOT mask 12) + (ucast pAddr' AND mask 12)"
        using pAddr'_mask_lower
        unfolding word_le_def uint_word_and_not_mask_plus_word_and_mask
        by (simp add: uint_and_mask)
      also have "... = vAddr'"
        unfolding vAddr'_alt
        by simp
      finally show ?thesis
        using v_lower by auto
    qed

  -- \<open>We prove an upper bound of @{term vAddr'}.\<close>
  have vAddr'_upper: "ucast vAddr' + (1::65 word) \<le> ucast (getBase cap) + ucast (getLength cap)"
    proof -
      have pAddr'_mask_upper: "pAddr' AND mask 12 \<le> (pAddr AND mask 12) + ucast accessLength'"
        using word_plus_mono_right[where y=pDelta, 
                OF _ plus_word_and_mask_no_wrap[where x=pAddr and y="ucast accessLength'" and n=12]]
        using `pDelta \<le> ucast accessLength'`
        unfolding pAddr'_mask
        by simp
      have "pAddr AND mask 12 \<le> (pAddr AND mask 12) + ucast accessLength'"
        using pAddr'_mask_lower pAddr'_mask_upper
        by simp
      from uint_plus_simple[OF this]
      have "uint vAddr' \<le> 
            uint (vAddr AND NOT mask 12) + uint (pAddr AND mask 12) + uint accessLength'"
        using pAddr'_mask_upper
        unfolding vAddr'_alt
        unfolding word_le_def
        by (simp add: uint_and_mask uint_and_not_mask
                      uint_word_and_not_mask_plus_word_and_mask)
      also have "... = uint vAddr + uint accessLength'"
        using arg_cong[where f=uint, OF getPhysicalAddress_vAddr_and_mask_12[OF pAddr, THEN sym]]
        by (simp add: uint_and_mask uint_and_not_mask
                      uint_word_and_not_mask_plus_word_and_mask)
      finally show ?thesis
        using v_upper
        unfolding word_le_def accessLength_alt add.assoc[THEN sym]
        by simp
    qed

  -- \<open>We prove that @{term vAddr'} lies in the memory segment of @{term cap}.\<close>
  have "vAddr' \<in> MemSegmentCap cap"
    using vAddr'_lower vAddr'_upper
    by (intro MemSegment_memberI_65word) auto

  thus ?thesis
    using vAddr'_trans that
    by metis
qed

lemma TranslateNearbyAddress_LegacyInstructions:
  fixes vAddr :: VirtualAddress
  fixes pAddr' :: PhysicalAddress
  fixes accessLength :: "3 word"
  assumes v_upper: "ucast vAddr + ucast accessLength + (1::65 word) \<le> 
                    ucast (getBase cap) + ucast (getLength cap)"
      and v_lower: "getBase cap \<le> vAddr"
      and alignment: "unat vAddr mod 8 + unat accessLength < 8"
      and pAddr: "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
      and pAddr': "pAddr' \<in> MemSegment pAddr (ucast accessLength + 1)"
  obtains vAddr' where
    "getPhysicalAddress (vAddr', accessType) s = Some pAddr'" and
    "vAddr' \<in> MemSegmentCap cap"
proof -
  define accessLength' :: "65 word" where "accessLength' \<equiv> ucast accessLength + 1"
  have alignment': "unat vAddr mod 32 + unat accessLength' \<le> 32"
    proof -
      have "(8::nat) dvd 32" by arith
      have "(unat vAddr mod 32) div 8 \<le> 3" by auto
      from this[THEN mult_left_mono[where c=8], 
                THEN add_left_mono[where c="(unat vAddr mod 32) mod 8"]]
      have "unat vAddr mod 32 \<le> 24 + (unat vAddr mod 32 mod 8)"
        by simp
      hence "unat vAddr mod 32 \<le> 24 + (unat vAddr mod 8)"
        unfolding mod_mod_cancel[OF `(8::nat) dvd 32`]
        by simp
      thus ?thesis
        unfolding accessLength'_def
        using alignment
        by auto
    qed
  have v_upper': "ucast vAddr + accessLength' \<le> ucast (getBase cap) + ucast (getLength cap)"
    using v_upper
    unfolding accessLength'_def
    by (simp add: add.assoc)
  have length: "1 \<le> accessLength'" "accessLength' \<le> 32"
    using uint_lt[where w=accessLength]
    unfolding accessLength'_def word_le_def
    by auto
  show ?thesis
    using TranslateNearbyAddress[OF v_upper' v_lower length alignment' pAddr]
    using pAddr' that
    unfolding accessLength'_def
    by auto
qed

lemma TranslateNearbyAddress_CapAligned:
  fixes vAddr :: VirtualAddress
  fixes pAddr' :: PhysicalAddress
  assumes v_upper: "ucast vAddr + (32::65 word) \<le> 
                    ucast (getBase cap) + ucast (getLength cap)"
      and v_lower: "getBase cap \<le> vAddr"
      and alignment: "isCapAligned vAddr"
      and pAddr: "getPhysicalAddress (vAddr, accessType) s = Some pAddr"
      and pAddr': "pAddr' \<in> MemSegment pAddr 32"
  obtains vAddr' where
    "getPhysicalAddress (vAddr', accessType) s = Some pAddr'" and
    "vAddr' \<in> MemSegmentCap cap"
proof -
  define accessLength' :: "65 word" where "accessLength' \<equiv> 32"
  have v_upper': "ucast vAddr + accessLength' \<le> ucast (getBase cap) + ucast (getLength cap)"
    using v_upper
    unfolding accessLength'_def
    by (simp add: add.commute)
  have "(ucast vAddr::5 word) = 0"
    using alignment
    unfolding isCapAligned_def
    by simp
  from arg_cong[where f=unat, OF this]
  have [simp]: "unat vAddr mod 32 = 0"
    by (simp add: unat_and_mask)
  have alignment': "unat vAddr mod 32 + unat accessLength' \<le> 32"
    unfolding accessLength'_def
    by auto
  show ?thesis
    using TranslateNearbyAddress[OF v_upper' v_lower _ _ alignment' pAddr]
    using pAddr' that
    unfolding accessLength'_def
    by auto
qed

section \<open>Fetch\<close>

subsection \<open>@{term PartialFetch}\<close>

definition FetchPartial where
  "FetchPartial \<equiv> MakePartial Fetch"

abbreviation "getFetchPartial \<equiv> ValuePart FetchPartial"

lemmas getFetchPartial_alt_def_aux =
  PrePost_AddressTranslation[
    where p="return (x = None)" and 
          q="\<lambda>y. bind (read_state (getReadInst y)) (\<lambda>z. return (x = Some (Some z)))",
    OF IsInvariant_constant] for x

schematic_goal getFetchPartial_alt_def:
  shows "getFetchPartial = ?x"
unfolding FetchPartial_def Fetch_alt_def
by (intro ValuePartMakePartial_from_PrePost)
   (PrePost intro: getFetchPartial_alt_def_aux[THEN PrePost_post_weakening]
            simp: all_distrib[where h="\<lambda>x. _ = x", THEN sym])

subsection \<open>@{term NextInstruction}\<close>

definition NextInstruction where
  "NextInstruction \<equiv> 
   bind (read_state getFetchPartial)
        (\<lambda>v. return (case v of None \<Rightarrow> None 
                             | Some None \<Rightarrow> None
                             | Some (Some w) \<Rightarrow> Some w))"

abbreviation "getNextInstruction \<equiv> ValuePart NextInstruction"

lemma NextInstruction_read_only [simp]:
  shows "StatePart NextInstruction = (\<lambda>s. s)"
unfolding NextInstruction_def
by (simp add: ValueAndStatePart_simp) 

lemma Commute_NextInstruction [Commute_compositeI]:
  assumes "Commute (read_state getPC) m"
      and "Commute (read_state getPCC) m"
      and "Commute (read_state getCP0Compare) m"
      and "Commute (read_state getCP0Count) m"
      and "Commute (read_state getCP0StatusIE) m"
      and "Commute (read_state getCP0StatusEXL) m"
      and "Commute (read_state getCP0StatusERL) m"
      and "Commute (read_state getCP0StatusIM) m"
      and "Commute (read_state getCP0CauseIP) m"
      and "Commute (read_state getExceptionSignalled) m"
      and "\<And>v. Commute (read_state (getPhysicalAddress v)) m"
      and "\<And>v. Commute (read_state (getReadInst v)) m"
  shows "Commute NextInstruction m"
using assms
unfolding NextInstruction_def getFetchPartial_alt_def Commute_def
by (strong_cong_simp add: ValueAndStatePart_simp)

subsection \<open>@{const PrePost} of @{const Fetch}\<close>

lemma PrePost_Fetch_getExceptionSignalled:
  shows "PrePost (return True)
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled
                              | Some w \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b
                                          \<not>\<^sub>b read_state getExceptionSignalled)"
unfolding Fetch_alt_def
by (PrePost intro: PrePost_DefinedAddressTranslation[where p="\<lambda>x. return True", 
                                                     THEN PrePost_post_weakening])

lemma PrePost_Fetch_aux:
  assumes "\<And>x. Commute p (update_state (setCP0CauseIP x))"
      and "\<And>x. Commute p (update_state (setCP0CauseTI x))"
      and "\<And>x. Commute p (ReadInst x)"
  shows "PrePost p
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> return True
                              | Some w \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p)"
unfolding Fetch_alt_def
by (PrePost intro: assms PrePost_DefinedAddressTranslation
                           [where p="\<lambda>x. p", THEN PrePost_post_weakening])

lemma PrePost_Fetch:
  assumes "\<And>x v. Commute (p x) (update_state (setCP0CauseIP v))"
      and "\<And>x v. Commute (p x) (update_state (setCP0CauseTI v))"
      and "\<And>x v. Commute (p x) (ReadInst v)"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled
                              | Some w \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p w)"
  (is "PrePost ?pre _ ?post")
proof (intro PrePostI)
  fix s
  assume "ValuePart ?pre s"
  thus "ValuePart (bind Fetch ?post) s"
    using PrePostE[where s=s, OF PrePost_Fetch_getExceptionSignalled]
    using PrePostE[where s=s, OF PrePost_Fetch_aux[OF assms]]
    unfolding NextInstruction_def FetchPartial_def MakePartial_def
    by (auto simp: ValueAndStatePart_simp split: option.splits if_splits)
qed

section \<open>Valid states\<close>

subsection \<open>Ghost state\<close>

definition EmptyGhostState where 
  "EmptyGhostState \<equiv>
   \<not>\<^sub>b read_state isUnpredictable \<and>\<^sub>b
   \<not>\<^sub>b read_state getExceptionSignalled \<and>\<^sub>b
   (read_state getBranchTo =\<^sub>b return None) \<and>\<^sub>b
   (read_state BranchToPCC =\<^sub>b return None)"

abbreviation "getEmptyGhostState \<equiv> ValuePart EmptyGhostState"

lemma EmptyGhostState_StatePart [simp]:
  shows "StatePart EmptyGhostState = (\<lambda>s. s)"
unfolding EmptyGhostState_def
by (simp add: ValueAndStatePart_simp)

lemma getEmptyGhostStateI [intro]:
  assumes "\<not> isUnpredictable s"
      and "\<not> getExceptionSignalled s"
      and "getBranchTo s = None"
      and "BranchToPCC s = None"
  shows "getEmptyGhostState s"
using assms
unfolding EmptyGhostState_def
by (simp add: ValueAndStatePart_simp)

lemma EmptyGhostStateE [elim!]:
  assumes "getEmptyGhostState s"
  shows "\<not> isUnpredictable s"
    and "\<not> getExceptionSignalled s"
    and "getBranchTo s = None"
    and "BranchToPCC s = None"
using assms
unfolding EmptyGhostState_def
by (simp_all add: ValueAndStatePart_simp)

definition NextWithGhostState where
  "NextWithGhostState =
   bind (update_state (currentInst_update Map.empty))
        (\<lambda>_. bind Fetch 
        (\<lambda>v. bind (update_state (currentInst_update (\<lambda>_. v)))
        (\<lambda>_. bind (read_state currentInst)
        (\<lambda>v. bind (case v of None \<Rightarrow> return () | Some w \<Rightarrow> Run (Decode w))
        (\<lambda>_. bind TakeBranch
        (\<lambda>_. bind (read_state getCP0Count) 
        (\<lambda>b. bind (update_state (setCP0Count (b + 1))) 
        (\<lambda>_. bind (read_state currentInst) 
        (\<lambda>v. update_state (lastInst_update (\<lambda>_. v)))))))))))"

lemma Next_NextWithGhostState:
  shows "Next = bind NextWithGhostState (\<lambda>_. update_state (setExceptionSignalled False))"
proof -
  have commutativity: 
       "bind (read_state getCP0Count) 
             (\<lambda>b. bind (update_state (setCP0Count (b + 1))) 
             (\<lambda>_. bind (read_state currentInst) 
             (\<lambda>v. bind (update_state (lastInst_update (\<lambda>_. v)))
             (\<lambda>_. update_state (setExceptionSignalled False))))) = 
        bind (update_state (setExceptionSignalled False)) 
             (\<lambda>_. bind (read_state getCP0Count) 
             (\<lambda>b. bind (update_state (setCP0Count (b + 1))) 
             (\<lambda>_. bind (read_state currentInst) 
             (\<lambda>v. update_state (lastInst_update (\<lambda>_. v))))))"
    unfolding monad_def Let_def
    by auto
  show ?thesis
    unfolding Next_alt_def NextWithGhostState_def
    by (simp add: commutativity bind_associativity)
qed

subsection \<open>Valid states\<close>

definition StateIsValid where 
  "StateIsValid =
   EmptyGhostState \<and>\<^sub>b
   read_state getCP0ConfigBE \<and>\<^sub>b
   \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
   (read_state getBranchDelay =\<^sub>b return None \<or>\<^sub>b
    read_state BranchDelayPCC =\<^sub>b return None)"

abbreviation "getStateIsValid \<equiv> ValuePart StateIsValid"

lemma StateIsValid_StatePart [simp]:
  shows "StatePart StateIsValid = (\<lambda>s. s)"
unfolding StateIsValid_def
by (simp add: ValueAndStatePart_simp)

lemma getStateIsValidI [intro]:
  assumes "getEmptyGhostState s"
      and "getCP0ConfigBE s"
      and "\<not> getCP0StatusRE s"
      and "getBranchDelay s = None \<or> BranchDelayPCC s = None"
  shows "getStateIsValid s"
using assms
unfolding StateIsValid_def is_some_def
by (auto simp: ValueAndStatePart_simp)

lemma StateIsValidE [elim!]:
  assumes "getStateIsValid s"
  shows "getEmptyGhostState s"
    and "getCP0ConfigBE s"
    and "\<not> getCP0StatusRE s"
using assms
unfolding StateIsValid_def
by (simp_all add: ValueAndStatePart_simp)

lemma StateIsValid_EmptyGhostStateE [elim!]:
  assumes "getStateIsValid s"
  shows "\<not> isUnpredictable s"
    and "\<not> getExceptionSignalled s"
    and "getBranchTo s = None"
    and "BranchToPCC s = None"
using StateIsValidE[OF assms]
by auto

section \<open>Semantics of unpredictable operations\<close>

definition UnpredictableNext :: "state \<Rightarrow> state set" where
  "UnpredictableNext s \<equiv> 
   {s' |s'. (\<forall>a. getMemCap a s' = getMemCap a s) \<and>
            (getPCC s' = getPCC s) \<and>
            (BranchDelayPCC s' = BranchDelayPCC s) \<and>
            (\<forall>cd. getCAPR cd s' = getCAPR cd s) \<and>
            (\<forall>cd. getSCAPR cd s' = getSCAPR cd s) \<and>
            (\<forall>vAddr. getPhysicalAddress vAddr s' = getPhysicalAddress vAddr s) \<and>
            getStateIsValid s'}"

lemma UnpredictableNextI [intro]:
  assumes "\<And>a. getMemCap a s' = getMemCap a s"
      and "getPCC s' = getPCC s"
      and "BranchDelayPCC s' = BranchDelayPCC s"
      and "\<And>cd. getCAPR cd s' = getCAPR cd s"
      and "\<And>cd. getSCAPR cd s' = getSCAPR cd s"
      and "\<And>vAddr. getPhysicalAddress vAddr s' = getPhysicalAddress vAddr s"
      and "getStateIsValid s'"
  shows "s' \<in> UnpredictableNext s"
using assms
unfolding UnpredictableNext_def
by auto

lemma UnpredictableNextE [elim!]:
  assumes "s' \<in> UnpredictableNext s"
  shows "getMemCap a s' = getMemCap a s"
    and "getPCC s' = getPCC s"
    and "BranchDelayPCC s' = BranchDelayPCC s"
    and "getCAPR cd s' = getCAPR cd s"
    and "getSCAPR cd' s' = getSCAPR cd' s"
    and "getStateIsValid s'"
using assms
unfolding UnpredictableNext_def
by (auto split: prod.splits)

lemma UnpredictableNextE_getMemData [elim!]:
  assumes "s' \<in> UnpredictableNext s"
  shows "getMemData a s' = getMemData a s"
using UnpredictableNextE[OF assms]
using getMemData_getMemCap
by auto

lemma UnpredictableNextE_getBranchDelayPccCap [elim!]:
  assumes "s' \<in> UnpredictableNext s"
  shows "getBranchDelayPccCap s' = getBranchDelayPccCap s"
using UnpredictableNextE[OF assms]
unfolding getBranchDelayPccCap_def
by auto

lemma UnpredictableNextE_getEmptyGhostState [elim!]:
  assumes "s' \<in> UnpredictableNext s"
  shows "getEmptyGhostState s'"
using UnpredictableNextE[OF assms]
by auto

lemma UnpredictableNextE_getCapReg [elim]:
  assumes unpred: "s' \<in> UnpredictableNext s"
      and ghost: "getEmptyGhostState s"
  shows "getCapReg r s' = getCapReg r s"
proof -
  have ghost2: "getEmptyGhostState s'"
    using UnpredictableNextE_getEmptyGhostState[OF unpred]
    by simp
  show ?thesis
    using UnpredictableNextE[OF unpred]
    using UnpredictableNextE_getBranchDelayPccCap[OF unpred]
    using EmptyGhostStateE[OF ghost]
    using EmptyGhostStateE[OF ghost2]
    by (cases r) (auto simp: getBranchToPccCap_def)
qed

lemma UnpredictableNextE_getCap [elim]:
  assumes unpred: "s' \<in> UnpredictableNext s"
      and ghost: "getEmptyGhostState s"
  shows "getCap loc s' = getCap loc s"
using UnpredictableNextE[OF unpred]
using UnpredictableNextE_getCapReg[OF unpred ghost]
by (cases loc) auto

lemma UnpredictableNextE_getPhysicalAddress [elim!]:
  assumes "s' \<in> UnpredictableNext s"
  shows "getPhysicalAddress vAddr s' = getPhysicalAddress vAddr s"
using assms
unfolding UnpredictableNext_def
by (cases vAddr) (auto split: prod.splits)

(*<*)
end
(*>*)