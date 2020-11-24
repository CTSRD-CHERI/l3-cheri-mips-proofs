(*<*) 

(* Author: Kyndylan Nienhuis *)

theory MemoryInvariant

imports 
  "UnpredictableBehaviour"
  "ExceptionFlag"
  "ExecutionStep"
begin

(*>*)
section \<open>Memory invariant\<close>

named_theorems MemoryInvariantI

abbreviation (out) MemoryInvariantPost where
  "MemoryInvariantPost addr val \<equiv> 
   read_state getExceptionSignalled \<or>\<^sub>b
   read_state isUnpredictable \<or>\<^sub>b
   (read_state (getMemData addr) =\<^sub>b return val)"
  
method MemoryInvariant uses intro =
  PrePost intro: intro MemoryInvariantI[THEN PrePost_post_weakening]

(* Code generation - start - memory invariant *)

(* Code generation - skip - SignalCP2UnusableException *)

(* Code generation - skip - SignalCapException_internal *)

(* Code generation - skip - SignalCapException *)

(* Code generation - skip - SignalCapException_noReg *)

lemma MemoryInvariant_dfn'ERET [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind ERETActions
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 dfn'ERET
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'ERET_alt_def ERETActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

(* Code generation - skip - SignalTLBException *)

(* Code generation - skip - AddressTranslation *)

(* Code generation - skip - SignalTLBCapException *)

(* Code generation - skip - write'MEM *)

(* Code generation - skip - InitMEM *)

(* Code generation - override - WriteData *)

lemma updateDwordInRaw_idem:
  assumes "index < 32"
      and "of_nat (index div 8) = (ucast addr'::2 word) \<Longrightarrow> extract_byte (index mod 8) msk = 0"
  shows "extract_byte index (updateDwordInRaw (addr', val, msk, old_blob)) = 
         extract_byte index old_blob"
using assms
unfolding extract_byte_updateDwordInRaw
by auto

lemma MemoryInvariant_WriteData_getMemData:
  assumes "slice 3 addr = addr' \<Longrightarrow> extract_byte (unat (addr XOR mask 3) mod 8) msk = 0"
  shows "IsInvariant (read_state (getMemData addr) =\<^sub>b return val)
                     (WriteData (addr', val', msk))"
proof (cases "(slice 5 addr::35 word) = slice 2 addr'")
  case False
  show ?thesis
    unfolding WriteData_alt_def write'MEM_alt_def 
    by PrePost (auto simp: getMemData_def Let_def MEM_def ValuePart_bind ucast_shiftr False)
next
  case True
  have "(8::nat) dvd 32" by arith
  from mod_mod_cancel[OF this]
  have [simp]: "x mod 32 mod 8 = x mod 8" for x :: nat by auto
  have *: "slice 3 addr = addr'"
  if "of_nat (unat (addr AND mask 5 XOR mask 3) div 8) = (ucast addr'::2 word)" 
    proof (intro word_eqI impI, simp add: word_size)
      fix n :: nat
      assume "n < 37"
      show "(slice 3 addr::37 word) !! n = addr' !! n"
        proof (cases "n \<le> 1")
          case True
          have "(ucast addr'::2 word) !! n =
                (of_nat (unat (addr AND mask 5 XOR mask 3) div 8)::2 word) !! n"
            using that by auto
          also have "... = (addr AND mask 5 XOR mask 3) !! (n + 3)"
            unfolding test_bit_nat zdiv_int 
            using bin_nth_div[where n=3] True
            by (auto simp: sym_uint_nat test_bit_def')
          also have "... = (slice 3 addr::2 word) !! n"
            using True 
            by (simp add: word_ops_nth_size word_size nth_slice)
          finally show ?thesis
            using True
            unfolding nth_slice nth_ucast
            by auto
        next
          case False
          define n' where "n' \<equiv> n - 2"
          hence [simp]: "n = n' + 2"
            using False by auto
          have [simp]: "5 + n' = n' + 5" by arith
          have "(slice 5 addr::35 word) !! n' = (slice 2 addr'::35 word) !! n'"
            using `slice 5 addr = slice 2 addr'` by auto
          thus ?thesis
            using test_bit_size[where w=addr' and n=n] 
            unfolding nth_slice word_size
            by auto
        qed
    qed
  have "addr AND mask 5 XOR mask 3 = (addr XOR mask 3) AND mask 5"
    by (intro word_eqI) (auto simp add: word_ops_nth_size word_size)
  hence "unat (addr AND mask 5 XOR mask 3) = unat (addr XOR mask 3) mod 32"
    by (auto simp: unat_and_mask)    
  hence [simp]: "extract_byte (unat (addr AND mask 5 XOR mask 3)) 
                              (updateDwordInRaw (addr', val', msk, old_blob)) = 
                 extract_byte (unat (addr AND mask 5 XOR mask 3)) 
                              old_blob" for old_blob
    using assms *
    by (intro updateDwordInRaw_idem) auto
  show ?thesis
    unfolding WriteData_alt_def write'MEM_alt_def 
    by PrePost (auto simp: getMemData_def Let_def MEM_def ValuePart_bind ucast_shiftr)
qed

(* We deliberately don't add the lemma to MemoryInvariantI. *)

lemma MemoryInvariant_WriteData:
  shows "PrePost (return (case v of (addr', val', msk) \<Rightarrow>
                          slice 3 a \<noteq> addr' \<or>
                          extract_byte (unat (a XOR mask 3) mod 8) msk = 0) \<and>\<^sub>b
                  (read_state (getMemData a) =\<^sub>b return val)) 
                 (WriteData v)
                 (\<lambda>_. read_state (getMemData a) =\<^sub>b return val)" 
  (is "PrePost ?p ?m ?q")
proof (intro PrePostI)
  fix s
  assume as: "ValuePart ?p s"
  hence "extract_byte (unat (a XOR mask 3) mod 8) (snd (snd v)) = 0" 
  if "slice 3 a = fst v"
    using as that
    by (cases v) (strong_cong_simp add: ValueAndStatePart_simp if_bool_simps)
  note aux = MemoryInvariant_WriteData_getMemData[OF this]
  have "ValuePart (read_state (getMemData a) =\<^sub>b return val) s"
    using as by (auto simp: ValueAndStatePart_simp)
  note PrePostE[where s=s, OF aux this]
  thus "ValuePart (bind (WriteData v) (\<lambda>_. read_state (getMemData a) =\<^sub>b return val)) s"
    by (cases v) (simp add: ValueAndStatePart_simp)
qed

(* Code generation - end override *)

(* Code generation - override - WriteCap *)

lemma MemoryInvariant_WriteCap_aux2:
  assumes "slice (log2 CAPBYTEWIDTH) addr \<noteq> addr'"
  shows "getMemData addr (setMEM (v, addr') s) = getMemData addr s" 
using assms
unfolding getMemData_def Let_def
by auto

lemma MemoryInvariant_WriteCap_aux:
  shows "PrePost (return (slice (log2 CAPBYTEWIDTH) addr \<noteq> fst v) \<and>\<^sub>b
                  (read_state (getMemData addr) =\<^sub>b return val)) 
                 (WriteCap v)
                 (\<lambda>_. read_state (getMemData addr) =\<^sub>b return val)"
unfolding WriteCap_alt_def 
by PrePost (auto intro!: MemoryInvariant_WriteCap_aux2)

lemma MemoryInvariant_WriteCap_unpred:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b read_state isUnpredictable)
                     (WriteCap v)"
by Invariant

lemmas MemoryInvariant_WriteCap [MemoryInvariantI] =
  PrePost_weakest_pre_disj
    [OF MemoryInvariant_WriteCap_aux
        MemoryInvariant_WriteCap_unpred]

(* Code generation - end override *)

lemma MemoryInvariant_LoadMemoryCap [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (LoadMemoryCap v)"
by MemoryInvariant auto?

lemma MemoryInvariant_LoadMemory [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (LoadMemory v)"
by MemoryInvariant auto?

lemma MemoryInvariant_LoadCap [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (LoadCap v)"
by MemoryInvariant auto?

(* Code generation - override - StoreMemoryCap *)

lemma extract_byte_from_mask:
  assumes "n \<le> m"
      and "n \<le> LENGTH('a)"
      and "m = m' * 8"
      and "n = n' * 8"
      and "LENGTH('a) = l' * 8"
  shows "(extract_byte index ((2::'a::len word) ^ m - 2 ^ n) = 0) \<longleftrightarrow>
         (l' \<le> index \<or> m' \<le> index \<or> index < n')" 
  (is "?l \<longleftrightarrow> ?r")
proof 
  assume ?l
  from word_eqD[OF this, where x=0]
  show ?r
    unfolding nth_extract_byte
    unfolding word_power_of_two_difference[OF assms(1,2)]
    by (cases "l' \<le> index \<or> m' \<le> index")
       (auto simp: word_ops_nth_size word_size assms)
next
  assume ?r
  thus ?l
    unfolding word_eq_iff nth_extract_byte 
    unfolding word_power_of_two_difference[OF assms(1,2)]
    by (auto simp: word_ao_nth word_ops_nth_size word_size assms)
qed

lemma extract_byte_from_WriteData_mask:
  fixes length :: "3 word"
    and vAddr' :: "64 word"
    and addr addr' :: "40 word"
  defines "m \<equiv> 56 - (unat length * 8 + (unat (vAddr' AND mask 3)) * 8) + (8 + unat length * 8)"
      and "n \<equiv> 56 - (unat length * 8 + (unat (vAddr' AND mask 3)) * 8)"
  assumes bounds: "unat length + unat vAddr' mod 8 < unat addr mod 8 \<or>
                   unat addr mod 8 < unat vAddr' mod 8"
      and length: "unat vAddr' mod 8 + unat length < 8"
  shows "extract_byte (unat (addr XOR mask 3) mod 8) ((2::64 word) ^ m - 2 ^ n) = 0"
proof -
  have leq: "n \<le> m"
    unfolding m_def n_def by simp
  have leq2: "n \<le> 64"
    unfolding n_def by simp
  define m' where "m' = max (7 - unat (vAddr' AND mask 3)) (unat length) + 1"
  define n' where "n' = 7 - unat length - (unat (vAddr' AND mask 3))"
  have m: "m = m' * 8"
    unfolding m_def m'_def diff_mult_distrib add_mult_distrib
    by simp
  have n: "n = n' * 8"
    unfolding n_def n'_def diff_mult_distrib add_mult_distrib
    by simp
  define index where "index = unat (addr XOR mask 3) mod 8"
  have "(ucast addr::3 word) \<le> max_word"
    by simp
  hence "(ucast addr::3 word) \<le> 7"
    by (simp add: max_word_def)
  note unat_sub_7 = unat_sub[OF this]
  have "unat (addr XOR mask 3) mod 8 = unat (ucast (addr XOR mask 3)::3 word)"
    by (simp add: unat_and_mask)
  also have "... = unat (NOT (ucast addr::3 word))"
    using mask_max_word[where 'a=3]
    by (simp add: ucast_xor)
  also have "... = 7 - unat addr mod 8"
    by (simp add: unat_sub_7 word_not_alt max_word_def unat_and_mask)
  finally have index_alt: "index = 7 - unat addr mod 8"
    unfolding index_def by simp
  note [simp] = le_diff_iff'[OF mod_Suc_le_divisor mod_Suc_le_divisor, where c=7, simplified]
  note [simp] = less_diff_iff'[OF mod_Suc_le_divisor, where c=7, simplified]
  have "m' \<le> index \<or> index < n'"
    unfolding index_alt n'_def m'_def
    using bounds length
    by (auto simp add: unat_and_mask not_le not_less Suc_le_eq le_max_iff_disj)
  thus ?thesis
    using leq2 extract_byte_from_mask[OF leq _ m n, where 'a=64 and l'=8 and index=index]
    unfolding index_def
    by simp
qed

lemma MemoryInvariant_WriteData_specific_Mem:
  fixes length :: "3 word"
    and vAddr' :: "64 word"
    and addr :: "40 word"
  defines "m \<equiv> 56 - (unat length * 8 + (unat (vAddr' AND mask 3)) * 8) + (8 + unat length * 8)"
      and "n \<equiv> 56 - (unat length * 8 + (unat (vAddr' AND mask 3)) * 8)"
  shows "PrePost (return ((slice 3 addr::37 word) \<noteq> slice 3 addr' \<or>
                          ((unat length + unat vAddr' mod 8 < unat addr mod 8 \<or> 
                            unat addr mod 8 < unat vAddr' mod 8) \<and>
                           unat vAddr' mod 8 + unat length < 8)) \<and>\<^sub>b
                  (read_state (getMemData addr) =\<^sub>b return val))
                 (WriteData (slice 3 addr', x, (2 ^ m - 2 ^ n)))
                 (\<lambda>_. read_state (getMemData addr) =\<^sub>b return val)"
unfolding m_def n_def
using extract_byte_from_WriteData_mask
by (intro PrePostIE[OF MemoryInvariant_WriteData])
   (auto simp: ValueAndStatePart_simp)

lemma MemoryInvariant_WriteData_specific_unpred:
  shows "IsInvariant (read_state getExceptionSignalled \<or>\<^sub>b read_state isUnpredictable)
                     (WriteData v)"
by Invariant

lemmas MemoryInvariant_WriteData_specific [MemoryInvariantI] =
  PrePost_weakest_pre_disj
    [OF MemoryInvariant_WriteData_specific_Mem 
        MemoryInvariant_WriteData_specific_unpred]

lemma MemoryInvariant_AdjustEndian [MemoryInvariantI]:
  fixes l :: "3 word"
    and a' :: "64 word"
    and a :: "40 word"
  defines "b \<equiv> (unat l + unat a' mod 8 < unat a mod 8 \<or> unat a mod 8 < unat a' mod 8) \<and> 
                unat a' mod 8 + unat l < 8"
  shows "PrePost (read_state getExceptionSignalled \<or>\<^sub>b
                  read_state isUnpredictable \<or>\<^sub>b
                  (return ((slice 3 a::37 word) \<noteq> slice 3 (snd v) \<or> b) \<and>\<^sub>b 
                   (read_state (getMemData a) =\<^sub>b return val)))
                 (AdjustEndian v)
                 (\<lambda>x. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      (return ((slice 3 a::37 word) \<noteq> slice 3 x \<or> b) \<and>\<^sub>b 
                       (read_state (getMemData a) =\<^sub>b return val)))"
unfolding AdjustEndian_alt_def
by PrePost (auto simp: slice_xor)

lemma MemoryInvariant_MemSegmentI:
  fixes accessLength :: "3 word"
  assumes trans: "getPhysicalAddress (vAddr', STORE) s = Some pAddr'"
      and slice: "(slice 3 pAddr::37 word) = slice 3 pAddr'"
      and lower: "unat vAddr' mod 8 \<le> unat pAddr mod 8"
      and upper: "unat pAddr mod 8 \<le> unat accessLength + unat vAddr' mod 8"
  shows "pAddr \<in> MemSegment pAddr' (ucast accessLength + 1)"
proof
  note getPhysicalAddress_ucast12[OF trans]
  from arg_cong[OF this, where f="\<lambda>x. (ucast x::3 word)"]
  have "(ucast pAddr'::3 word) = ucast vAddr'"
    by auto
  note pAddr' = arg_cong[OF this, where f=unat]
  have lower_2: "pAddr' AND mask 3 \<le> pAddr AND mask 3"
    using lower pAddr'
    unfolding word_le_nat_alt
    by (simp add: unat_and_mask)
  have "unat (ucast accessLength::40 word) + unat (1::40 word) < 2 ^ LENGTH(40)"
    using unat_lt2p[where x=accessLength]
    by auto
  from unat_add_lem[THEN iffD1, OF this]
  have [simp]: "unat (ucast accessLength + 1::40 word) = 
                unat (ucast accessLength::40 word) + 1"
    by simp
  have "unat (pAddr' AND mask 3) + unat (ucast accessLength + 1::40 word) < 2 ^ LENGTH(40)"
    using unat_lt2p[where x=accessLength]
    by (auto simp add: unat_and_mask)
  from unat_add_lem[THEN iffD1, OF this]
  have "(pAddr AND mask 3) < (pAddr' AND mask 3) + (ucast accessLength + 1)" 
    using upper pAddr'
    unfolding word_less_nat_alt
    by (simp add: unat_and_mask)
  hence *: "(pAddr AND mask 3) - (pAddr' AND mask 3) < ucast accessLength + 1"
    using lower_2 word_less_sub_right by metis
  have "pAddr - pAddr' = 
        ((pAddr AND NOT mask 3) + (pAddr AND mask 3)) -
        ((pAddr' AND NOT mask 3) + (pAddr' AND mask 3))"
    by simp
  also have "... = (pAddr AND mask 3) - (pAddr' AND mask 3)"
    using slice_eq_imp_and_not_mask_eq[OF _ slice]
    by simp
  finally show "pAddr - pAddr' < ucast accessLength + 1"
    using * by auto
qed

lemma MemoryInvariant_MemSegmentI_length_1:
  assumes trans: "getPhysicalAddress (vAddr', STORE) s = Some pAddr'"
      and slice: "(slice 3 pAddr::37 word) = slice 3 pAddr'"
      and lower: "unat vAddr' mod 8 = unat pAddr mod 8"
  shows "pAddr \<in> MemSegment pAddr' 1"
using assms
using MemoryInvariant_MemSegmentI[where accessLength=0]
by auto

lemma MemoryInvariant_StoreMemoryCap [MemoryInvariantI]:
  shows "PrePost ((case v of (memType, accessLength, memElem, needAlign, vAddr, cond) \<Rightarrow>
                   bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> 
                                        return ((needAlign \<and> memType = accessLength) \<or> 
                                                unat vAddr mod 8 + unat accessLength < 8) \<and>\<^sub>b 
                                        return (a \<notin> MemSegment a' (ucast accessLength + 1)))) \<and>\<^sub>b
                   (read_state (getMemData a) =\<^sub>b return val))
                 (StoreMemoryCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding StoreMemoryCap_alt_def
by (MemoryInvariant intro: PrePost_DefinedAddressTranslation)
   (auto simp: not_le not_less
         intro: isAligned_max_length 
         elim!: MemoryInvariant_MemSegmentI
                MemoryInvariant_MemSegmentI_length_1
                contrapos_np[where Q="_ \<in> MemSegment _ _"])

(* Code generation - end override *)

(* Code generation - override - StoreMemory *)

lemma MemoryInvariant_StoreMemory [MemoryInvariantI]:
  shows "PrePost ((case v of (memType, accessLength, needAlign, memElem, vAddr, cond) \<Rightarrow>
                   bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> 
                                        return ((needAlign \<and> memType = accessLength) \<or> 
                                                unat vAddr mod 8 + unat accessLength < 8) \<and>\<^sub>b 
                                        return (a \<notin> MemSegment a' (ucast accessLength + 1)))) \<and>\<^sub>b
                   (read_state (getMemData a) =\<^sub>b return val))
                 (StoreMemory v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding StoreMemory_alt_def 
by MemoryInvariant auto?

(* Code generation - end override *)

(* Code generation - override - StoreCap *)

lemma MemoryInvariant_StoreCap [MemoryInvariantI]:
  shows "PrePost ((case v of (vAddr, cap, cond) \<Rightarrow>
                   bind (read_state getLLbit)
                        (\<lambda>llbit. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> return ((cond \<longrightarrow> llbit = Some True) \<longrightarrow>
                                                          (slice 5 a::35 word) \<noteq> slice 5 a')))) \<and>\<^sub>b
                   (read_state (getMemData a) =\<^sub>b return val))
                 (StoreCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  note addr_trans [MemoryInvariantI] = PrePost_DefinedAddressTranslation
     [where p="\<lambda>x. bind (read_state getLLbit)
                        (\<lambda>llbit. return (((snd (snd v)) \<longrightarrow> llbit = Some True) \<longrightarrow> 
                                          slice 5 a \<noteq> slice 5 x)) \<and>\<^sub>b 
                   (read_state (getMemData a) =\<^sub>b return val)"]
  show ?thesis
    unfolding StoreCap_alt_def 
    by (cases v, strong_cong_simp) MemoryInvariant
qed

(* Code generation - end override *)

(* Code generation - skip - Fetch *)

lemma MemoryInvariant_mtc [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (mtc v)"
unfolding mtc_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dmtc [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dmtc v)"
unfolding dmtc_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_mfc [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (mfc v)"
unfolding mfc_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dmfc [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dmfc v)"
unfolding dmfc_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ADDI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ADDI v)"
unfolding dfn'ADDI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ADDIU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ADDIU v)"
unfolding dfn'ADDIU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DADDI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DADDI v)"
unfolding dfn'DADDI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DADDIU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DADDIU v)"
unfolding dfn'DADDIU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLTI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLTI v)"
unfolding dfn'SLTI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLTIU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLTIU v)"
unfolding dfn'SLTIU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ANDI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ANDI v)"
unfolding dfn'ANDI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ORI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ORI v)"
unfolding dfn'ORI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'XORI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'XORI v)"
unfolding dfn'XORI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LUI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'LUI v)"
unfolding dfn'LUI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ADD [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ADD v)"
unfolding dfn'ADD_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ADDU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ADDU v)"
unfolding dfn'ADDU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SUB [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SUB v)"
unfolding dfn'SUB_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SUBU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SUBU v)"
unfolding dfn'SUBU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DADD [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DADD v)"
unfolding dfn'DADD_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DADDU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DADDU v)"
unfolding dfn'DADDU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSUB [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSUB v)"
unfolding dfn'DSUB_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSUBU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSUBU v)"
unfolding dfn'DSUBU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLT [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLT v)"
unfolding dfn'SLT_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLTU v)"
unfolding dfn'SLTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'AND [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'AND v)"
unfolding dfn'AND_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'OR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'OR v)"
unfolding dfn'OR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'XOR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'XOR v)"
unfolding dfn'XOR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'NOR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'NOR v)"
unfolding dfn'NOR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MOVN [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MOVN v)"
unfolding dfn'MOVN_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MOVZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MOVZ v)"
unfolding dfn'MOVZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MADD [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MADD v)"
unfolding dfn'MADD_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MADDU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MADDU v)"
unfolding dfn'MADDU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MSUB [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MSUB v)"
unfolding dfn'MSUB_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MSUBU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MSUBU v)"
unfolding dfn'MSUBU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MUL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MUL v)"
unfolding dfn'MUL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MULT [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MULT v)"
unfolding dfn'MULT_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MULTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MULTU v)"
unfolding dfn'MULTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DMULT [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DMULT v)"
unfolding dfn'DMULT_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DMULTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DMULTU v)"
unfolding dfn'DMULTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DIV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DIV v)"
unfolding dfn'DIV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DIVU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DIVU v)"
unfolding dfn'DIVU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DDIV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DDIV v)"
unfolding dfn'DDIV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DDIVU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DDIVU v)"
unfolding dfn'DDIVU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MFHI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MFHI v)"
unfolding dfn'MFHI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MFLO [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MFLO v)"
unfolding dfn'MFLO_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MTHI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MTHI v)"
unfolding dfn'MTHI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MTLO [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MTLO v)"
unfolding dfn'MTLO_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLL v)"
unfolding dfn'SLL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SRL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SRL v)"
unfolding dfn'SRL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SRA [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SRA v)"
unfolding dfn'SRA_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SLLV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SLLV v)"
unfolding dfn'SLLV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SRLV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SRLV v)"
unfolding dfn'SRLV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SRAV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'SRAV v)"
unfolding dfn'SRAV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSLL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSLL v)"
unfolding dfn'DSLL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRL v)"
unfolding dfn'DSRL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRA [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRA v)"
unfolding dfn'DSRA_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSLLV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSLLV v)"
unfolding dfn'DSLLV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRLV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRLV v)"
unfolding dfn'DSRLV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRAV [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRAV v)"
unfolding dfn'DSRAV_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSLL32 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSLL32 v)"
unfolding dfn'DSLL32_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRL32 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRL32 v)"
unfolding dfn'DSRL32_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DSRA32 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DSRA32 v)"
unfolding dfn'DSRA32_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TGE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TGE v)"
unfolding dfn'TGE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TGEU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TGEU v)"
unfolding dfn'TGEU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLT [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TLT v)"
unfolding dfn'TLT_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TLTU v)"
unfolding dfn'TLTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TEQ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TEQ v)"
unfolding dfn'TEQ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TNE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TNE v)"
unfolding dfn'TNE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TGEI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TGEI v)"
unfolding dfn'TGEI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TGEIU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TGEIU v)"
unfolding dfn'TGEIU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLTI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TLTI v)"
unfolding dfn'TLTI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLTIU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TLTIU v)"
unfolding dfn'TLTIU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TEQI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TEQI v)"
unfolding dfn'TEQI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TNEI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'TNEI v)"
unfolding dfn'TNEI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_loadByte [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (loadByte v)"
unfolding loadByte_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_loadHalf [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (loadHalf v)"
unfolding loadHalf_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_loadWord [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (loadWord v)"
unfolding loadWord_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_loadDoubleword [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (loadDoubleword v)"
unfolding loadDoubleword_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LB [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LBActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LB v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LB_alt_def LBActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LBU [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LBUActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LBU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LBU_alt_def LBUActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LH [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LHActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LH v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LH_alt_def LHActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LHU [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LHUActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LHU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LHU_alt_def LHUActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LW [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LWActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LW v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LW_alt_def LWActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LWU [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LWUActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LWU v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LWU_alt_def LWUActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LL [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LLActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LL_alt_def LLActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LD [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LDActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LD_alt_def LDActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LLD [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LLDActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LLD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LLD_alt_def LLDActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LWL [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LWLActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LWL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LWL_alt_def LWLActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LWR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LWRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LWR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LWR_alt_def LWRActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LDL [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LDLActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LDL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LDL_alt_def LDLActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'LDR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (LDRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'LDR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'LDR_alt_def LDRActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SB [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SBActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SB v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SB_alt_def SBActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SH [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SHActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SH v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SH_alt_def SHActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

(* Code generation - override - storeWord *)

lemma MemoryInvariant_storeWord [MemoryInvariantI]:
  shows "PrePost ((case v of (b, rt, offset, cond) \<Rightarrow>
                   bind (read_state (getGPR b))
                        (\<lambda>v. bind (read_state (getSCAPR 0))
                        (\<lambda>cap. bind (return (scast offset + v + getBase cap + getOffset cap))
                        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> return (a \<notin> MemSegment a' 4)))))) \<and>\<^sub>b
                  (read_state (getMemData a) =\<^sub>b return val))
                 (storeWord v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding storeWord_alt_def 
unfolding LegacyStoreVirtualAddress_def getVirtualAddress_alt_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
by MemoryInvariant auto?

(* Code generation - end override *)

(* Code generation - override - storeDoubleword *)

lemma MemoryInvariant_storeDoubleword [MemoryInvariantI]:
  shows "PrePost ((case v of (b, rt, offset, cond) \<Rightarrow>
                   bind (read_state (getGPR b))
                        (\<lambda>v. bind (read_state (getSCAPR 0))
                        (\<lambda>cap. bind (return (scast offset + v + getBase cap + getOffset cap))
                        (\<lambda>vAddr. bind (read_state (getPhysicalAddress (vAddr, STORE)))
                        (\<lambda>x. case x of None \<Rightarrow> return True
                                     | Some a' \<Rightarrow> return (a \<notin> MemSegment a' 8)))))) \<and>\<^sub>b
                  (read_state (getMemData a) =\<^sub>b return val))
                 (storeDoubleword v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding storeDoubleword_alt_def 
unfolding LegacyStoreVirtualAddress_def getVirtualAddress_alt_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
by MemoryInvariant auto?

(* Code generation - end override *)

lemma MemoryInvariant_dfn'SW [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SWActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SW v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SW_alt_def SWActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SD [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SDActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SD_alt_def SDActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SC_alt_def SCActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SCD [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (SCDActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SCD v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SCD_alt_def SCDActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

(* Code generation - override - dfn'SWL *)

lemma MemoryInvariant_dfn'SWL [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  bind (SWLActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SWL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'SWL_alt_def SWLActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
by MemoryInvariant
   (auto simp: ucast_and ucast_not 
               unat_not unat_and_mask unat_max_word
               word_bool_alg.conj_disj_distrib2
         split: option.splits)

(* Code generation - end override *)

(* Code generation - override - dfn'SWR *)

lemma MemoryInvariant_dfn'SWR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  bind (SWRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SWR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  have [simp]: "x AND - 4 = x AND NOT mask 2" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  have [simp]: "3 - (NOT x AND mask 2) = x AND mask 2" for x :: "'a::len word"
    using mask_minus_word_and_mask[where x="NOT x" and n=2]
    unfolding mask_def
    by simp
  have "(4::nat) dvd 8"
    by arith
  note [simp] = mod_mod_cancel[OF this]
  have "4 * x mod 8 \<le> 4" for x :: nat
    by arith
  from add_le_less_mono[where d=4, OF this]
  have [simp]: "4 * x mod 8 + y mod 4 < 8" for x y :: nat
    by simp
  show ?thesis
    unfolding dfn'SWR_alt_def SWRActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by MemoryInvariant
       (auto simp: ucast_and ucast_not 
                   unat_not unat_and_mask unat_and_not_mask unat_max_word
                   word_bool_alg.conj_disj_distrib2
             split: option.splits)
qed

(* Code generation - end override *)

(* Code generation - override - dfn'SDL *)

lemma MemoryInvariant_dfn'SDL [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  bind (SDLActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SDL v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  have unat_mod_8_less: "unat x mod 8 < n" if "NOT ucast x = y" "unat (NOT y) < n"
  for x :: "64 word" and y :: "3 word" and n
    using arg_cong[where f=unat, OF that(1)] that(2)
    unfolding unat_not unat_ucast unat_and_mask unat_max_word
    by simp
  have unat_mod_8_zero: "unat x mod 8 = 0" if "NOT ucast x = y" "unat (NOT y) = 0"
  for x :: "64 word" and y :: "3 word"
    using unat_mod_8_less[where n=1] that
    by simp
  have not_ucast_mask_3: "(NOT ucast x::'a::len word) AND mask 3 = ucast y" if "NOT ucast x = y"
  for x :: "64 word" and y :: "3 word"
    using arg_cong[where f="ucast::3 word \<Rightarrow> 'a word", OF that]
    by (simp add: ucast_not word_bool_alg.conj_disj_distrib2)
  have word_3_exhaustive: "x = 7"
  if "x \<noteq> 6" "x \<noteq> 5" "x \<noteq> 4" "x \<noteq> 3" "x \<noteq> 2" "x \<noteq> 1" "x \<noteq> 0"
  for x :: "3 word"
    using exhaustive_3_word that by auto
  show ?thesis
    unfolding dfn'SDL_alt_def SDLActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by MemoryInvariant
       (auto simp: unat_and_mask not_ucast_mask_3 numeral_2_eq_2
                   word_bool_alg.conj_disj_distrib2
             dest!: word_3_exhaustive
             elim!: unat_mod_8_less unat_mod_8_zero
             split: option.splits)
qed

(* Code generation - end override *)

(* Code generation - override - dfn'SDR *)

lemma MemoryInvariant_dfn'SDR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  bind (SDRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'SDR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  have [simp]: "x AND - 8 = x AND NOT mask 3" for x :: "'a::len word"
    unfolding word_not_alt max_word_minus mask_def
    by simp
  have [simp]: "7 - (NOT x) = x" for x :: "3 word"
    unfolding word_not_alt max_word_def
    by simp
  have ucast_mask_3: "(ucast x::40 word) AND mask 3 = ucast (NOT y)" if "NOT ucast x = y"
  for x :: "64 word" and y :: "3 word"
    using arg_cong[where f="\<lambda>x. ucast (NOT x)::40 word", OF that]
    by (simp add: word_bool_alg.conj_disj_distrib2 ucast_not)
  have word_3_exhaustive: "x = 7"
  if "x \<noteq> 6" "x \<noteq> 5" "x \<noteq> 4" "x \<noteq> 3" "x \<noteq> 2" "x \<noteq> 1" "x \<noteq> 0"
  for x :: "3 word"
    using exhaustive_3_word that by auto
  have [simp]: "(-1::3 word) = 7" "(-2::3 word) = 6" "(-3::3 word) = 5" "(-4::3 word) = 4"
               "(-5::3 word) = 3" "(-6::3 word) = 2" "(-7::3 word) = 1" "(-8::3 word) = 0" 
    by simp_all
  show ?thesis
    unfolding dfn'SDR_alt_def SDRActions_def 
    unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
    unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
    unfolding CheckBranch_alt_def getVirtualAddress_alt_def
    unfolding BigEndianMem_alt_def BigEndianCPU_alt_def ReverseEndian_alt_def
    by MemoryInvariant
       (auto simp: unat_and_not_mask unat_and_mask mask_plus_one
                   word_bool_alg.conj_disj_distrib2
             dest!: ucast_mask_3 word_3_exhaustive
             split: option.splits)
qed

(* Code generation - end override *)

lemma MemoryInvariant_dfn'BREAK [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'BREAK"
unfolding dfn'BREAK_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'SYSCALL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'SYSCALL"
unfolding dfn'SYSCALL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MTC0 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MTC0 v)"
unfolding dfn'MTC0_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DMTC0 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DMTC0 v)"
unfolding dfn'DMTC0_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'MFC0 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'MFC0 v)"
unfolding dfn'MFC0_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'DMFC0 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'DMFC0 v)"
unfolding dfn'DMFC0_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'J [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'J v)"
unfolding dfn'J_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'JAL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'JAL v)"
unfolding dfn'JAL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'JALR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'JALR v)"
unfolding dfn'JALR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'JR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'JR v)"
unfolding dfn'JR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BEQ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BEQ v)"
unfolding dfn'BEQ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BNE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BNE v)"
unfolding dfn'BNE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLEZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLEZ v)"
unfolding dfn'BLEZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGTZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGTZ v)"
unfolding dfn'BGTZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLTZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLTZ v)"
unfolding dfn'BLTZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGEZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGEZ v)"
unfolding dfn'BGEZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLTZAL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLTZAL v)"
unfolding dfn'BLTZAL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGEZAL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGEZAL v)"
unfolding dfn'BGEZAL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BEQL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BEQL v)"
unfolding dfn'BEQL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BNEL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BNEL v)"
unfolding dfn'BNEL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLEZL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLEZL v)"
unfolding dfn'BLEZL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGTZL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGTZL v)"
unfolding dfn'BGTZL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLTZL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLTZL v)"
unfolding dfn'BLTZL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGEZL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGEZL v)"
unfolding dfn'BGEZL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BLTZALL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BLTZALL v)"
unfolding dfn'BLTZALL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'BGEZALL [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'BGEZALL v)"
unfolding dfn'BGEZALL_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'RDHWR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'RDHWR v)"
unfolding dfn'RDHWR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CACHE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CACHE v)"
unfolding dfn'CACHE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ReservedInstruction [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'ReservedInstruction"
unfolding dfn'ReservedInstruction_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'Unpredictable [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'Unpredictable"
unfolding dfn'Unpredictable_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLBP [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'TLBP"
unfolding dfn'TLBP_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLBR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'TLBR"
unfolding dfn'TLBR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLBWI [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'TLBWI"
unfolding dfn'TLBWI_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'TLBWR [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'TLBWR"
unfolding dfn'TLBWR_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'COP1 [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'COP1 v)"
unfolding dfn'COP1_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetBase [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetBase v)"
unfolding dfn'CGetBase_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetOffset [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetOffset v)"
unfolding dfn'CGetOffset_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetLen [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetLen v)"
unfolding dfn'CGetLen_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetTag [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetTag v)"
unfolding dfn'CGetTag_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetSealed [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetSealed v)"
unfolding dfn'CGetSealed_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetPerm [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetPerm v)"
unfolding dfn'CGetPerm_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetType [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetType v)"
unfolding dfn'CGetType_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetAddr [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetAddr v)"
unfolding dfn'CGetAddr_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetPCC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CGetPCCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CGetPCC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CGetPCC_alt_def CGetPCCActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetPCCSetOffset [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CGetPCCSetOffsetActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CGetPCCSetOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CGetPCCSetOffset_alt_def CGetPCCSetOffsetActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CGetCause [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CGetCause v)"
unfolding dfn'CGetCause_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSetCause [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CSetCause v)"
unfolding dfn'CSetCause_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CIncOffset [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CIncOffsetActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CIncOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CIncOffset_alt_def CIncOffsetActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CIncOffsetImmediate [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CIncOffsetImmediateActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CIncOffsetImmediate v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CIncOffsetImmediate_alt_def CIncOffsetImmediateActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSetBounds [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSetBoundsActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSetBounds v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSetBounds_alt_def CSetBoundsActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSetBoundsExact [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSetBoundsExactActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSetBoundsExact v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSetBoundsExact_alt_def CSetBoundsExactActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSetBoundsImmediate [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSetBoundsImmediateActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSetBoundsImmediate v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSetBoundsImmediate_alt_def CSetBoundsImmediateActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_ClearRegs [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (ClearRegs v)"
unfolding ClearRegs_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ClearLo [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ClearLo v)"
unfolding dfn'ClearLo_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'ClearHi [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'ClearHi v)"
unfolding dfn'ClearHi_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CClearLo [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CClearLoActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CClearLo v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CClearLo_alt_def CClearLoActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CClearHi [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CClearHiActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CClearHi v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CClearHi_alt_def CClearHiActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CClearTag [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CClearTagActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CClearTag v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CClearTag_alt_def CClearTagActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CAndPerm [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CAndPermActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CAndPerm v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CAndPerm_alt_def CAndPermActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSetOffset [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSetOffsetActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSetOffset v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSetOffset_alt_def CSetOffsetActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSub [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CSub v)"
unfolding dfn'CSub_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CCheckPerm [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CCheckPerm v)"
unfolding dfn'CCheckPerm_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CCheckType [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CCheckType v)"
unfolding dfn'CCheckType_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CFromPtr [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CFromPtrActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CFromPtr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CFromPtr_alt_def CFromPtrActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CToPtr [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CToPtr v)"
unfolding dfn'CToPtr_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_CPtrCmp [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (CPtrCmp v)"
unfolding CPtrCmp_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CEQ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CEQ v)"
unfolding dfn'CEQ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CNE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CNE v)"
unfolding dfn'CNE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLT [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CLT v)"
unfolding dfn'CLT_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLE [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CLE v)"
unfolding dfn'CLE_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CLTU v)"
unfolding dfn'CLTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLEU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CLEU v)"
unfolding dfn'CLEU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CEXEQ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CEXEQ v)"
unfolding dfn'CEXEQ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CNEXEQ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CNEXEQ v)"
unfolding dfn'CNEXEQ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CBTU [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CBTU v)"
unfolding dfn'CBTU_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CBTS [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CBTS v)"
unfolding dfn'CBTS_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CBEZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CBEZ v)"
unfolding dfn'CBEZ_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CBNZ [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CBNZ v)"
unfolding dfn'CBNZ_alt_def 
by MemoryInvariant auto?

(* Code generation - override - dfn'CSC *)

lemma MemoryInvariant_dfn'CSC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSC_alt_def CSCActions_def 
unfolding CSCPhysicalAddress_def CSCVirtualAddress_def
by MemoryInvariant 
   (auto simp: eq_slice_eq_and_not_mask not_less not_le
         dest!: aligned_MemSegment_member)

(* Code generation - end override *)

lemma MemoryInvariant_dfn'CLC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CLCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CLC_alt_def CLCActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLoad [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CLoadActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CLoad v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CLoad_alt_def CLoadActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

(* Code generation - skip - store *)

(* Code generation - override - dfn'CStore *)

lemma MemoryInvariant_dfn'CStore [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CStoreActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CStore v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  have [simp]: "min (unat x) 3 = unat x" for x :: "2 word"
    using min_unat_length[where 'a=2]
    by simp
  show ?thesis
    unfolding dfn'CStore_alt_def CStoreActions_def store_alt_def
    unfolding CStorePhysicalAddress_def CStoreVirtualAddress_def
    by MemoryInvariant 
       (cases rule: exhaustive_2_word[where x="case v of (rs, cb, rt, offset, t) \<Rightarrow> t"],
        auto simp: mask_plus_one split: option.splits)
qed

(* Code generation - end override *)

lemma MemoryInvariant_dfn'CLLC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CLLCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CLLC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CLLC_alt_def CLLCActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CLLx [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CLLxActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CLLx v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CLLx_alt_def CLLxActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

(* Code generation - override - dfn'CSCC *)

lemma MemoryInvariant_dfn'CSCC [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSCCActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSCC v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSCC_alt_def CSCCActions_def 
unfolding CSCCPhysicalAddress_def CSCCVirtualAddress_def
by MemoryInvariant
   (auto simp: eq_slice_eq_and_not_mask not_less not_le
         dest!: aligned_MemSegment_member
         split: option.splits if_splits)

(* Code generation - end override *)

(* Code generation - override - dfn'CSCx *)

lemma MemoryInvariant_dfn'CSCx [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSCxActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSCx v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
proof -
  have [simp]: "min (unat x) 3 = unat x" for x :: "2 word"
    using min_unat_length[where 'a=2]
    by simp
  show ?thesis
    unfolding dfn'CSCx_alt_def CSCxActions_def store_alt_def
    unfolding CSCxPhysicalAddress_def CSCxVirtualAddress_def
    by MemoryInvariant 
       (cases rule: exhaustive_2_word[where x="case v of (rs, cb, rd, t) \<Rightarrow> t"],
        auto simp: mask_plus_one split: option.splits)
qed

(* Code generation - end override *)

lemma MemoryInvariant_dfn'CMOVN [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CMOVNActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CMOVN v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CMOVN_alt_def CMOVNActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CMOVZ [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CMOVZActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CMOVZ v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CMOVZ_alt_def CMOVZActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CMove [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CMoveActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CMove v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CMove_alt_def CMoveActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CTestSubset [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CTestSubset v)"
unfolding dfn'CTestSubset_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CBuildCap [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CBuildCapActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CBuildCap v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CBuildCap_alt_def CBuildCapActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CCopyType [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CCopyTypeActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CCopyType v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CCopyType_alt_def CCopyTypeActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CJR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CJRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CJR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CJR_alt_def CJRActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CJALR [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CJALRActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CJALR v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CJALR_alt_def CJALRActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CSeal [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CSealActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CSeal v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CSeal_alt_def CSealActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CUnseal [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CUnsealActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CUnseal v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CUnseal_alt_def CUnsealActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CCall [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) (dfn'CCall v)"
unfolding dfn'CCall_alt_def 
by MemoryInvariant auto?

(* Code generation - override - dfn'CCallFast *)

lemma MemoryInvariant_dfn'CCallFast [MemoryInvariantI]:
  shows "IsInvariant (return False) (dfn'CCallFast v)"
by MemoryInvariant

(* Code generation - end override *)

lemma MemoryInvariant_dfn'CReadHwr [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CReadHwrActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CReadHwr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CReadHwr_alt_def CReadHwrActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CWriteHwr [MemoryInvariantI]:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  bind (CWriteHwrActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))))
                 (dfn'CWriteHwr v)
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding dfn'CWriteHwr_alt_def CWriteHwrActions_def 
unfolding LegacyStoreActions_def LegacyStorePhysicalAddress_def LegacyStoreVirtualAddress_def
unfolding BYTE_def HALFWORD_def WORD_def DOUBLEWORD_def
unfolding CheckBranch_alt_def getVirtualAddress_alt_def
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'CReturn [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'CReturn"
unfolding dfn'CReturn_alt_def 
by MemoryInvariant auto?

lemma MemoryInvariant_dfn'UnknownCapInstruction [MemoryInvariantI]:
  shows "IsInvariant (read_state (getMemData a) =\<^sub>b return val) dfn'UnknownCapInstruction"
unfolding dfn'UnknownCapInstruction_alt_def 
by MemoryInvariant auto?

(* Code generation - override - Run *)

lemma MemoryInvariant_Run_aux:
  shows "PrePost ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state getCP0ConfigBE) \<and>\<^sub>b
                  (\<not>\<^sub>b read_state getCP0StatusRE) \<and>\<^sub>b
                  bind (RunActions v)
                       (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p))) \<and>\<^sub>b
                  return (case v of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                  | _ \<Rightarrow> True))
                 (Run v) 
                 (\<lambda>_. read_state getExceptionSignalled \<or>\<^sub>b
                      read_state isUnpredictable \<or>\<^sub>b
                      read_state (getMemData a) =\<^sub>b return val)"
unfolding Run_alt_def CheckBranch_alt_def RunActions_def
by MemoryInvariant auto?

lemmas MemoryInvariant_Run [MemoryInvariantI] =
  PrePost_weakest_pre_disj[OF MemoryInvariant_Run_aux
                              UndefinedCase_Run]

(* Code generation - end override *)

(* Code generation - override - Next *)

lemma MemoryInvariant_TakeBranch [MemoryInvariantI]:
  shows "IsInvariant (MemoryInvariantPost a val) TakeBranch"
unfolding TakeBranch_def
by PrePost (auto split: option.splits)

lemma MemoryInvariant_Fetch_aux1:
  shows "IsInvariant ((read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                      (read_state getCP0ConfigBE) \<and>\<^sub>b
                      (\<not>\<^sub>b read_state getCP0StatusRE)) 
                     Fetch"
by Invariant

lemma MemoryInvariant_Fetch_aux2:
  fixes a
  defines "p \<equiv> \<lambda>w. return (case Decode w of COP2 (CHERICOP2 (CCallFast _)) \<Rightarrow> False
                                           | _ \<Rightarrow> True) \<and>\<^sub>b 
                    bind (RunActions (Decode w))
                         (\<lambda>p. return (a \<notin> \<Union> (WrittenAddresses ` p)))"
  shows "PrePost (bind NextInstruction (case_option (return True) p))
                 Fetch
                 (\<lambda>x. case x of None \<Rightarrow> read_state getExceptionSignalled
                              | Some w \<Rightarrow> read_state isUnpredictable \<or>\<^sub>b p w)"
unfolding p_def
by (intro PrePost_Fetch) Commute+

lemmas MemoryInvariant_Fetch [MemoryInvariantI] =
  PrePost_weakest_pre_conj
      [OF MemoryInvariant_Fetch_aux1[where a=a] 
          MemoryInvariant_Fetch_aux2[where a=a]] for a

lemma MemoryInvariant_NextWithGhostState [MemoryInvariantI]:
  shows "PrePost (read_state getEmptyGhostState \<and>\<^sub>b
                  read_state getCP0ConfigBE \<and>\<^sub>b
                  \<not>\<^sub>b read_state getCP0StatusRE \<and>\<^sub>b
                  (read_state (getMemData a) =\<^sub>b return val) \<and>\<^sub>b
                  (read_state CCallFastInstructionParam =\<^sub>b return None) \<and>\<^sub>b
                  bind DomainActions
                       (\<lambda>p. return (\<forall>x\<in>p. a \<notin> WrittenAddresses x)))
                 NextWithGhostState
                 (\<lambda>_. MemoryInvariantPost a val)"
unfolding NextWithGhostState_def DomainActions_def
by MemoryInvariant
   (auto split: all_split elim!: CCallFastInstructionParam_None)

(* Code generation - end override *)

(* Code generation - end *)

theorem MemoryInvariant:
  assumes prov: "a \<notin> \<Union> (WrittenAddresses ` actions)"
      and valid: "getStateIsValid s"
      and suc: "(PreserveDomain actions, s') \<in> NextStates s"
  shows "getMemData a s' = getMemData a s"
using assms
using PrePostE[where s=s,
               OF MemoryInvariant_NextWithGhostState
                  [where a=a and val="getMemData a s"]]
unfolding StateIsValid_def
unfolding NextStates_def Next_NextWithGhostState NextNonExceptionStep_def
by (auto simp: ValueAndStatePart_simp split: if_splits option.splits)

corollary MemoryInvariantInstantiation:
  assumes "(lbl, s') \<in> NextStates s"
  shows "MemoryInvariant s lbl s'"
unfolding MemoryInvariant_def
using assms MemoryInvariant
by auto blast?

(*<*)
end
(*>*)