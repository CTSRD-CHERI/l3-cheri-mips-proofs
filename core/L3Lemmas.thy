(*<*)

(* Author: Kyndylan Nienhuis *)

theory L3Lemmas

imports 
  "CHERI-p256.L3_Lib"
  "Preamble"
begin

(*>*)
section \<open>Lemmas about L3\<close>

text \<open>In this theory we prove lemmas about the L3 library. (The only reason we also import the CHERI
model is that we want the proof methods that are defined here to have access to the distributive
cases of types defined in the CHERI model.)\<close>

subsection \<open>Folding and unfolding definitions\<close>

thm bin_to_bl_def
declare bin_to_bl_def [simp del]

thm word_extract_def
declare word_extract_def [alt_def_simp]

thm word_bits_def
declare word_bits_def [alt_def_simp]

subsection \<open>Alternative definitions of monadic functions\<close>

text \<open>Some of the original definitions introduce case-expressions (of pairs) that the simplifier
does not remove. The following definitions prevent that problem.\<close>

thm extend_state_def

lemma extend_state_alt:
  shows "extend_state v m = 
         (\<lambda>s. (let m = m (v, s) in (fst m, snd (snd m))))" 
        (is "?l = ?r")
proof
  fix s
  show "?l s = ?r s"
    unfolding extend_state_def
    by (cases "m (v, s)") auto
qed

thm trim_state_def

lemma trim_state_alt:
  shows "trim_state m = 
         (\<lambda>s. (let m = m (snd s) in (fst m, (fst s, snd m))))" 
        (is "?l = ?r")
proof
  fix s
  show "?l s = ?r s"
    proof (cases s)
      case (Pair a b)
      thus ?thesis
        unfolding trim_state_def 
        by (cases "m b") auto
    qed
qed

thm bind_def

lemma bind_alt:
  shows "bind m n = 
         (\<lambda>s. (let m = m s in n (fst m) (snd m)))" 
        (is "?l = ?r")
proof
  fix s
  show "?l s = ?r s"
    unfolding bind_def 
    by (cases "m s") auto
qed

text \<open>With the following we can unfold all monadic expressions at once. We do not include the
definitions for the loops, because they are recursive functions.\<close>

lemmas monad_def = return_def
                   read_state_def
                   update_state_def
                   extend_state_alt
                   trim_state_alt
                   bind_alt

subsection \<open>Should be moved to L3-lib\<close>

subsubsection \<open>@{const log2}\<close>

lemma log2_constants [simp]:
  shows "log2 1 = 0"
    and "log2 2 = 1"
    and "log2 4 = 2"
    and "log2 8 = 3"
    and "log2 16 = 4"
    and "log2 32 = 5"
    and "log2 64 = 6"
    and "log2 128 = 7"
    and "log2 256 = 8"
    and "log2 512 = 9"
    and "log2 1024 = 10"
by (simp_all add: log2.simps)

subsubsection \<open>@{const nat_to_bitstring}\<close>

lemma nth_nat_to_bitstring:
  assumes "0 < n" "m < log2 n + 1"
  shows "nat_to_bitstring n ! m = 
         bin_nth (int n) (log2 n - m)"
proof -
  obtain k where "n = Suc k"
    using assms gr0_implies_Suc by auto
  thus ?thesis 
   using assms
   by (simp add: nat_to_bitstring_def nth_bin_to_bl) 
qed

subsubsection \<open>@{const word_bits}\<close>

lemma nth_word_bits:
  fixes w :: "'a::len word"
  shows "(word_bits h l w) !! n = 
         (w !! (n + l) \<and> n < Suc h - l)"
proof (cases "n < len_of TYPE ('a)")
  case True
  hence "n < size (w >> l)" unfolding word_size by simp
  note Word.word_ops_nth_size[OF this]
  thus ?thesis
    unfolding word_bits_def
    using True
    by (simp add: word_size nth_shiftr)
next
  case False
  hence "size (word_bits h l w) \<le> n"
    unfolding word_size by simp
  hence *: "\<not> (word_bits h l w) !! n"
    using test_bit_size by force
  have "size w \<le> n + l"
    using False unfolding word_size by simp
  hence "\<not> w !! (n + l)"
    using test_bit_size by force
  thus ?thesis using * by simp
qed

subsubsection \<open>@{const word_extract}\<close>

lemma nth_word_extract:
  shows "((word_extract h l w)::'a::len word) !! n = 
         (w !! (n + l) \<and> n < Suc h - l \<and> n < len_of TYPE('a))"
unfolding word_extract_def
unfolding nth_ucast nth_word_bits
by auto

lemma word_extract_zero [simp]:
  shows "word_extract n m 0 = 0"
by (auto intro: word_eqI simp: nth_word_extract)

lemma word_extract_start_zero [simp]:
  shows "word_extract n 0 x = ucast (x AND mask (Suc n))"
using test_bit_size
by (auto intro!: word_eqI simp: word_size nth_word_extract nth_ucast word_ao_nth)

lemma word_extract_empty_bounds:
  assumes "m < n"
  shows "word_extract m n x = 0"
using assms
by (intro word_eqI) (simp add: nth_word_extract)

lemma word_extract_word_extract:
  shows "word_extract m n (word_extract k l x::'a::len word) = 
         word_extract (min (min (m + l) k) (l + LENGTH('a) - 1)) (n + l) x"
         (is "?l = ?r")
proof (intro word_eqI iffI impI)
  fix i
  assume "?l !! i"
  thus "?r !! i"
    by (auto simp: nth_word_extract add.assoc)
next
  fix i
  assume "?r !! i"
  hence "i < Suc (min (min (m + l) k) (l + LENGTH('a) - Suc 0)) - (n + l)"
    by (simp add: nth_word_extract)
  hence "i < LENGTH('a) - n"
    using lens_not_0(2)[where ?'a='a]
    by arith
  thus "?l !! i"
    using `?r !! i`
    by (auto simp: word_size nth_word_extract add.assoc)
qed

subsubsection \<open>@{const word_replicate}\<close>

lemma word_replicate_alt_def:
  fixes x :: "'a::len word"
  shows "word_replicate n x = word_of_int (((\<lambda>y. bin_cat y LENGTH('a) (uint x)) ^^ n) 0)"
unfolding word_replicate_def
unfolding word_rcat_def
unfolding bin_rcat_def
unfolding foldl_conv_foldr
by simp

lemma word_replicate_none [simp]:
  shows "word_replicate 0 x = 0"
unfolding word_replicate_alt_def
by simp

lemma word_replicate_once [simp]:
  shows "word_replicate 1 x = ucast x"
unfolding word_replicate_alt_def ucast_def
by simp

lemma word_replicate_zero [simp]:
  shows "word_replicate n 0 = 0"
by (induct n) (simp_all add: word_replicate_def word_rcat_def bin_rcat_def)

lemma nth_word_replicate_one [simp]:
  shows "(word_replicate n (1::1 word)::'a::len word) !! i = 
         (i < min n LENGTH('a))"
proof (induct n arbitrary: i)
  case (Suc n)
  note Suc[where i="i - 1"]
  thus ?case
    unfolding word_replicate_alt_def 
    by (cases "i = 0") auto
qed simp

lemma word_replicate_one [simp]:
  shows "word_replicate n (1::1 word) = mask n"
by (intro word_eqI impI) (simp add: word_size)

lemma word_replicate_if [alt_def_simp]:
  shows "word_replicate n (if b then (1::1 word) else 0) = (if b then mask n else 0)"
by simp_all

subsubsection \<open>Defining \<open>extract_byte\<close>\<close>

definition extract_byte :: "nat \<Rightarrow> 'b::len word \<Rightarrow> 8 word" where
  "extract_byte index val \<equiv>
     word_extract (index * 8 + 7) (index * 8) val"

lemma extract_byte_zero_word [simp]:
  shows "extract_byte n 0 = 0"
unfolding extract_byte_def Let_def
by simp

lemma extract_byte_zero_index:
  shows "extract_byte 0 x = ucast (x AND mask 8)"
unfolding extract_byte_def Let_def
by simp

lemma nth_extract_byte:
  shows "extract_byte index x !! n = (x !! (n + index * 8) \<and> n < 8)"
unfolding extract_byte_def Let_def
by (auto simp: nth_word_extract)

lemma extract_byte_outside_bounds:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) \<le> n * 8"
  shows "extract_byte n x = 0"
proof (intro word_eqI, clarsimp)
  fix m
  assume "extract_byte n x !! m"
  hence "m + n * 8 < LENGTH('a)"
    using test_bit_size
    unfolding nth_extract_byte word_size
    by auto
  thus False
    using assms
    by auto
qed

lemma extract_byte_word_and:
  shows "extract_byte index (x AND y) = extract_byte index x AND extract_byte index y"
by (auto intro: word_eqI simp: nth_extract_byte word_ao_nth)

lemma extract_byte_word_or:
  shows "extract_byte index (x OR y) = extract_byte index x OR extract_byte index y"
by (auto intro: word_eqI simp: nth_extract_byte word_ao_nth)

lemma extract_byte_word_not:
  fixes x :: "'a::len word"
  assumes "LENGTH('a) = k * 8"
  shows "extract_byte index (NOT x) = 
         (if k \<le> index then 0
          else NOT extract_byte index x)"
         (is "?l = ?r")
proof (intro word_eqI impI, simp add: word_size split del: if_splits(1))
  fix n :: nat
  assume "n < 8"
  hence [simp]: "(NOT extract_byte index x) !! n = (\<not> extract_byte index x !! n)"
    by (auto simp: word_size word_ops_nth_size)
  hence "n < LENGTH('a)"
    using assms `n < 8`
    using lens_not_0(2)[where ?'a='a]
    by arith
  show "?l !! n = ?r !! n"
    proof (cases "n + index * 8 < LENGTH('a)")
      case True
      hence [simp]: "(NOT x) !! (n + index * 8) = (\<not> x !! (n + index * 8))"
        by (auto simp: word_size word_ops_nth_size)
      thus ?thesis
        using `n < 8` True
        by (auto intro: word_eqI simp: assms nth_extract_byte)
    next
      case False
      hence [simp]: "\<not> (NOT x) !! (n + index * 8)"
        using test_bit_size
        unfolding word_size
        by auto
      have "k \<le> index"
        using `n < 8` False
        unfolding assms not_less
        by auto
      thus ?thesis 
        by (auto intro: word_eqI simp: assms nth_extract_byte)
    qed
qed

lemma extract_byte_ucast:
  assumes "LENGTH('a) = k * 8"
  shows "extract_byte index (ucast x::'a::len word) =
         (if k \<le> index then 0
          else extract_byte index x)"
by (intro word_eqI)
   (auto simp: assms
               nth_extract_byte 
               nth_ucast)

lemma extract_byte_word_cat:
  assumes "LENGTH('a) = k * 8"
  shows "extract_byte index (word_cat x (y::'a::len word)::'b::len word) = 
         (if index < k
          then extract_byte index (y AND mask LENGTH('b))
          else extract_byte (index - k) (x AND mask (LENGTH('b) - k * 8)))"
using test_bit_size
by (intro word_eqI)
   (auto simp: assms
               word_size 
               nth_extract_byte 
               nth_word_cat
               nth_ucast
               word_ao_nth
               if_distrib[where f="\<lambda>x. x !! _"]
               diff_mult_distrib)

lemma extract_byte_word_extract:
  assumes "m = m' * 8 - 1"
      and "m' \<noteq> 0"
      and "n = n' * 8"
      and "LENGTH('a) = l' * 8"
  shows "extract_byte index (word_extract m n x::'a::len word) = 
         (if m' \<le> index + n' \<or> l' \<le> index then 0
          else extract_byte (index + n') x)"
proof (cases "m' \<le> index + n'")
  case True
  thus ?thesis
    using `m' \<noteq> 0`
    unfolding assms extract_byte_def word_extract_word_extract
    by (auto intro!: word_extract_empty_bounds)
next
  case *: False
  hence [simp]: "min (index * 8 + 7 + n' * 8) (m' * 8 - Suc 0) = index * 8 + 7 + n' * 8"
    by auto
  have "l' \<noteq> 0"
    using lens_not_0(2)[where ?'a='a] assms by auto
  show ?thesis
    proof (cases "l' \<le> index")
      case True
      thus ?thesis
        using `l' \<noteq> 0`
        unfolding assms extract_byte_def word_extract_word_extract
        by (auto intro!: word_extract_empty_bounds)
    next
      case False
      hence [simp]: "min (index * 8 + 7 + n' * 8) (n' * 8 + l' * 8 - Suc 0) = 
                     index * 8 + n' * 8 + 7" 
        by arith
      show ?thesis
        using * False
        unfolding assms extract_byte_def word_extract_word_extract
        by auto
    qed
qed

subsubsection \<open>Monad\<close>

lemma bind_read_state_irrelevant [simp]:
  shows "bind (read_state f) (\<lambda>_. m) = m"
unfolding bind_def read_state_def
by simp

lemma bind_read_state_duplicate [simp]:
  shows "bind (read_state f) (\<lambda>a. bind (read_state f) (\<lambda>b. m a b)) = 
         bind (read_state f) (\<lambda>a. m a a)"
unfolding bind_def read_state_def
by simp

lemma update_state_bind_return_null [simp]:
  shows "bind (update_state f) (\<lambda>_. return ()) = update_state f"
unfolding bind_def update_state_def return_def
by simp

lemma foreach_loop_return [simp]:
  shows "foreach_loop (l, \<lambda>_. return ()) = return ()"
by (induct l) simp_all

subsection \<open>@{const for_loop}\<close>

text \<open>The @{term for_loop} uses complicated recursion that makes proofs awkward. We avoid this
problem by rewriting @{term "for_loop (j, k) m"} to @{term "foreach_loop (seq j k) m"}. The
definition of @{term seq} hides the complicated recursion (in our proofs we do not need to unfold
@{term seq} often), and we can use the simple recursive definition of @{term foreach_loop} in our
proofs.\<close>

thm for_loop.simps

definition seq :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "seq i j \<equiv> 
   if i \<le> j then map nat [int i..int j]
   else rev (map nat [int j..int i])"

lemma upto_singleton [simp]:
  shows "[i..i] = [i]"
by (simp add: upto.simps) 

lemma seq_singleton [simp]:
  shows "seq i i = [i]"
unfolding seq_def
by simp

lemma seq_recursive:
  shows "seq i j = 
         (if i = j then [i]
          else if i < j then i # (seq (i + 1) j)
          else i # (seq (i - 1) j))"
proof (cases "i = j")
  case True
  thus ?thesis by auto
next
  case not_eq: False
  show ?thesis
    proof (cases "i \<le> j")
      case True
      hence "i < j" using not_eq by simp
      hence [simp]: "Suc (j - Suc i) = j - i" by auto
      show ?thesis
        using `i < j`
        unfolding seq_def[where i=i and j=j]
        unfolding seq_def[where i="i + 1" and j=j]
        using upto.simps[where i="int i" and j="int j"]
        by (simp add: add.commute)
    next
      case False
      hence "j < i" by simp
      hence [simp]: "Suc (i - Suc j) = i - j" by auto
      have [simp]: "int (i - Suc 0) = int i - 1" if "i \<noteq> 0"
        using that
        by auto
      have "j = i - 1" if "j < i" "i - Suc 0 \<le> j"
        using that by auto
      thus ?thesis
        using `j < i`
        unfolding seq_def[where i=i and j=j]
        unfolding seq_def[where i="i - 1" and j=j]
        using upto_rec2[where i="int j" and j="int i"]
        by auto
    qed
qed

lemma set_seq:
  shows "set (seq i j) = 
         (if i \<le> j then nat ` {int i..int j}
          else nat ` {int j..int i})"
unfolding seq_def
by simp

lemma set_seq_zero [simp]:
  shows "set (seq 0 k) = {i. i \<le> k}"
unfolding set_seq
proof (intro equalityI subsetI, simp_all)
  fix x
  assume "x \<in> nat ` {0..int k}"
  thus "x \<le> k" by auto
next
  fix x
  assume "x \<le> k"
  hence "int x \<in> {0..int k}"
    by auto
  from imageI[OF this, where f=nat]
  show "x \<in> nat ` {0..int k}" by simp
qed

lemma for_loop_alt [simp]:
  shows "for_loop (i, j, m) = foreach_loop ((seq i j), m)"
proof (induct "if i < j then j - i else i - j" arbitrary: i)
  case 0
  hence "i = j" by arith
  thus ?case
    unfolding seq_def
    by (simp add: for_loop.simps)
next
  case (Suc k)
  hence "i \<noteq> j" by auto

  -- "We first rewrite the induction hypothesis."
  define i' where "i' \<equiv> if i < j then i + 1 else i - 1"
  have k: "k = (if i' < j then j - i' else i' - j)"
    unfolding i'_def
    using Suc(2)
    by auto
  hence ih: "for_loop (i', j, m) = foreach_loop (seq i' j, m)"
    using Suc(1)
    by metis

  -- "Now we prove the goal"
  have "for_loop (i, j, m) = bind (m i) (\<lambda>u. for_loop (i', j, m))"
    using `i \<noteq> j`
    unfolding i'_def
    by (simp add: for_loop.simps)
  also have "... = bind (m i) (\<lambda>u. foreach_loop (seq i' j, m))"
    using ih by auto
  also have "... = foreach_loop (seq i j, m)"
    using `i \<noteq> j`
    unfolding i'_def
    unfolding seq_recursive[where i=i and j=j]
    by simp
  finally show "?case" .
qed

subsection \<open>Value and state parts\<close>
  
definition ValuePart :: "('state \<Rightarrow> 'a \<times> 'state) \<Rightarrow> 'state \<Rightarrow> 'a" where
  "ValuePart m \<equiv> (\<lambda>s. fst (m s))"

definition StatePart :: "('state \<Rightarrow> 'a \<times> 'state) \<Rightarrow> 'state \<Rightarrow> 'state" where
  "StatePart m \<equiv> (\<lambda>s. snd (m s))"

lemma monad_eqI:
  assumes "\<And>s. ValuePart m s = ValuePart n s"
      and "\<And>s. StatePart m s = StatePart n s"
  shows "m = n"
using assms
unfolding ValuePart_def StatePart_def
by (intro ext prod_eqI)

named_theorems ValueAndStatePart_simp
  
lemma ValuePart_unit [simp]:
  fixes m :: "'state \<Rightarrow> unit \<times> 'state"
  shows "ValuePart m = (\<lambda>_. ())"
unfolding ValuePart_def
by simp

lemma bind_to_value_and_StateParts:
  shows "bind m n = (\<lambda>s. n (ValuePart m s) (StatePart m s))"
unfolding monad_def ValuePart_def StatePart_def Let_def
by simp

subsubsection \<open>@{const return}\<close>

lemma ValuePart_return [simp]:
  shows "ValuePart (return x) = (\<lambda>_. x)"
unfolding ValuePart_def
by simp

lemma StatePart_return [simp]:
  shows "StatePart (return x) = (\<lambda>s. s)"
unfolding StatePart_def
by simp

subsubsection \<open>@{const read_state}\<close>

lemma ValuePart_read_state [simp]:
  shows "ValuePart (read_state f) = f"
unfolding ValuePart_def
by simp

lemma StatePart_read_state [simp]:
  shows "StatePart (read_state f) = (\<lambda>s. s)"
unfolding StatePart_def
by simp

subsubsection \<open>@{const update_state}\<close>

text \<open>The @{const ValuePart} is already covered by \<open>ValuePart_unit\<close>.\<close>

lemma StatePart_update_state [simp]:
  shows "StatePart (update_state f) = f"
unfolding StatePart_def
by simp

subsubsection \<open>@{const bind}\<close>

lemma ValuePart_bind [ValueAndStatePart_simp]:
  shows "ValuePart (bind m n) = 
         (\<lambda>s. ValuePart (n (ValuePart m s)) (StatePart m s))"
unfolding monad_def Let_def ValuePart_def StatePart_def
by simp

lemma StatePart_bind [ValueAndStatePart_simp]:
  shows "StatePart (bind m n) = 
         (\<lambda>s. StatePart (n (ValuePart m s)) (StatePart m s))"
unfolding monad_def Let_def ValuePart_def StatePart_def
by simp

lemma ValuePart_bind_return [simp]:
  shows "ValuePart (bind m (\<lambda>_. return x)) = (\<lambda>_. x)"
by (simp add: ValuePart_bind)

lemma StatePart_bind_return [simp]:
  shows "StatePart (bind m (\<lambda>a. return (f a))) = StatePart m"
by (simp add: StatePart_bind)

lemma StatePart_bind_read_state [simp]:
  shows "StatePart (bind m (\<lambda>a. read_state (f a))) = StatePart m"
by (simp add: StatePart_bind)

subsubsection \<open>@{const foreach_loop}\<close>

text \<open>The @{const ValuePart} is already covered by \<open>ValuePart_unit\<close>.\<close>

lemma StatePart_foreach_loop [simp]:
  shows "StatePart (foreach_loop (l, m)) = fold (\<lambda>a. StatePart (m a)) l"
by (induct l)
   (auto simp add: StatePart_bind)

subsection \<open>Monadic connectives\<close>

definition UnaryLift :: "('a \<Rightarrow> 'b) \<Rightarrow> 
                         ('state \<Rightarrow> 'a \<times> 'state) \<Rightarrow> 
                         ('state \<Rightarrow> 'b \<times> 'state)" where
  "UnaryLift f m \<equiv> 
   bind (read_state (ValuePart m))
        (\<lambda>x. return (f x))"

lemma ValuePart_UnaryLift [simp]:
  shows "ValuePart (UnaryLift f m) s = f (ValuePart m s)"
unfolding UnaryLift_def
by (simp add: ValueAndStatePart_simp)

lemma StatePart_UnaryLift [simp]:
  shows "StatePart (UnaryLift f m) = (\<lambda>s. s)"
unfolding UnaryLift_def
by (simp add: ValueAndStatePart_simp)

definition BinaryLift :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 
                          ('state \<Rightarrow> 'a \<times> 'state) \<Rightarrow> 
                          ('state \<Rightarrow> 'b \<times> 'state) \<Rightarrow> 
                          ('state \<Rightarrow> 'c \<times> 'state)" where
  "BinaryLift f m m' \<equiv> 
   bind (read_state (ValuePart m))
        (\<lambda>x. bind (read_state (ValuePart m'))
        (\<lambda>x'. return (f x x')))"

lemma ValuePart_BinaryLift [ValueAndStatePart_simp]:
  shows "ValuePart (BinaryLift f m m') s = (f (ValuePart m s) (ValuePart m' s))"
unfolding BinaryLift_def
by (simp add: ValueAndStatePart_simp)

lemma StatePart_BinaryLift [simp]:
  shows "StatePart (BinaryLift f m m') = (\<lambda>s. s)"
unfolding BinaryLift_def
by (simp add: ValueAndStatePart_simp)

definition BinderLift :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 
                          ('a \<Rightarrow> 'state \<Rightarrow> 'b \<times> 'state) \<Rightarrow> 
                          ('state \<Rightarrow> 'c \<times> 'state)" where
  "BinderLift f m \<equiv>
   read_state (\<lambda>s. f (\<lambda>a. ValuePart (m a) s))"

lemma ValuePart_BinderLift [ValueAndStatePart_simp]:
  shows "ValuePart (BinderLift f m) s = (f (\<lambda>a. ValuePart (m a) s))"
unfolding BinderLift_def
by (simp add: ValueAndStatePart_simp)

lemma StatePart_BinderLift [simp]:
  shows "StatePart (BinderLift f m) = (\<lambda>s. s)"
unfolding BinderLift_def
by (simp add: ValueAndStatePart_simp)

definition EqMonadic (infixr "=\<^sub>b" 95) where
  "EqMonadic \<equiv> BinaryLift (op =)"

lemma EqMonadic_equals [simp]:
  shows "(m =\<^sub>b m) = return True"
unfolding EqMonadic_def BinaryLift_def
by simp_all

lemma EqMonadic_return [simp]:
  shows "(return x =\<^sub>b return y) = return (x = y)"
unfolding EqMonadic_def BinaryLift_def
by simp

lemma ValuePart_EqMonadic [ValueAndStatePart_simp]:
  shows "ValuePart (m =\<^sub>b m') s = (ValuePart m s = ValuePart m' s)"
unfolding EqMonadic_def 
by (simp add: ValueAndStatePart_simp)

lemma StatePart_EqMonadic [simp]:
  shows "StatePart (m =\<^sub>b m') = (\<lambda>s. s)"
unfolding EqMonadic_def 
by simp

definition NotMonadic ("\<not>\<^sub>b _" [90] 90) where
  "NotMonadic \<equiv> UnaryLift Not"

lemma NotMonadic_return [simp]:
  shows "\<not>\<^sub>b (return True) = return False"
    and "\<not>\<^sub>b (return False) = return True"
unfolding NotMonadic_def UnaryLift_def
by simp_all

lemma ValuePart_NotMonadic [simp]:
  shows "ValuePart (\<not>\<^sub>b m) s = (\<not> ValuePart m s)"
unfolding NotMonadic_def 
by simp

lemma StatePart_NotMonadic [simp]:
  shows "StatePart (\<not>\<^sub>b m) = (\<lambda>s. s)"
unfolding NotMonadic_def 
by simp

definition ConjMonadic (infixr "\<and>\<^sub>b" 84) where
  "ConjMonadic \<equiv> BinaryLift (op \<and>)"

lemma ConjMonadic_return [simp]:
  shows "m \<and>\<^sub>b (return True) = read_state (ValuePart m)"
    and "m \<and>\<^sub>b (return False) = return False"
    and "(return True) \<and>\<^sub>b m = read_state (ValuePart m)"
    and "(return False) \<and>\<^sub>b m = return False"
unfolding ConjMonadic_def BinaryLift_def
by simp_all

lemma ValuePart_ConjMonadic [ValueAndStatePart_simp]:
  shows "ValuePart (m \<and>\<^sub>b m') s = (ValuePart m s \<and> ValuePart m' s)"
unfolding ConjMonadic_def 
by (simp add: ValueAndStatePart_simp)

lemma StatePart_ConjMonadic [simp]:
  shows "StatePart (m \<and>\<^sub>b m') = (\<lambda>s. s)"
unfolding ConjMonadic_def 
by simp

definition DisjMonadic (infixr "\<or>\<^sub>b" 81) where
  "DisjMonadic \<equiv> BinaryLift (op \<or>)"

lemma DisjMonadic_return [simp]:
  shows "m \<or>\<^sub>b (return True) = return True"
    and "m \<or>\<^sub>b (return False) = read_state (ValuePart m)"
    and "(return True) \<or>\<^sub>b m = return True"
    and "(return False) \<or>\<^sub>b m = read_state (ValuePart m)"
unfolding DisjMonadic_def BinaryLift_def
by simp_all

lemma ValuePart_DisjMonadic [ValueAndStatePart_simp]:
  shows "ValuePart (m \<or>\<^sub>b m') s = (ValuePart m s \<or> ValuePart m' s)"
unfolding DisjMonadic_def 
by (simp add: ValueAndStatePart_simp)

lemma StatePart_DisjMonadic [simp]:
  shows "StatePart (m \<or>\<^sub>b m') = (\<lambda>s. s)"
unfolding DisjMonadic_def 
by simp

definition AllMonadic (binder "\<forall>\<^sub>b" 10) where
  "AllMonadic \<equiv> BinderLift All"

lemma ValuePart_AllMonadic [ValueAndStatePart_simp]:
  shows "ValuePart (\<forall>\<^sub>bx. m x) s = (\<forall>a. ValuePart (m a) s)"
unfolding AllMonadic_def 
by (simp add: ValueAndStatePart_simp)

lemma StatePart_AllMonadic [simp]:
  shows "StatePart (\<forall>\<^sub>bx. m x) = (\<lambda>s. s)"
unfolding AllMonadic_def 
by simp

lemma AllMonadic_constant:
  shows "(\<forall>\<^sub>bx. m) = read_state (ValuePart m)"
unfolding AllMonadic_def BinderLift_def
by simp_all

definition ExMonadic (binder "\<exists>\<^sub>b" 10) where
  "ExMonadic \<equiv> BinderLift Ex"

lemma ValuePart_ExMonadic [ValueAndStatePart_simp]:
  shows "ValuePart (\<exists>\<^sub>bx. m x) s = (\<exists>a. ValuePart (m a) s)"
unfolding ExMonadic_def 
by (simp add: ValueAndStatePart_simp)

lemma StatePart_ExMonadic [simp]:
  shows "StatePart (\<exists>\<^sub>bx. m x) = (\<lambda>s. s)"
unfolding ExMonadic_def 
by simp

lemma ExMonadic_constant:
  shows "(\<exists>\<^sub>bx. m) = read_state (ValuePart m)"
unfolding ExMonadic_def BinderLift_def
by simp_all

lemma AllMonadic_constant_readonly [simp]:
  shows "(\<forall>\<^sub>bx. return b) = return b"
    and "(\<forall>\<^sub>bx. read_state f) = read_state f"
    and "(\<forall>\<^sub>bx. m =\<^sub>b m') = (m =\<^sub>b m')"
    and "(\<forall>\<^sub>bx. m \<and>\<^sub>b m') = (m \<and>\<^sub>b m')"
    and "(\<forall>\<^sub>bx. m \<or>\<^sub>b m') = (m \<or>\<^sub>b m')"
    and "(\<forall>\<^sub>bx. (\<forall>\<^sub>by. n y)) = (\<forall>\<^sub>by. n y)"
    and "(\<forall>\<^sub>bx. (\<exists>\<^sub>by. n y)) = (\<exists>\<^sub>by. n y)"
unfolding AllMonadic_constant
by (auto intro: monad_eqI)

lemma ExMonadic_constant_readonly [simp]:
  shows "(\<exists>\<^sub>bx. return b) = return b"
    and "(\<exists>\<^sub>bx. read_state f) = read_state f"
    and "(\<exists>\<^sub>bx. m =\<^sub>b m') = (m =\<^sub>b m')"
    and "(\<exists>\<^sub>bx. m \<and>\<^sub>b m') = (m \<and>\<^sub>b m')"
    and "(\<exists>\<^sub>bx. m \<or>\<^sub>b m') = (m \<or>\<^sub>b m')"
    and "(\<exists>\<^sub>bx. (\<forall>\<^sub>by. n y)) = (\<forall>\<^sub>by. n y)"
    and "(\<exists>\<^sub>bx. (\<exists>\<^sub>by. n y)) = (\<exists>\<^sub>by. n y)"
unfolding ExMonadic_constant
by (auto intro: monad_eqI)

(*<*)
end
(*>*)