(* Author: Kyndylan Nienhuis *)

theory LaTeXoutput

imports Main

begin

section \<open>\LaTeX commands\<close>

(* subsection \<open>New line\<close>

definition LatexNewLine :: unit 
  where "LatexNewLine = ()"
declare LatexNewLine_def [simp]

notation LatexNewLine ("ret")
notation (latex output) LatexNewLine ("\<^latex>\<open>\\\\\<close>") *)

(* subsection \<open>Ampersand\<close>

definition LatexAmp :: unit
  where "LatexAmp = ()"
declare LatexAmp_def [simp]

notation LatexAmp ("amp") 
notation (latex output) LatexAmp ("\<^latex>\<open>&\<close>") *)

subsection \<open>Label\<close>

definition LatexLabel :: "string \<Rightarrow> unit" 
  where "LatexLabel name = ()" 
declare LatexLabel_def [simp]

notation LatexLabel ("lbl (_)")
notation (latex output) LatexLabel ("\<^latex>\<open>\\label{\<close>_\<^latex>\<open>}\<close>")

section \<open>Combining Isabelle and \LaTeX commands\<close>

subsection \<open>Forget left\<close>

definition ForgetLeft :: "unit \<Rightarrow> 'a \<Rightarrow> 'a"
  where "ForgetLeft x y = y"
declare ForgetLeft_def [simp]

notation ForgetLeft ("(\<lbrakk>_\<rbrakk> (_))" [106, 105] 105) 
notation (latex output) ForgetLeft ("(_)(_)")

subsection \<open>Forget right\<close>

definition ForgetRight :: "'a \<Rightarrow> unit \<Rightarrow> 'a"
  where "ForgetRight x y = x"
declare ForgetRight_def [simp]

notation ForgetRight ("((_) \<lbrakk>_\<rbrakk>)" [106, 107] 106) 
notation (latex output) ForgetRight ("(_)(_)")

section \<open>Notation\<close>

subsection \<open>Constructors\<close>

definition IsaConstructor :: "'a \<Rightarrow> 'a" 
  where "IsaConstructor f = f" 
declare IsaConstructor_def [simp]

notation (latex output) IsaConstructor ("\<^latex>\<open>\\IsaConstructor{\<close>_\<^latex>\<open>}\<close>")

subsection \<open>Fields\<close>

definition IsaField :: "'a \<Rightarrow> 'a" 
  where "IsaField f = f" 
declare IsaField_def [simp]

notation (latex output) IsaField ("\<^latex>\<open>\\IsaField{\<close>_\<^latex>\<open>}\<close>")

subsection \<open>Definitions\<close>

definition IsaDefinition :: "'a \<Rightarrow> 'a" 
  where "IsaDefinition f = f" 
declare IsaDefinition_def [simp]

notation (latex output) IsaDefinition ("\<^latex>\<open>\\IsaDefinition{\<close>_\<^latex>\<open>}\<close>")

subsection \<open>Meta equality\<close>

notation (latex output) Pure.eq
  ("((_) \<equiv>//(_))")

subsection \<open>Orders\<close>

definition GreaterThanOrEqual (infix "\<ge>" 50)
  where "GreaterThanOrEqual x y \<equiv> y \<le> x"
declare GreaterThanOrEqual_def [simp]

definition GreaterThan (infix ">" 50)
  where "GreaterThan x y \<equiv> y < x"
declare GreaterThan_def [simp]

subsection \<open>Negation\<close>

definition NegationTextual
  where "NegationTextual \<equiv> Not"
declare NegationTextual_def [simp]

notation NegationTextual ("(not (_))" [40] 40)
notation (latex output) NegationTextual
  ("(\<^latex>\<open>\\IsaKeyword{not}\<close> (_))")

subsection \<open>Implication\<close>

definition ImpliesTextual
  where "ImpliesTextual \<equiv> implies"
declare ImpliesTextual_def [simp]

notation ImpliesTextual ("(if (_)/ then (_))" [26, 25] 25)
notation (latex output) ImpliesTextual
  ("(\<^latex>\<open>\\IsaKeyword{if}\<close> (_)//\<^latex>\<open>\\IsaKeyword{then}\<close> (_))")

subsection \<open>Inline implication\<close>

definition InlineImpliesTextual
  where "InlineImpliesTextual \<equiv> implies"
declare InlineImpliesTextual_def [simp]

notation InlineImpliesTextual ("(inline if (_)/ then (_))" [26, 25] 25)
notation (latex output) InlineImpliesTextual
  ("(\<^latex>\<open>\\IsaKeyword{if}\<close> (_)/ \<^latex>\<open>\\IsaKeyword{then}\<close> (_))")

subsection \<open>Is-defined-as\<close>

definition DefinitionTextual
  where "DefinitionTextual \<equiv> iff"
declare DefinitionTextual_def [simp]

notation DefinitionTextual ("((_)/ is defined as/ (_))" [3, 2] 2)
notation (latex output) DefinitionTextual
  ("((_)/ \<^latex>\<open>\\IsaKeyword{is defined as}\<close>//\<^latex>\<open>\\quad{}\<close>(_))")

subsection \<open>Conjunction\<close>

definition ConjTextual
  where "ConjTextual \<equiv> conj"
declare ConjTextual_def [simp]

notation ConjTextual ("((_)/ and (_))" [35, 36] 35)
notation (latex output) ConjTextual
  ("((_)//\<^latex>\<open>\\IsaKeyword{and}\<close> (_))")

subsection \<open>Inline conjunction\<close>

definition InlineConjTextual
  where "InlineConjTextual \<equiv> conj"
declare InlineConjTextual_def [simp]

notation InlineConjTextual ("((_)/ inline and (_))" [35, 36] 35)
notation (latex output) InlineConjTextual
  ("((_)/ \<^latex>\<open>\\IsaKeyword{and}\<close> (_))")

subsection \<open>Disjunction\<close>

definition DisjTextual
  where "DisjTextual \<equiv> disj"
declare DisjTextual_def [simp]

notation DisjTextual ("((_)/ or (_))" [30, 31] 30)
notation (latex output) DisjTextual
  ("((_)//\<^latex>\<open>\\IsaKeyword{or}\<close> (_))")

subsection \<open>Inline disjunction\<close>

definition InlineDisjTextual
  where "InlineDisjTextual \<equiv> disj"
declare InlineDisjTextual_def [simp]

notation InlineDisjTextual ("((_)/ inline or (_))" [30, 31] 30)
notation (latex output) InlineDisjTextual
  ("((_)/ \<^latex>\<open>\\IsaKeyword{or}\<close> (_))")

subsection \<open>Universal quantification\<close>

definition AllTextual
  where "AllTextual \<equiv> All"
declare AllTextual_def [simp]

syntax "_AllTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool" ("(for all _./ (_))" [0, 10] 10)

syntax (latex output) "_AllTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool"
  ("(\<^latex>\<open>\\IsaKeyword{for all}\<close> (_).//(_))")

(* TODO: the support for multiple binder works only in one direction, strangely enough. *)

translations "for all x y. f" \<rightleftharpoons> "for all x. (for all y. f)"
translations "for all x. f" \<rightleftharpoons> "CONST AllTextual (\<lambda>x. f)"

subsection \<open>Inline universal quantification\<close>

definition InlineAllTextual
  where "InlineAllTextual \<equiv> All"
declare InlineAllTextual_def [simp]

syntax "_InlineAllTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool" ("(inline for all _./ (_))" [0, 10] 10)

syntax (latex output) "_InlineAllTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool"
  ("(\<^latex>\<open>\\IsaKeyword{for all}\<close> (_)./ (_))")

(* TODO: the support for multiple binder works only in one direction, strangely enough. *)

translations "inline for all x y. f" \<rightleftharpoons> "inline for all x. (inline for all y. f)"
translations "inline for all x. f" \<rightleftharpoons> "CONST InlineAllTextual (\<lambda>x. f)"

subsection \<open>Existential quantification\<close>

definition ExTextual
  where "ExTextual \<equiv> Ex"
declare ExTextual_def [simp]

syntax "_ExTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool" ("(exists _./ (_))" [0, 10] 10)

syntax (latex output) "_ExTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool"
  ("(\<^latex>\<open>\\IsaKeyword{exists}\<close> (_).//(_))")

(* TODO: the support for multiple binder works only in one direction, strangely enough. *)

translations "exists x y. f" \<rightleftharpoons> "exists x. (exists y. f)"
translations "exists x. f" \<rightleftharpoons> "CONST ExTextual (\<lambda>x. f)"

subsection \<open>Inline existential quantification\<close>

definition InlineExTextual
  where "InlineExTextual \<equiv> Ex"
declare InlineExTextual_def [simp]

syntax "_InlineExTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool" ("(inline exists _./ (_))" [0, 10] 10)

syntax (latex output) "_InlineExTextual" :: "idts \<Rightarrow> bool \<Rightarrow> bool"
  ("(\<^latex>\<open>\\IsaKeyword{exists}\<close> (_)./ (_))")

(* TODO: the support for multiple binder works only in one direction, strangely enough. *)

translations "inline exists x y. f" \<rightleftharpoons> "inline exists x. (inline exists y. f)"
translations "inline exists x. f" \<rightleftharpoons> "CONST InlineExTextual (\<lambda>x. f)"

subsection \<open>If then else\<close>

notation (latex output) If
  ("(\<^latex>\<open>\\IsaKeyword{if}\<close> (_)//\<^latex>\<open>\\IsaKeyword{then}\<close> (_)//\<^latex>\<open>\\IsaKeyword{else}\<close> (_))")

subsection \<open>Inline if then else\<close>

definition InlineIfThenElse
  where "InlineIfThenElse \<equiv> If"
declare InlineIfThenElse_def [simp]

notation InlineIfThenElse ("(inline if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
notation (latex output) InlineIfThenElse
  ("(\<^latex>\<open>\\IsaKeyword{if}\<close> (_)/ \<^latex>\<open>\\IsaKeyword{then}\<close> (_)/ \<^latex>\<open>\\IsaKeyword{else}\<close> (_))")

subsection \<open>Let binding\<close>

syntax (latex output)
  "_Let" :: "[letbinds, 'a] => 'a"
  ("(\<^latex>\<open>\\IsaKeyword{let}\<close> (_) \<^latex>\<open>\\IsaKeyword{in}\<close>//(_))")

subsection \<open>Inline let\<close>

definition InlineLet
  where "InlineLet \<equiv> Let"
declare InlineLet_def [simp]

syntax "_InlineLet" :: "letbinds \<Rightarrow> 'a \<Rightarrow> 'a" ("(inline let (_) in (_))")

syntax (latex output) "_InlineLet" :: "letbinds \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(\<^latex>\<open>\\IsaKeyword{let}\<close> (_) \<^latex>\<open>\\IsaKeyword{in}\<close>/ (_))")

translations
  "_InlineLet (_binds b bs) e"  \<rightleftharpoons> "_InlineLet b (_InlineLet bs e)"
  "inline let x = a in e"       \<rightleftharpoons> "CONST InlineLet a (\<lambda>x. e)"

subsection \<open>Cases\<close>

syntax (latex output)
  "_case_syntax":: "['a, cases_syn] => 'b"
    ("(\<^latex>\<open>\\IsaKeyword{case}\<close> _//\<^latex>\<open>\\IsaKeyword{of}\<close> _)")
  "_case1":: "['a, 'b] \<Rightarrow> case_syn" ("(2(\<open>unbreakable\<close>_) \<Rightarrow>/ _)")
  "_case2":: "[case_syn, cases_syn] \<Rightarrow> cases_syn" ("(_//_)")

subsection \<open>List concatenation\<close>

definition ReverseCons
  where "ReverseCons t h \<equiv> (h # t)" 
declare ReverseCons_def [simp]

notation ReverseCons ("((_); (_))" [65, 65] 65) 
(* notation (latex output) ReverseCons ("((_); (_))") *)

end