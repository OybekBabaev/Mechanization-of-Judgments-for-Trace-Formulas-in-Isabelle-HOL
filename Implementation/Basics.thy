theory Basics
  imports Main "HOL-Library.Finite_Map"
begin

type_synonym var = string
type_synonym method_name = string
type_synonym stm_var = string

datatype aexp = Num int
  | Var var
  | Add aexp aexp (infix "\<oplus>" 60)
  | Sub aexp aexp (infix "\<ominus>" 60)
  | Mul aexp aexp (infix "\<otimes>" 65)

datatype bexp = TRUE
  | FALSE
  | Eq aexp aexp      (infix "==" 60)
  | Leq aexp aexp
  | Not bexp
  | And bexp bexp
  | Or bexp bexp

datatype S = SKIP
  | Assign var aexp    ("_ := _" [1000, 56] 56)
  | Seq    S S         (infixr ";;" 55)
  | If     bexp S S    ("IF _ THEN _ ELSE _ FI" [55, 55, 55] 56)
  | Call   method_name
  | SVar   stm_var

type_synonym Rec = "S \<times> (method_name, S) fmap"

type_synonym state = "(var, int) fmap"

text \<open>only allow non-empty traces\<close>
type_synonym trace = "state \<times> state list"

abbreviation read_val :: "state \<Rightarrow> var \<Rightarrow> int" ("_\<langle>_\<rangle>" [75, 75] 75) where
  "s\<langle>x\<rangle> \<equiv> case fmlookup s x of Some n \<Rightarrow> n | _ \<Rightarrow> 0"

abbreviation write_val :: "('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap" 
  ("_\<langle>_ \<longmapsto> _\<rangle>" [80, 60, 60] 80) where
  "s\<langle>x \<longmapsto> n\<rangle> \<equiv> fmupd x n s"

primrec eval\<^sub>A :: "aexp \<Rightarrow> state \<Rightarrow> int" ("\<bbbA>\<lbrakk>_\<rbrakk>(_)" [60, 71] 71) where
  "\<bbbA>\<lbrakk>Num n\<rbrakk>(s) = n" |
  "\<bbbA>\<lbrakk>Var x\<rbrakk>(s) = s\<langle>x\<rangle>" |
  "\<bbbA>\<lbrakk>a \<oplus> a'\<rbrakk>(s) = \<bbbA>\<lbrakk>a\<rbrakk>(s) + \<bbbA>\<lbrakk>a'\<rbrakk>(s)" |
  "\<bbbA>\<lbrakk>a \<ominus> a'\<rbrakk>(s) = \<bbbA>\<lbrakk>a\<rbrakk>(s) - \<bbbA>\<lbrakk>a'\<rbrakk>(s)" |
  "\<bbbA>\<lbrakk>a \<otimes> a'\<rbrakk>(s) = \<bbbA>\<lbrakk>a\<rbrakk>(s) * \<bbbA>\<lbrakk>a'\<rbrakk>(s)"

primrec eval\<^sub>B :: "state \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<Turnstile>" 65) where
  "_ \<Turnstile> TRUE = True" |
  "_ \<Turnstile> FALSE = False" |
  "s \<Turnstile> (Eq a a') = (\<bbbA>\<lbrakk>a\<rbrakk>(s) = \<bbbA>\<lbrakk>a'\<rbrakk>(s))" |
  "s \<Turnstile> (Leq a a') = (\<bbbA>\<lbrakk>a\<rbrakk>(s) \<le> \<bbbA>\<lbrakk>a'\<rbrakk>(s))" |
  "s \<Turnstile> (Not b) = (\<not> s \<Turnstile> b)" |
  "s \<Turnstile> (And b b') = (s \<Turnstile> b \<and> s \<Turnstile> b')" |
  "s \<Turnstile> (Or b b') = (s \<Turnstile> b \<or> s \<Turnstile> b')"

end