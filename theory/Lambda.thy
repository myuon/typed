theory Lambda
imports Main
begin

fun pred :: "nat \<Rightarrow> nat" where
  "pred 0 = 0"
  | "pred (Suc k) = k"

section {* lambda term with de Bruijn index *}

subsection {* Definition *}
datatype dlambda = lvar nat | labs dlambda | lapp dlambda dlambda

notation
  lapp (infixl "$" 60)

subsection {* shift & subst *}
fun shift' :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> dlambda \<Rightarrow> dlambda" where
  "shift' d c (lvar k) = (if k < c then lvar k else lvar (d k))"
  | "shift' d c (labs t) = labs (shift' d (Suc c) t)"
  | "shift' d c (lapp tx ty) = lapp (shift' d c tx) (shift' d c ty)"

definition shift :: "(nat \<Rightarrow> nat) \<Rightarrow> dlambda \<Rightarrow> dlambda" where
  "shift d M = shift' d 0 M"

fun subst :: "dlambda \<Rightarrow> nat \<Rightarrow> dlambda \<Rightarrow> dlambda" where
  "subst (lvar k) j s = (if k = j then s else lvar k)"
  | "subst (labs t) j s = labs (subst t (Suc j) (shift Suc s))"
  | "subst (lapp t1 t2) j s = lapp (subst t1 j s) (subst t2 j s)"

definition subst_op ("_ [_ \<rightarrow> _]" [80] 70) where
  "subst_op = subst"

fun subst0 :: "dlambda \<Rightarrow> dlambda \<Rightarrow> dlambda" where
  "subst0 M N = shift pred (N [0 \<rightarrow> (shift Suc M)])"
  
value "subst0 (labs (lvar 10)) (lvar 0)"

subsection {* free variables *}

fun FV' :: "nat \<Rightarrow> dlambda \<Rightarrow> nat set" where
  "FV' n (lvar x) = (if x \<ge> n then {x - n} else {})"
  | "FV' n (lapp M N) = FV' n M \<union> FV' n N"
  | "FV' n (labs M) = FV' (n+1) M"

definition FV :: "dlambda \<Rightarrow> nat set" where
  "FV M = FV' 0 M"

lemma "FV (lvar 0) = {0}" by (simp add: FV_def)
lemma "FV (labs (lvar 0)) = {}" by (simp add: FV_def)
lemma "FV (labs (labs (lapp (lvar 0) (lvar 10)))) = {8}" by (simp add: FV_def)

subsubsection {* lemmas *}

lemma subst'_nohit: "\<And>i N. 0 \<notin> FV' i M \<Longrightarrow> M [i \<rightarrow> N] = M"
by (induction M, auto simp add: subst_op_def)

lemma subst0_nohit: "\<And>N. 0 \<notin> FV M \<Longrightarrow> M [0 \<rightarrow> N] = M"
by (simp add: subst'_nohit FV_def)

lemma shift'_FV': "\<And>i j. i \<notin> FV' j (shift' (\<lambda>k. Suc (k + i)) j M)"
by (induction M, auto)

lemma shift_FV: "0 \<notin> FV (shift Suc M)"
using shift'_FV' [of 0 0 M] by (simp add: shift_def FV_def)

lemma shift_nosubst: "(shift Suc M) [0 \<rightarrow> N] = shift Suc M"
by (rule subst0_nohit [OF shift_FV])

lemma unshift'_shift'_id: "\<And>i. shift' pred (Suc i) (shift' Suc i M) = M"
by (induction M, auto)

lemma unshift'_shift'_i_Suci_id: "\<And>i. shift' pred i (shift' Suc i M) = M"
by (induction M, auto)

subsection {* closedness *} 

definition closed :: "dlambda \<Rightarrow> bool" where
  "closed M \<equiv> FV M = {}"

lemma closed_subst_inv: "\<And>N. closed M \<Longrightarrow> M [0 \<rightarrow> N] = M"
apply (rule subst0_nohit)
by (simp add: closed_def)

subsection {* reduction *}
  
inductive beta :: "dlambda \<Rightarrow> dlambda \<Rightarrow> bool" (infixl "=\<beta>" 50) where
  b_beta: "beta (lapp (labs M) N) (subst0 N M)"
| b_refl: "beta M M"
| b_app1: "beta M M' \<Longrightarrow> beta (lapp M Z) (lapp M' Z)"
| b_app2: "beta M M' \<Longrightarrow> beta (lapp Z M) (lapp Z M')"
| b_abs: "beta M M' \<Longrightarrow> beta (labs M) (labs M')"
| b_sym: "beta M N \<Longrightarrow> beta N M"
| b_trans: "\<lbrakk> beta M N; beta N L \<rbrakk> \<Longrightarrow> beta M L"

subsubsection {* Y combinator *}

definition Y where
  "Y \<equiv> labs (lapp (labs (lapp (lvar 1) (lapp (lvar 0) (lvar 0)))) (labs (lapp (lvar 1) (lapp (lvar 0) (lvar 0)))))"

theorem fixedpoint_Y: "lapp Y M =\<beta> lapp M (lapp Y M)"
proof-
  define X where "X = labs (lapp (lvar 1) (lapp (lvar 0) (lvar 0)))"
  define M' where "M' = shift Suc M"
  define W where "W = labs (lapp M' (lapp (lvar 0) (lvar 0)))"
  have Y_is_lXX: "Y = labs (lapp X X)"
    using Y_def X_def by simp

  have H0: "beta (lapp Y M) (lapp (labs (lapp X X)) M)"
    apply (subst Y_is_lXX)
    by (rule b_refl)
  have H1: "beta (lapp (labs (lapp X X)) M) (lapp W W)"
    apply (rule, rule b_beta)
    apply (simp add: X_def)
    apply (simp add: unshift'_shift'_id shift_def subst_op_def)
    apply (simp add: W_def M'_def shift_def)
    by (rule b_refl)
  have H2: "beta (lapp W W) (lapp (labs (lapp M' (lapp (lvar 0) (lvar 0)))) W)"
    by (simp add: W_def, rule b_refl)
  have H3: "beta (lapp (labs (lapp M' (lapp (lvar 0) (lvar 0)))) W) (lapp M (lapp W W))"
    apply (rule, rule b_beta)
    apply (simp add: M'_def)
    using shift_nosubst [of M "shift Suc W"] apply (simp add: subst_op_def)
    apply (simp add: unshift'_shift'_i_Suci_id shift_def)
    by (rule b_refl)
  have H4: "beta (lapp M (lapp Y M)) (lapp M (lapp W W))"
    apply (rule b_app2)
    by (rule, rule H0, rule H1)
  show ?thesis
    apply (rule, rule H0)
    apply (rule, rule H1)
    apply (rule, rule H2)
    apply (rule, rule H3)
    by (rule b_sym, rule H4)
qed

subsection {* definability *}

primrec iter :: "(dlambda \<Rightarrow> dlambda) \<Rightarrow> nat \<Rightarrow> dlambda \<Rightarrow> dlambda" where
  "iter F 0 M = M"
  | "iter F (Suc i) M = F (iter F i M)"

subsubsection {* Church number *}

fun ChurchN :: "nat \<Rightarrow> dlambda" where
  "ChurchN n = labs (labs (iter (\<lambda>k. lapp (lvar 1) k) n (lvar 0)))"

lemma ChurchN_closed: "closed (ChurchN n)"
apply (induction n)
  apply (simp add: closed_def FV_def)
by (simp add: closed_def FV_def)

definition ChAdd :: "dlambda" where
  "ChAdd = labs (labs (labs (labs (lvar 3 $ lvar 1 $ (lvar 2 $ lvar 1 $ lvar 0)))))"
definition ChMult :: "dlambda" where
  "ChMult = labs (labs (labs (lvar 2 $ (lvar 1 $ lvar 0))))"
definition ChExp :: "dlambda" where
  "ChExp = labs (labs (lvar 0 $ lvar 1))"

lemma ChAdd_add: "ChAdd $ ChurchN n $ ChurchN m =\<beta> ChurchN (n + m)"
proof (induction m)
  case 0
  have "ChAdd $ ChurchN n $ ChurchN 0 =\<beta> (labs (labs (labs (labs (lvar 3 $ lvar 1 $ (lvar 2 $ lvar 1 $ lvar 0)))))) $ ChurchN n $ ChurchN 0"
    by (simp add: ChAdd_def, rule b_refl)
  also have "((labs (labs (labs (labs (lvar 3 $ lvar 1 $ (lvar 2 $ lvar 1 $ lvar 0)))))) $ ChurchN n $ ChurchN 0) =\<beta> ((labs (labs (labs (ChurchN n $ lvar 1 $ (lvar 2 $ lvar 1 $ lvar 0))))) $ ChurchN 0)"
    apply (rule b_app1)
    apply (rule, rule b_beta)
    
next
  case (Suc m)
  then show ?case sorry
qed









end