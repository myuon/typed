theory Lambda
imports Nominal
begin

atom_decl name

section {* lambda term with de Bruijn index *}

subsection {* Definition *}

nominal_datatype lambda =
  Var "name"
| App "lambda" "lambda"
| Lam "\<guillemotleft>name\<guillemotright>lambda" ("lam [_]._" [100, 100] 100)

notation
  App (infixl "$" 120)

(* ascii code *)

abbreviation nf where
  "nf == name 102"

abbreviation np where
  "np == name 112"

abbreviation nq where
  "nq == name 113"

abbreviation nx where
  "nx == name 120"

abbreviation ny where
  "ny == name 121"

abbreviation nz where
  "nz == name 122"

subsubsection {* substitution *}  

nominal_primrec subst :: "lambda \<Rightarrow> name \<Rightarrow> lambda \<Rightarrow> lambda" ("_[_::=_]" [150] 120) where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
  | "(App M1 M2)[y ::= s] = App (M1[y ::= s]) (M2[y ::= s])"
  | "x \<sharp> (y,s) \<Longrightarrow> (lam [x].M)[y ::= s] = lam [x].(M[y ::= s])"
  apply (finite_guess)+
  apply (rule TrueI)+
  apply (simp add: abs_fresh)
  apply (fresh_guess)+
  done

lemma forget:
  assumes a: "x \<sharp> M"
  shows "M [x ::= N] = M"
using a
apply (nominal_induct M avoiding: x N rule: lambda.strong_induct)
apply (auto simp add: abs_fresh fresh_atm)
done

lemma fresh_fact:
  fixes z :: "name"
  assumes a: "z \<sharp> s" "z = y \<or> z \<sharp> t"
  shows "z \<sharp> (t[y ::= s])"
using a
apply (nominal_induct t avoiding: z y s rule: lambda.strong_induct)
apply (auto simp add: abs_fresh fresh_atm)
done

lemma substitution:
  assumes a: "x \<noteq> y" "x \<sharp> u"
  shows "(t[x::=s]) [y::=u] = (t[y::=u]) [x::=s[y::=u]]"
using a
apply (nominal_induct t avoiding: x y s u rule: lambda.strong_induct)
apply (auto simp add: fresh_fact forget)
done

lemma subst_rename:
  assumes a: "y \<sharp> t"
  shows "(t[x::=s]) = (([(y,x)]\<bullet>t)[y::=s])"
using a
apply (nominal_induct t avoiding: x y s rule: lambda.strong_induct)
apply (auto simp add: swap_simps fresh_atm abs_fresh)
done

subsection {* beta reduction *}

inductive beta :: "lambda \<Rightarrow> lambda \<Rightarrow> bool" (infixl "\<rightarrow>\<beta>" 50) where
  b_app1 [intro]: "t1 \<rightarrow>\<beta> t2 \<Longrightarrow> App t1 s \<rightarrow>\<beta> App t2 s"
| b_app2 [intro]: "t1 \<rightarrow>\<beta> t2 \<Longrightarrow> App s t1 \<rightarrow>\<beta> App s t2"
| b_abs [intro]: "t1 \<rightarrow>\<beta> t2 \<Longrightarrow> lam[x].t1 \<rightarrow>\<beta> lam[x].t2"
| b_beta [intro]: "App (lam [x].t) s \<rightarrow>\<beta> (t[x::=s])"

inductive long_beta :: "lambda \<Rightarrow> lambda \<Rightarrow> bool" (infixl "\<longrightarrow>\<beta>*" 50) where
  bs_refl [intro]: "t \<longrightarrow>\<beta>* t"
| bs_step [intro]: "t \<rightarrow>\<beta> s \<Longrightarrow> t \<longrightarrow>\<beta>* s"
| bs_trans [trans]: "\<lbrakk> t1 \<longrightarrow>\<beta>* t2; t2 \<longrightarrow>\<beta>* t3 \<rbrakk> \<Longrightarrow> t1 \<longrightarrow>\<beta>* t3"

inductive beta_eq :: "lambda \<Rightarrow> lambda \<Rightarrow> bool" (infixl "=\<beta>" 50) where
  beq_bs [intro]: "t \<longrightarrow>\<beta>* s \<Longrightarrow> t =\<beta> s"
| beq_sym [sym]: "t =\<beta> s \<Longrightarrow> s =\<beta> t"
| beq_trans [trans]: "\<lbrakk> s =\<beta> t; t =\<beta> u \<rbrakk> \<Longrightarrow> s =\<beta> u"

lemma bs_abs:
  assumes "t1 \<longrightarrow>\<beta>* t2"
  shows "\<And>x. lam [x]. t1 \<longrightarrow>\<beta>* lam [x]. t2"
apply (rule long_beta.induct [OF assms], auto)
apply (rule bs_trans, auto)
done

lemma bs_app1:
  assumes "t1 \<longrightarrow>\<beta>* t2"
  shows "\<And>s. App t1 s \<longrightarrow>\<beta>* App t2 s"
apply (rule long_beta.induct [OF assms], auto)
apply (rule bs_trans, auto)
done

lemma bs_app2:
  assumes "t1 \<longrightarrow>\<beta>* t2"
  shows "\<And>s. App s t1 \<longrightarrow>\<beta>* App s t2"
apply (rule long_beta.induct [OF assms], auto)
apply (rule bs_trans, auto)
done

lemma beq_refl [intro]: "t =\<beta> t"
by (rule, rule bs_refl)

lemma beq_app1:
  assumes "t1 =\<beta> t2"
  shows "\<And>s. App t1 s =\<beta> App t2 s"
apply (rule beta_eq.induct [OF assms])
apply (rule, rule bs_app1, simp)
apply (rule beq_sym, simp)
apply (rule beq_trans, simp, simp)
done

lemma beq_app2:
  assumes "t1 =\<beta> t2"
  shows "\<And>s. App s t1 =\<beta> App s t2"
apply (rule beta_eq.induct [OF assms])
apply (rule, rule bs_app2, simp)
apply (rule beq_sym, simp)
apply (rule beq_trans, simp, simp)
done
                                       
subsection {* free variables *}

(*
nominal_primrec FV :: "lambda \<Rightarrow> name set" where
  "FV (Var x) = {x}"
  | "FV (App M N) = FV M \<union> FV N"
  | "FV (lam [x]. M) = FV M - {x}"
  apply (finite_guess)+
  apply simp+
  defer
  apply (fresh_guess)+
  sorry
*)

subsection {* fixedpoint *}

definition Y where
  "Y \<equiv> lam [nf]. (lam [nx]. Var nf $ (Var nx $ Var nx)) $ (lam [nx]. Var nf $ (Var nx $ Var nx))"

theorem fixedpoint_Y:
  assumes Mvar: "nx \<sharp> M"
  shows "Y $ M =\<beta> M $ (Y $ M)"
proof-
  define X where "X = (lam [nx]. (Var nf $ (Var nx $ Var nx)))"
  define W where "W = (lam [nx]. (M $ (Var nx $ Var nx)))"
  have Y_is_lXX: "Y = (lam [nf]. (X $ X))"
    apply (simp add: Y_def X_def)
    done
  have Mvar': "nx \<sharp> (nf,M)"
    using Mvar
    by (simp add: fresh_atm)

  have L0: "(lam [nx].Var nf $ (Var nx $ Var nx))[nf::=M] = W"
    apply (simp add: W_def)
    using Mvar' apply simp
    done
    
  have H0: "Y $ M \<longrightarrow>\<beta>* (lam [nf]. (X $ X)) $ M"
    by (subst Y_is_lXX, simp add: X_def, rule bs_refl)
  also have H1: "(lam [nf]. (X $ X)) $ M \<longrightarrow>\<beta>* (lam [nx]. (M $ (Var nx $ Var nx))) $ W"
    apply (simp add: X_def W_def)
    apply (rule bs_trans, rule, rule b_beta)
    apply (simp add: L0 W_def)
    apply (rule bs_refl)
    done
  also have H2: "(lam [nx]. (M $ (Var nx $ Var nx))) $ W \<longrightarrow>\<beta>* M $ (W $ W)"
    unfolding W_def
    apply (rule bs_trans, rule, rule b_beta)
    using forget [OF Mvar] apply simp
    apply (rule bs_refl)
    done
  also have H3: "M $ (Y $ M) \<longrightarrow>\<beta>* M $ (W $ W)"
    proof-
      have H4: "Y $ M \<longrightarrow>\<beta>* W $ W"
        apply (subst Y_is_lXX)
        apply (rule bs_trans, rule H1, simp add: W_def, rule bs_refl)
        done
      show ?thesis
        using bs_app2 [OF H4] by simp
    qed
  show ?thesis
    apply (rule beq_trans, rule beq_bs)
    apply (rule bs_trans [OF H0], rule bs_trans [OF H1], rule H2)
    apply (rule beq_sym, rule, rule H3)
    done
qed        

subsection {* definability *}

primrec iter :: "(lambda \<Rightarrow> lambda) \<Rightarrow> nat \<Rightarrow> lambda \<Rightarrow> lambda" where
  "iter F 0 M = M"
  | "iter F (Suc i) M = F (iter F i M)"

lemma iter_join: "iter F n (iter F m M) = iter F (n + m) M"
by (induction n, auto)

subsubsection {* Church number *}

fun ChurchN where
  "ChurchN n = lam [nf]. lam [nx]. iter (\<lambda>k. Var nf $ k) n (Var nx)"

definition ChAdd where
  "ChAdd = lam [nx]. lam [ny]. lam [np]. lam [nq]. Var nx $ Var np $ (Var ny $ Var np $ Var nq)"
definition ChMult where
  "ChMult = lam [nx]. lam [ny]. lam [nz]. Var nx $ (Var ny $ Var nz)"
definition ChExp where
  "ChExp = lam [nx]. lam [ny]. Var ny $ Var nx"

text {*
  ChAdd n m
  = (lam x. lam y. lam p. lam q. x p (y p q)) (lam f. lam x. iter (f -) n x) (lam f. lam x. iter (f -) m x)
  = lam p. lam q. (lam f. lam x. iter (f -) n x) p ((lam f. lam x. iter (f -) m x) p q)
  = lam p. lam q. (lam f. lam x. iter (f -) n x) p (iter (p -) m q))
  = lam p. lam q. (iter (p -) n (iter (p -) m q))
  = lam p. lam q. (iter (p -) (n + m) q)
  = n + m
*}

lemma ChAdd_add: "ChAdd $ ChurchN n $ ChurchN m =\<beta> ChurchN (n + m)"
proof-
  have f1y: "ny \<sharp> (nx, ChurchN n)"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f1p: "np \<sharp> (nx, ChurchN n)"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f1q: "nq \<sharp> (nx, ChurchN n)"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f2p: "np \<sharp> (ny, ChurchN m)"
    apply (induction m)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f2q: "nq \<sharp> (ny, ChurchN m)"
    apply (induction m)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f3f: "nf \<sharp> (ny, ChurchN m)"
    apply (induction m)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f3x: "nx \<sharp> (ny, ChurchN m)"
    apply (induction m)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f4x: "nx \<sharp> (nf, Var np)"
    by (simp add: fresh_atm)

  have "ChAdd $ (ChurchN n) $ (ChurchN m) \<longrightarrow>\<beta>* (lam [nx]. lam [ny]. lam [np]. lam [nq]. Var nx $ Var np $ (Var ny $ Var np $ Var nq)) $ (ChurchN n) $ (ChurchN m)"
    by (simp add: ChAdd_def, rule bs_refl)
  also have "... \<longrightarrow>\<beta>* (lam [ny]. lam [np]. lam [nq]. ChurchN n $ Var np $ (Var ny $ Var np $ Var nq)) $ (ChurchN m)"
    apply (rule bs_app1, rule, rule, rule b_beta)
    proof-
      have h: "(lam [ny].lam [np].lam [nq].Var nx $ Var np $ (Var ny $ Var np $ Var nq))[nx::=ChurchN n] = lam [ny].lam [np].lam [nq].(ChurchN n $ Var np $ (Var ny $ Var np $ Var nq))"
        apply (subst subst.simps(3) [OF f1y])
        apply (subst subst.simps(3) [OF f1p])
        apply (subst subst.simps(3) [OF f1q])
        apply simp
        done
      show "(lam [ny].lam [np].lam [nq].Var nx $ Var np $ (Var ny $ Var np $ Var nq))[nx::=ChurchN n] \<longrightarrow>\<beta>* lam [ny].lam [np].lam [nq].ChurchN n $ Var np $ (Var ny $ Var np $ Var nq)"
        by (subst h, rule bs_refl)
    qed
  also have "... \<longrightarrow>\<beta>* lam [np]. lam [nq]. ChurchN n $ Var np $ (ChurchN m $ Var np $ Var nq)"
    apply (rule, rule, rule b_beta)
    proof-
      have h: "(lam [np].lam [nq].ChurchN n $ Var np $ (Var ny $ Var np $ Var nq))[ny::=ChurchN m] = lam [np].lam [nq].ChurchN n $ Var np $ (ChurchN m $ Var np $ Var nq)"
        apply (subst subst.simps(3) [OF f2p])
        apply (subst subst.simps(3) [OF f2q])
        apply (subst lambda.inject(3), subst abs_fun_eq1)
        apply (subst lambda.inject(3), subst abs_fun_eq1)
        apply simp
        using subst.simps(3) [OF f3f] subst.simps(3) [OF f3x]
        by (smt ChurchN.simps f1y forget fresh_prodD(2))
      show "(lam [np].lam [nq].ChurchN n $ Var np $ (Var ny $ Var np $ Var nq))[ny::=ChurchN m] \<longrightarrow>\<beta>* lam [np].lam [nq].ChurchN n $ Var np $ (ChurchN m $ Var np $ Var nq)"
        by (subst h, rule bs_refl)
    qed
  also have "... = lam [np]. lam [nq]. ChurchN n $ Var np $ ((lam [nf]. lam [nx]. iter (\<lambda>k. Var nf $ k) m (Var nx)) $ Var np $ Var nq)" by simp
  also have "... \<longrightarrow>\<beta>* lam [np]. lam [nq]. ChurchN n $ Var np $ (iter (\<lambda>k. Var np $ k) m (Var nq))"
    apply (rule bs_abs, rule bs_abs, rule bs_app2)
    apply (rule, rule, rule, rule b_beta)
    apply (simp add: subst.simps(3) [OF f4x])
    apply (rule bs_trans, rule, rule b_beta)
    proof-
      have h: "(iter (op $ (Var nf)) m (Var nx)[nf::=Var np]) [nx::=Var nq] = iter (op $ (Var np)) m (Var nq)"
        by (induction m, auto)
      show "(iter (op $ (Var nf)) m (Var nx)[nf::=Var np]) [nx::=Var nq] \<longrightarrow>\<beta>* iter (op $ (Var np)) m (Var nq)" 
        by (subst h, rule bs_refl)
    qed
  also have "... = lam [np]. lam [nq]. (lam [nf]. lam [nx]. iter (\<lambda>k. Var nf $ k) n (Var nx)) $ Var np $ (iter (\<lambda>k. Var np $ k) m (Var nq))" by simp
  also have "... \<longrightarrow>\<beta>* lam [np]. lam [nq]. (iter (\<lambda>k. Var np $ k) n (iter (\<lambda>k. Var np $ k) m (Var nq)))"
    apply (rule bs_trans, rule bs_abs, rule bs_abs, rule bs_app1, rule, rule b_beta)
    apply (simp add: subst.simps(3) [OF f4x])
    apply (rule bs_abs, rule bs_abs)
    apply (rule bs_trans, rule, rule b_beta)
    proof-
      have h: "(iter (op $ (Var nf)) n (Var nx)[nf::=Var np]) [nx::=iter (op $ (Var np)) m (Var nq)] \<longrightarrow>\<beta>* iter (op $ (Var np)) n (iter (op $ (Var np)) m (Var nq))"
        apply (induction n, auto)
        apply (rule bs_app2, simp)
        done
      show "(iter (op $ (Var nf)) n (Var nx)[nf::=Var np]) [nx::=iter (op $ (Var np)) m (Var nq)] \<longrightarrow>\<beta>* iter (op $ (Var np)) n (iter (op $ (Var np)) m (Var nq))"
        by (simp add: h)
    qed
  also have "... = lam [np]. lam [nq]. (iter (\<lambda>k. Var np $ k) (n + m) (Var nq))" by (simp add: iter_join)
  also have "... = lam [nf]. lam [nx]. (iter (\<lambda>k. Var nf $ k) (n + m) (Var nx))"
    apply (subst lambda.inject(3), subst alpha)
    apply (rule disjI2, rule, simp, rule)
      apply (simp, subst swap_simps, simp, simp)
    apply (subst lambda.inject(3), subst alpha)
      apply (rule disjI2, rule, simp, rule)
      apply (induction n, simp)
        apply (induction m, simp add: swap_simps, simp add: swap_simps)
        apply (induction m, simp add: swap_simps, simp add: swap_simps)
    apply (induction n, simp)
      apply (induction m, simp add: swap_simps fresh_atm, simp add: swap_simps fresh_atm)
      apply (induction m, simp add: swap_simps fresh_atm, simp add: swap_simps fresh_atm)
    apply (induction n, simp)
      apply (induction m, simp add: swap_simps fresh_atm abs_fresh, simp add: swap_simps fresh_atm abs_fresh)
      apply (induction m, simp add: swap_simps fresh_atm abs_fresh, simp add: swap_simps fresh_atm abs_fresh)
    done
  also have "... = ChurchN (n + m)" by simp
  finally have lem: "(ChAdd $ ChurchN n $ ChurchN m) \<longrightarrow>\<beta>* ChurchN (n + m)" by simp

  show ?thesis
    by (rule, rule lem)
qed


subsubsection {* Boolean, conditional *}

definition Btrue where
  "Btrue = lam [nx]. lam [ny]. Var nx"
definition Bfalse where
  "Bfalse = lam [nx]. lam [ny]. Var ny"

definition Bif where
  "Bif b p q = b $ p $ q"

lemma Bif_true:
  assumes fp: "ny \<sharp> (nx, P)" "ny \<sharp> P"
  shows "Bif Btrue P Q =\<beta> P"
proof rule
  have "Bif Btrue P Q = (lam [nx]. lam [ny]. Var nx) $ P $ Q"
    by (simp add: Bif_def Btrue_def)
  also have "... \<longrightarrow>\<beta>* (lam [ny]. P) $ Q"
    apply (rule bs_app1, rule, rule, rule b_beta)
    apply (subst subst.simps(3) [OF fp(1)], rule bs_abs, simp, rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* P"
    apply (rule, rule, rule b_beta)
    apply (subst forget, rule fp, rule bs_refl)
    done
  finally show "Bif Btrue P Q \<longrightarrow>\<beta>* P" by simp
qed

lemma Bif_false:
  assumes fp: "ny \<sharp> (nx, P)" "ny \<sharp> Q"
  shows "Bif Bfalse P Q =\<beta> Q"
proof rule
  have "Bif Bfalse P Q = (lam [nx]. lam [ny]. Var ny) $ P $ Q"
    by (simp add: Bif_def Bfalse_def)
  also have "... \<longrightarrow>\<beta>* (lam [ny]. Var ny) $ Q"
    apply (rule bs_app1, rule, rule, rule b_beta)
    apply (subst subst.simps(3) [OF fp(1)], rule bs_abs, simp, rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* Q"
    apply (rule, rule, rule b_beta)
    apply (simp, rule bs_refl)
    done
  finally show "Bif Bfalse P Q \<longrightarrow>\<beta>* Q" by simp
qed

subsubsection {* Pairing *}

definition Ppair where
  "Ppair M N = lam [nz]. Var nz $ M $ N"
definition Pproj1 where
  "Pproj1 M = M $ Btrue"
definition Pproj2 where
  "Pproj2 M = M $ Bfalse"

lemma Ppair_proj1:
  assumes "nz \<sharp> M" "nz \<sharp> N" "ny \<sharp> M"
  shows "Pproj1 (Ppair M N) =\<beta> M"
proof rule
  have f1y: "ny \<sharp> (nx, M)"
    apply (simp add: fresh_prod, rule)
    apply (simp add: fresh_atm)
    apply (rule assms)
    done

  have "Pproj1 (Ppair M N) = (lam [nz]. Var nz $ M $ N) $ Btrue"
    by (simp add: Pproj1_def Ppair_def)
  also have "... \<longrightarrow>\<beta>* (Btrue $ M $ N)"
    apply (rule, rule, rule)
    apply (simp, subst forget, rule assms, subst forget, rule assms)
    apply (rule bs_refl)
    done
  also have "... = ((lam [nx]. lam [ny]. Var nx) $ M $ N)"
    by (simp add: Btrue_def)
  also have "... \<longrightarrow>\<beta>* (lam [ny]. M) $ N"
    apply (rule bs_app1, rule, rule, rule)
    apply (subst subst.simps, rule f1y, rule bs_abs, simp)
    apply (rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* M"
    by (rule, rule, rule, subst forget, rule assms, rule bs_refl)
  finally show "Pproj1 (Ppair M N) \<longrightarrow>\<beta>* M" by simp
qed

lemma Ppair_proj2:
  assumes "nz \<sharp> M" "nz \<sharp> N" "ny \<sharp> M"
  shows "Pproj2 (Ppair M N) =\<beta> N"
proof rule
  have f1y: "ny \<sharp> (nx, M)"
    apply (simp add: fresh_prod, rule)
    apply (simp add: fresh_atm)
    apply (rule assms)
    done

  have "Pproj2 (Ppair M N) = (lam [nz]. Var nz $ M $ N) $ Bfalse"
    by (simp add: Pproj2_def Ppair_def)
  also have "... \<longrightarrow>\<beta>* (Bfalse $ M $ N)"
    apply (rule, rule, rule)
    apply (simp, subst forget, rule assms, subst forget, rule assms)
    apply (rule bs_refl)
    done
  also have "... = ((lam [nx]. lam [ny]. Var ny) $ M $ N)"
    by (simp add: Bfalse_def)
  also have "... \<longrightarrow>\<beta>* (lam [ny]. Var ny) $ N"
    apply (rule bs_app1, rule, rule, rule)
    apply (subst subst.simps, rule f1y, rule bs_abs, simp)
    apply (rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* N"
    by (rule, rule, rule, simp, rule bs_refl)
  finally show "Pproj2 (Ppair M N) \<longrightarrow>\<beta>* N" by simp
qed

subsubsection {* definability *}

definition L1defined :: "(nat \<Rightarrow> nat) \<Rightarrow> lambda \<Rightarrow> bool" where
  "L1defined f F = (\<forall>(n :: nat). F $ ChurchN n =\<beta> ChurchN (f n))"

definition L1definable :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "L1definable f = (\<exists>F. L1defined f F)"                            

subsubsection {* initial functions *}

definition iS where
  "iS = Suc"
definition iZ where
  "iZ = (\<lambda>x. 0)"  

lemma iZ_defined: "L1defined iZ (lam [nx]. lam [nf]. lam [ny]. Var ny)"
proof (simp add: L1defined_def iZ_def, auto, rule)
  fix n
  have f1f: "nf \<sharp> (nx, lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx))"
    by (simp add: abs_fresh(1) fresh_atm)
  have f1y: "ny \<sharp> (nx, lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx))"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  
  have "(lam [nx].lam [nf].lam [ny].Var ny) $ (lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx)) \<longrightarrow>\<beta>* (lam [nf].lam [ny].Var ny)"
    apply (rule, rule, rule, subst subst.simps, rule f1f, subst subst.simps, rule f1y)
    apply (subst forget, simp add: fresh_atm, rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* lam [nf].lam [nx].Var nx"
    proof (rule bs_abs)
      have h: "lam [ny].Var ny = lam [nx].Var nx"
        apply (subst lambda.inject, subst alpha, rule disjI2, rule)
        apply (simp add: fresh_atm, rule, simp add: swap_simps, simp add: fresh_atm)
        done
      show "lam [ny].Var ny \<longrightarrow>\<beta>* lam [nx].Var nx"
        by (subst h, rule bs_refl)
    qed
  finally show "(lam [nx].lam [nf].lam [ny].Var ny) $ (lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx)) \<longrightarrow>\<beta>* lam [nf].lam [nx].Var nx"
    by simp
qed

lemma iS_defined: "L1defined iS (lam [nx]. lam [ny]. lam [nz]. Var ny $ (Var nx $ Var ny $ Var nz))"
proof (simp add: L1defined_def iS_def, auto, rule)
  fix n
  have f1x: "ny \<sharp> (nx, lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx))"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f1z: "nz \<sharp> (nx, lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx))"
    apply (induction n)
      apply (simp add: abs_fresh fresh_atm)
      apply (simp add: abs_fresh fresh_atm fresh_prod)
    done
  have f2: "nx \<sharp> (nf, Var ny)"
    by (simp add: fresh_atm)
  
  have "(lam [nx].lam [ny].lam [nz].Var ny $ (Var nx $ Var ny $ Var nz)) $ (lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx)) \<longrightarrow>\<beta>* lam [ny].lam [nz].Var ny $ ((lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx)) $ Var ny $ Var nz)"
    apply (rule, rule, rule, subst subst.simps, rule f1x, rule bs_abs, subst subst.simps, rule f1z, rule bs_abs)
    apply (simp, rule bs_refl)
    done
  also have "... \<longrightarrow>\<beta>* lam [ny].lam [nz].Var ny $ (iter (op $ (Var ny)) n (Var nz))"
    apply (rule bs_abs, rule bs_abs, rule bs_app2)
    apply (rule, rule, rule b_app1, rule b_beta)
    apply (subst subst.simps, rule f2, rule, rule, rule)
    apply (induction n, auto, rule bs_app2, simp)
    done
  also have "... = lam [nf].lam [nx].Var nf $ (iter (op $ (Var nf)) n (Var nx))"
    apply (subst lambda.inject, subst alpha, rule disjI2, rule)
    apply (simp, rule, simp add: swap_simps)
    apply (subst lambda.inject, subst alpha, rule disjI2, rule)
    apply (simp, rule, simp add: swap_simps)
    apply (induction n, auto simp add: swap_simps)
    apply (simp add: fresh_atm)
    apply (induction n, auto simp add: swap_simps fresh_atm)
    apply (induction n)
      apply (simp add: fresh_atm abs_fresh)
      apply (simp add: fresh_atm abs_fresh)
    done
  finally show "(lam [nx].lam [ny].lam [nz].Var ny $ (Var nx $ Var ny $ Var nz)) $ (lam [nf].lam [nx].iter (op $ (Var nf)) n (Var nx)) \<longrightarrow>\<beta>* lam [nf].lam [nx].Var nf $ iter (op $ (Var nf)) n (Var nx)"
    by simp
qed

subsubsection {* lemmas *}

text {*
  L1defined fx Fx <-> \<forall>n. Fx $ (lam f. lam x. iter (f -) n x) = lam f. lam x. iter (f -) (fx n) x
  L1defined gx Gx <-> \<forall>n. Gx $ (lam f. lam x. iter (f -) n x) = lam f. lam x. iter (f -) (gx n) x

  gx (fx n)
  = lam f. lam x. iter (f -) (gx (fx n)) x
  = Gx $ (lam f. lam x. iter (f -) (fx n) x)
  = Gx $ Fx $ n
*}                              

lemma L1definable_closed_under_compose:
  assumes "L1definable f" "L1definable g"
  shows "L1definable (\<lambda>x. f (g x))"
proof (simp add: L1definable_def)
  from assms(1) obtain F where
    F: "L1defined f F"
    using L1definable_def by blast
  from assms(2) obtain G where
    G: "L1defined g G"
    using L1definable_def by blast

  have "\<exists>c :: name. c \<sharp> (F,G)"
    apply (generate_fresh "name")
    by blast
  then obtain x :: name where
    x_fresh: "x \<sharp> (F,G)" by blast
  
  define H where "H = lam [x]. F $ (G $ Var x)"

  have Q: "\<forall>n. H $ ChurchN n =\<beta> ChurchN (f (g n))"
    proof (rule, rule beq_sym)
      fix n                                         
      have "ChurchN (f (g n)) =\<beta> F $ (ChurchN (g n))"
        apply (rule beq_sym)
        using F unfolding L1defined_def apply simp
        done
      also have "... =\<beta> F $ (G $ (ChurchN n))"
        apply (rule beq_sym)
        apply (rule beq_app2)
        using G unfolding L1defined_def apply simp
        done
      also have "... =\<beta> H $ (ChurchN n)"
        apply (rule beq_sym)
        unfolding H_def
        apply (rule, rule, rule, rule)
        apply (subst subst.simps, subst forget, simp add: x_fresh)
        apply (rule bs_app2)
        apply (subst subst.simps, subst forget, simp add: x_fresh)
        apply (rule bs_app2)
        apply (simp, rule bs_refl)
        done
      finally show "ChurchN (f (g n)) =\<beta> H $ ChurchN n" by simp
    qed
  
  show "\<exists>F. L1defined (\<lambda>x. f (g x)) F"
    unfolding L1defined_def
    by (rule, rule Q)
qed

subsection {* reduction *}

nominal_primrec beta_nf where
  "beta_nf (Var v) = True"
  | "beta_nf (App M N) = (if (\<exists>x. \<exists>y. M = lam [x]. y) then False else (beta_nf M \<and> beta_nf N))"
  | "beta_nf (lam [x]. M) = beta_nf M"
  apply (finite_guess)+
  apply (rule TrueI)+
  defer
  apply (fresh_guess)+
  by (simp add: fresh_bool)

inductive long_beta' :: "lambda \<Rightarrow> lambda \<Rightarrow> bool" where
  bs_refl' [intro]: "long_beta' t t"
| bs_cons' [intro]: "\<lbrakk> t1 \<rightarrow>\<beta> t2; long_beta' t2 t3 \<rbrakk> \<Longrightarrow> long_beta' t1 t3"

inductive long_beta_len :: "lambda \<Rightarrow> lambda \<Rightarrow> nat \<Rightarrow> bool" where
  bsl_refl: "long_beta_len t t 0"
| bsl_cons: "\<lbrakk> t1 \<rightarrow>\<beta> t2; long_beta_len t2 t3 m \<rbrakk> \<Longrightarrow> long_beta_len t1 t3 (Suc m)"

lemma long_beta_len_0: "long_beta_len M N 0 = (M = N)"
proof rule
  assume h: "long_beta_len M N 0"
  show "M = N"
    by (rule long_beta_len.cases [OF h], auto)
next
  show "M = N \<Longrightarrow> long_beta_len M N 0" by (simp, rule)
qed

lemma long_beta_len_Suc: "long_beta_len M N (Suc n) = (\<exists>L. M \<rightarrow>\<beta> L \<and> long_beta_len L N n)"
proof rule
  assume h: "long_beta_len M N (Suc n)"
  show "\<exists>L. M \<rightarrow>\<beta> L \<and> long_beta_len L N n"
    by (rule long_beta_len.cases [OF h], auto)
next
  assume "\<exists>L. M \<rightarrow>\<beta> L \<and> long_beta_len L N n"
  then obtain L where L: "M \<rightarrow>\<beta> L" "long_beta_len L N n" by fastforce
  show "long_beta_len M N (Suc n)"
    by (rule, rule L, rule L)
qed

lemma bsl_trans [trans]: "\<And>t1 t2 t3. \<lbrakk> long_beta_len t1 t2 n; long_beta_len t2 t3 m \<rbrakk> \<Longrightarrow> long_beta_len t1 t3 (n + m)"
proof (induction n)
  case 0
  assume hyp: "long_beta_len t1 t2 0" "long_beta_len t2 t3 m"
  have t12: "t1 = t2"
    by (rule long_beta_len.cases [OF hyp(1)], auto)
  show ?case
    by (subst t12, simp, rule hyp)
next
  case (Suc n)
  assume hyp: "\<And>s1 s2 s3. long_beta_len s1 s2 n \<Longrightarrow> long_beta_len s2 s3 m \<Longrightarrow> long_beta_len s1 s3 (n + m)"
  and hyp': "long_beta_len t1 t2 (Suc n)" "long_beta_len t2 t3 m"
  
  obtain t12 where
    t12_prop: "t1 \<rightarrow>\<beta> t12" "long_beta_len t12 t2 n"
    by (rule long_beta_len.cases [OF hyp'(1)], auto)
  
  show ?case
    by (simp, rule, rule t12_prop, rule hyp, rule t12_prop, rule hyp')
qed

lemma long_beta_discard_len: "long_beta_len M N k \<Longrightarrow> M \<longrightarrow>\<beta>* N"
apply (rule long_beta_len.induct, auto)
apply (rule bs_trans, auto)
done

lemma long_beta'_len: "long_beta' M N = (\<exists>k. long_beta_len M N k)"
apply (rule)
  apply (rule long_beta'.induct, simp)
  apply (rule, rule bsl_refl)
proof-
  fix t1 t2 t3
  assume "long_beta' M N"
  and hyp: "t1 \<rightarrow>\<beta> t2" "long_beta' t2 t3" "\<exists>k. long_beta_len t2 t3 k"
  
  from hyp(3) obtain k where k: "long_beta_len t2 t3 k" by fastforce
  show "\<exists>k. long_beta_len t1 t3 k"
    by (rule, rule, rule hyp, rule k)
next
  assume "\<exists>k. long_beta_len M N k"
  then obtain k where k_prop: "long_beta_len M N k" by fastforce

  have Q: "\<And>M N. long_beta_len M N k \<Longrightarrow> long_beta' M N"
    apply (induction k)
      apply (simp add: long_beta_len_0, rule bs_refl')
    apply (simp add: long_beta_len_Suc)
    apply blast
    done
  show "long_beta' M N"
    by (rule Q [OF k_prop])
qed

lemma long_beta_exist_len: "M \<longrightarrow>\<beta>* N = (\<exists>k. long_beta_len M N k)"
apply rule
  apply (rule long_beta.induct, auto)
  apply (rule, rule bsl_refl, rule, rule, simp, rule bsl_refl)
  apply (rule, rule bsl_trans, simp, simp)
proof-
  fix k
  have Q: "\<And>M N. long_beta_len M N k \<Longrightarrow> M \<longrightarrow>\<beta>* N"
    apply (induction k)
      apply (simp add: long_beta_len_0, rule bs_refl)
    apply (auto simp add: long_beta_len_Suc, rule bs_trans, rule bs_step)
    apply simp
    apply simp
    done
  show "long_beta_len M N k \<Longrightarrow> M \<longrightarrow>\<beta>* N"
    by (rule Q)
qed

lemma long_beta_alt: "long_beta M N = long_beta' M N"
by (simp add: long_beta'_len long_beta_exist_len)

subsection {* Parallel reduction *}

lemma subst_eqvt [eqvt]:
  fixes \<pi> :: "name prm"
  shows "\<pi> \<bullet> (t [x ::= s]) = (\<pi> \<bullet> t) [(\<pi> \<bullet> x) ::= (\<pi> \<bullet> s)]"
apply (nominal_induct t avoiding: x s rule: strong_induct)
apply (auto simp add: perm_bij fresh_atm fresh_bij)
done

inductive par_beta :: "lambda \<Rightarrow> lambda \<Rightarrow> bool" (infixl "\<Rightarrow>\<beta>" 50) where
  bp_var: "Var x \<Rightarrow>\<beta> Var x"
| bp_abs: "M \<Rightarrow>\<beta> N \<Longrightarrow> (lam [x].M) \<Rightarrow>\<beta> (lam [x].N)"
| bp_app: "\<lbrakk> M1 \<Rightarrow>\<beta> N1; M2 \<Rightarrow>\<beta> N2 \<rbrakk> \<Longrightarrow> App M1 M2 \<Rightarrow>\<beta> App N1 N2"
| bp_beta': "\<lbrakk> x \<sharp> (N1,N2); M1 \<Rightarrow>\<beta> M2; N1 \<Rightarrow>\<beta> N2 \<rbrakk> \<Longrightarrow> App (lam [x]. M1) N1 \<Rightarrow>\<beta> M2 [x::=N2]"

equivariance par_beta

nominal_inductive par_beta
by (simp_all add: abs_fresh fresh_fact)

lemma bp_beta:
  assumes "M1 \<Rightarrow>\<beta> M2" "N1 \<Rightarrow>\<beta> N2"
  shows "App (lam [x]. M1) N1 \<Rightarrow>\<beta> M2 [x::=N2]"
proof-
  obtain y :: name where y: "y \<sharp> (x,M1,N1,M2,N2)"
    by (rule exists_fresh, rule fin_supp, blast)
  have "App (lam [x]. M1) N1 = App (lam [y]. ([(y,x)] \<bullet> M1)) N1" using y
    by (simp add: lambda.inject alpha' fresh_prod fresh_atm, auto)
  also have "... \<Rightarrow>\<beta> ([(y,x)] \<bullet> M2) [y::=N2]"
    by (rule, simp add: y, rule eqvt, rule assms, rule assms)
  also have "... = M2 [x::=N2]" using y by (simp add: subst_rename[symmetric])
  finally show ?thesis by simp
qed

subsubsection {* coherence *}

lemma pb_from_Var:
  assumes "Var x \<Rightarrow>\<beta> M"
  shows "M = Var x"
by (rule par_beta.cases [OF assms], auto)

subsubsection {* reduction conversion *}

lemma bp_refl: "M \<Rightarrow>\<beta> M"
apply (nominal_induct M rule: lambda.strong_induct)
apply (rule, rule, simp, simp, rule, simp)
done

lemma one_beta_par: "\<And>N. M \<rightarrow>\<beta> N \<Longrightarrow> M \<Rightarrow>\<beta> N"
apply (nominal_induct M rule: lambda.strong_induct)
apply (rule beta.cases, simp+)
proof-
  fix M1 M2 N
  assume hyp: "\<And>N. M1 \<rightarrow>\<beta> N \<Longrightarrow> M1 \<Rightarrow>\<beta> N" "\<And>N. M2 \<rightarrow>\<beta> N \<Longrightarrow> M2 \<Rightarrow>\<beta> N" "M1 $ M2 \<rightarrow>\<beta> N"
  show "M1 $ M2 \<Rightarrow>\<beta> N"
    apply (rule beta.induct [OF hyp(3)])
    apply (rule, simp, rule bp_refl)
    apply (rule, rule bp_refl, simp)
    apply (rule, simp, rule bp_beta, rule bp_refl, rule bp_refl)
    done
next
  fix n M N
  assume hyp: "\<And>N. M \<rightarrow>\<beta> N \<Longrightarrow> M \<Rightarrow>\<beta> N" "lam [n]. M \<rightarrow>\<beta> N"
  show "lam [n]. M \<Rightarrow>\<beta> N"
    apply (rule beta.induct [OF hyp(2)])
    apply (rule, simp, rule bp_refl)
    apply (rule, rule bp_refl, simp)
    apply (rule, simp, rule bp_beta, rule bp_refl, rule bp_refl)
    done
qed

lemma par_beta_long: "\<And>N. M \<Rightarrow>\<beta> N \<Longrightarrow> M \<longrightarrow>\<beta>* N"
apply (nominal_induct M rule: lambda.strong_induct)
apply (rule par_beta.cases, simp, simp, rule bs_refl, simp, simp, simp)
proof-
  fix M1 M2 N
  assume hyp: "\<And>N. M1 \<Rightarrow>\<beta> N \<Longrightarrow> M1 \<longrightarrow>\<beta>* N" "\<And>N. M2 \<Rightarrow>\<beta> N \<Longrightarrow> M2 \<longrightarrow>\<beta>* N" "M1 $ M2 \<Rightarrow>\<beta> N"
  show "M1 $ M2 \<longrightarrow>\<beta>* N"
    apply (rule par_beta.induct [OF hyp(3)], rule bs_refl, rule bs_abs, simp)
    apply (rule bs_trans, rule bs_app1, simp, rule bs_app2, simp)
    apply (rule bs_trans, rule bs_app1, rule bs_abs, simp, rule bs_trans, rule bs_app2, simp, rule, rule)
    done
next
  fix n M N
  assume hyp: "\<And>N. M \<Rightarrow>\<beta> N \<Longrightarrow> M \<longrightarrow>\<beta>* N" "lam [n]. M \<Rightarrow>\<beta> N"
  have "\<exists>N'. N = lam [n]. N' \<longrightarrow> M \<Rightarrow>\<beta> N'"
    apply (rule par_beta.induct [OF hyp(2)], simp)
    using bp_refl apply auto[1] apply simp
    using bp_refl apply blast
    done
  then obtain N' where
    N': "N = lam [n]. N' \<Longrightarrow> M \<Rightarrow>\<beta> N'"
    using bp_refl by blast
  show "lam [n]. M \<longrightarrow>\<beta>* N"
    apply (cases "N = lam [n]. N'")
    apply (simp, rule bs_abs, rule hyp, rule N', simp)
    apply (rule par_beta.induct [OF hyp(2)])
    apply (rule bs_refl, rule bs_abs, simp)
    apply (rule bs_trans, rule bs_app1, simp, rule bs_app2, simp)
    apply (rule bs_trans, rule bs_app1, rule bs_abs, simp)
    apply (rule bs_trans, rule bs_app2, simp, rule, rule)
    done
qed    

text {*
  lemma: Pi => Qi ==> P1[x:=P2] => Q1[x:=Q2]
  proof.
    induction on P1 => Q1.
    ia) x => x
    x[x:=P2] => x[x:=Q2] by assumption
    ib) y => y
    clear
    ii) \y.M => \y.N (where M => N)
    \y.M[x:=P2] => \y.N[x:=Q2] by IH
    iii) M1M2 => N1N2 (where Mi => Ni)
    M1M2[x:=P2] = M1[x:=P2]M2[x:=P2] => N1[x:=Q2]N2[x:=Q2] = N1N2[x:=P2]
    iv) (\y.M1)M2 => N1[y:=N2] (where Mi => Ni)
    ((\y.M1)M2)[x:=P2] = (\y.M1[x:=P2])M2[x:=P2] => N1[x:=Q2][y:=(N2[x:=Q2])] = N1[y:=N2][x:=Q2] by subst.
  qed
*}

lemma abs_alpha: "c \<sharp> (xa,M) \<Longrightarrow> lam [xa]. M = lam [c]. ([(c,xa)] \<bullet> M)"
apply (subst lambda.inject, subst alpha)
apply (rule disjI2, rule)
apply (simp add: fresh_prod, simp add: fresh_atm, fastforce)
apply (rule, simp add: perm_swap(2))
apply (subst fresh_left, simp, simp add: swap_simps)
done

(*
lemma par_beta_subst:
  "\<And>P2 Q2. \<lbrakk> P1 \<Rightarrow>\<beta> Q1; P2 \<Rightarrow>\<beta> Q2 \<rbrakk> \<Longrightarrow> P1 [x ::= P2] \<Rightarrow>\<beta> Q1 [x ::= Q2]"
apply (rule par_beta.induct [of P1 Q1], simp)
apply (simp, rule, rule)
prefer 2
apply (simp, rule, simp, simp)
proof-
  fix P2 Q2 M N xa
  assume hyp: "P1 \<Rightarrow>\<beta> Q1" "P2 \<Rightarrow>\<beta> Q2" "M \<Rightarrow>\<beta> N" "M[x::=P2] \<Rightarrow>\<beta> N[x::=Q2]"
  show "(lam [xa].M)[x::=P2] \<Rightarrow>\<beta> (lam [xa].N)[x::=Q2]"
    proof (generate_fresh "name")
      fix c :: name
      assume c_fresh: "c \<sharp> (M, N, P2, Q2, x, xa)"
      have "(lam [xa].M)[x::=P2] = (lam [c]. ([(c,xa)] \<bullet> M))[x::=P2]"
        by (subst abs_alpha [of c], auto simp add: c_fresh)
      also have "... = lam [c]. (([(c,xa)] \<bullet> M)[x::=P2])"
        by (auto simp add: c_fresh)
      also have "... = lam [c]. (([(c,xa)]\<bullet>M)[([(c,xa)]\<bullet>x)::=([(c,xa)]\<bullet>P2)])"
        apply (subst forget)
        

      show "(lam [xa].M)[x::=P2] \<Rightarrow>\<beta> (lam [xa].N)[x::=Q2]"
        apply (subst p, subst subst.simps, simp add: c_fresh)
        apply (simp)
*)

lemma long_beta_induct_len:
  assumes "M \<longrightarrow>\<beta>* N"
  and "\<And>M. P M M"
  and "\<And>L M N. M \<rightarrow>\<beta> L \<Longrightarrow> P L N \<Longrightarrow> P M N"
  shows "P M N"
using assms(1) apply (simp add: long_beta_alt)
proof-
  have Q: "\<And>M N. long_beta' M N \<Longrightarrow> P M N"
    apply (rule long_beta'.induct, auto)
      apply (rule assms(2))
      apply (rule assms(3), simp, simp)
    done

  show ?thesis
    using assms(1) apply (simp add: long_beta_alt)
    apply (rule Q, simp)
    done
qed

lemma beta_var: "Var n \<longrightarrow>\<beta>* N \<Longrightarrow> Var n = N"
proof (simp add: long_beta_exist_len, auto)
  fix l
  assume hyp: "long_beta_len (Var n) N l"
  
  have "long_beta_len (Var n) N l \<Longrightarrow> Var n = N"
    apply (induction l)
    apply (simp add: long_beta_len_0)
    proof-
      fix l
      assume p: "long_beta_len (Var n) N l \<Longrightarrow> Var n = N" "long_beta_len (Var n) N (Suc l)"
      from long_beta_len_Suc p(2)
      obtain L where
        L: "Var n \<rightarrow>\<beta> L" by fastforce
      have False
        by (rule beta.cases [OF L], auto)
      then show "Var n = N" by simp
    qed
  then show "Var n = N"
    using hyp by simp
qed    

lemma nat_leq_induct_2:
  fixes n :: nat
  assumes "P 0" "P 1"
  and "\<forall>n\<ge>2. \<forall>m<n. P m \<longrightarrow> P n"
  shows "P n"
proof (induction n, rule assms)
  fix n
  show "P n \<Longrightarrow> P (Suc n)"
    apply (induction n)
      using assms(2) apply simp
    using assms(3)
    using numeral_2_eq_2 by force
qed

text {*
  lemma: beta_nf M; M => N ==> M = N
  proof:
    induction on M -> N
    i) Var x -> N  ~>  Var x => N  ~>  
*}

lemma beta_nf_pb: "\<lbrakk> beta_nf M; M \<Rightarrow>\<beta> N \<rbrakk> \<Longrightarrow> M = N"
using par_beta.induct [of M N "\<lambda>x y. beta_nf x \<longrightarrow> x \<Rightarrow>\<beta> y \<longrightarrow> x = y"]
by (rule, auto)

lemma beta_nf_lb: "\<lbrakk> beta_nf M; M \<longrightarrow>\<beta>* N \<rbrakk> \<Longrightarrow> M = N"
apply (simp add: long_beta_alt)
using long_beta'.induct [of M N "\<lambda>x y. beta_nf x \<and> long_beta' x y \<longrightarrow> x = y"] apply rule
apply (simp, simp, simp)
defer
apply (simp, simp)
proof (rule)
  fix t1 t2 t3
  assume "beta_nf M" "long_beta' M N"
  and hyp: "t1 \<rightarrow>\<beta> t2" "long_beta' t2 t3" "beta_nf t2 \<longrightarrow> t2 = t3" "beta_nf t1 \<and> long_beta' t1 t3"
  have p1: "t1 = t2"
    apply (rule beta_nf_pb, simp add: hyp(4))
    apply (rule one_beta_par, rule hyp)
    done
  also have "... = t3"
    using hyp by (simp add: p1)
  finally show "t1 = t3" by simp 
qed

lemma beta_subst: "M \<rightarrow>\<beta> M' \<Longrightarrow> M[x::=N] \<rightarrow>\<beta> M'[x::=N]"
apply (rule beta.induct [of M M'])
apply (simp, simp, rule b_app1, simp, simp, rule b_app2, simp)

end