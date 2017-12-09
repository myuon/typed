theory CR
imports Lambda
begin

inductive par_beta (infixl "\<Rightarrow>\<beta>" 50) where
  pb_var: "Var x \<Rightarrow>\<beta> Var x"
| pb_app: "\<lbrakk> t1 \<Rightarrow>\<beta> t2; s1 \<Rightarrow>\<beta> s2 \<rbrakk> \<Longrightarrow> t1 $ s1 \<Rightarrow>\<beta> t2 $ s2"
| pb_abs: "t \<Rightarrow>\<beta> s \<Longrightarrow> lam[x].t \<Rightarrow>\<beta> lam[x].s"
| pb_beta: "\<lbrakk> x \<sharp> (s1,s2); t1 \<Rightarrow>\<beta> t2; s1 \<Rightarrow>\<beta> s2 \<rbrakk> \<Longrightarrow> (lam [x]. t1) $ s1 \<Rightarrow>\<beta> t2 [x ::= s2]"

equivariance par_beta

nominal_inductive par_beta
by (simp_all add: abs_fresh subst_fresh)

lemma pb_refl: "t \<Rightarrow>\<beta> t"
apply (induction t rule: lambda.induct)
apply (rule, rule, simp, simp, rule, simp)
done

lemma one_to_par: "M \<rightarrow>\<beta> N \<Longrightarrow> M \<Rightarrow>\<beta> N"
apply (induction rule: beta.induct)
  apply (rule, simp, rule pb_refl)
  apply (rule, rule pb_refl, simp)
  apply (rule, simp, rule)
  apply (auto simp add: pb_refl)
done

abbreviation long_beta (infixl "\<longrightarrow>\<beta>" 50) where
  "long_beta == beta\<^sup>*\<^sup>*"

lemma lb_app1: "t1 \<longrightarrow>\<beta> t2 \<Longrightarrow> t1 $ s \<longrightarrow>\<beta> t2 $ s"
apply (induction rule: rtranclp_induct)
apply (simp, rule, simp, rule, simp)
done

lemma lb_app2: "s1 \<longrightarrow>\<beta> s2 \<Longrightarrow> t $ s1 \<longrightarrow>\<beta> t $ s2"
apply (induction rule: rtranclp_induct)
apply (simp, rule, simp, rule, simp)
done

lemma lb_abs: "t \<longrightarrow>\<beta> s \<Longrightarrow> lam[x].t \<longrightarrow>\<beta> lam[x].s"
apply (induction rule: rtranclp_induct)
apply (simp, rule, simp, rule, simp)
done

lemma perm_fresh_lambda:
  fixes M :: lambda and x y :: var
  assumes "y \<sharp> (x,M)"
  shows "x \<sharp> ([(y,x)] \<bullet> M)"
using assms
apply (nominal_induct M rule: lambda.strong_induct)
  apply (metis fresh_bij fresh_prodD(2) swap_simps(1))
  apply (simp add: fresh_prod)
  apply (metis fresh_bij fresh_prodD(2) swap_simps(1))
done

lemma perm_fresh_lambda':
  fixes M :: lambda and x y :: var
  assumes "y \<sharp> (x,M)"
  shows "x \<sharp> ([(x,y)] \<bullet> M)"
using assms
apply (nominal_induct M rule: lambda.strong_induct)
  apply (metis fresh_bij fresh_prodD(2) swap_simps(2))
  apply (simp add: fresh_prod)
  apply (metis fresh_bij fresh_prodD(2) swap_simps(2))
done

lemma lb_subst1: "t \<rightarrow>\<beta> s \<Longrightarrow> t[x ::= p] \<longrightarrow>\<beta> s[x ::= p]"
apply (nominal_induct avoiding: x p rule: beta.strong_induct, simp_all)
  apply (rule lb_app1, simp, rule lb_app2, simp)
  apply (rule lb_abs, simp)
  apply (rule rtranclp_trans, rule, rule, rule, rule subst_gfresh, simp_all)
  apply (subst substitution [symmetric], auto simp add: fresh_atm)
done

lemma lb_subst: "\<lbrakk> t1 \<longrightarrow>\<beta> t2; s1 \<longrightarrow>\<beta> s2 \<rbrakk> \<Longrightarrow> t1[x ::= s1] \<longrightarrow>\<beta> t2[x ::= s2]"
apply (induction rule: rtranclp_induct)
  apply (nominal_induct t1 avoiding: x s1 s2 rule: lambda.strong_induct)
  apply (simp, simp, rule rtranclp_trans, rule lb_app1)
  defer
  apply (rule lb_app2, simp)
  apply (simp, rule lb_abs, simp)
  apply (auto, rule rtranclp_trans, simp)
  apply (simp add: lb_subst1)
done

lemma par_to_longbeta: "M \<Rightarrow>\<beta> N \<Longrightarrow> M \<longrightarrow>\<beta> N"
apply (induction rule: par_beta.induct)
  apply (simp)
  apply (rule rtranclp_trans, rule lb_app1, simp, rule lb_app2, simp)
  apply (rule lb_abs, simp)
  apply (rule rtranclp_trans, rule r_into_rtranclp, rule, simp)
  apply (simp add: lb_subst)
done

nominal_primrec nonabs :: "lambda \<Rightarrow> bool" where
  "nonabs (lam [_]._) = False"
  | "nonabs (Var _) = True"
  | "nonabs (App _ _) = True"
by (finite_guess+, rule+, fresh_guess+)

lemma nonabs_eqvt[eqvt]:
  fixes \<pi> :: "var prm" and M :: lambda
  shows "\<pi> \<bullet> nonabs M = nonabs (\<pi> \<bullet> M)"
by (nominal_induct M rule: lambda.strong_induct, auto)

inductive bstar (infixl "\<longrightarrow>*" 50) where
  bs_var: "Var x \<longrightarrow>* Var x"
| bs_abs: "M \<longrightarrow>* M' \<Longrightarrow> lam [x]. M \<longrightarrow>* lam [x]. M'"
| bs_app: "\<lbrakk> nonabs M1; M1 \<longrightarrow>* M2; N1 \<longrightarrow>* N2 \<rbrakk> \<Longrightarrow> M1 $ N1 \<longrightarrow>* M2 $ N2"
| bs_beta': "\<lbrakk> x \<sharp> (N1,N2); M1 \<longrightarrow>* M2; N1 \<longrightarrow>* N2 \<rbrakk> \<Longrightarrow> (lam [x]. M1) $ N1 \<longrightarrow>* M2 [x ::= N2]"

equivariance bstar

nominal_inductive bstar
by (simp_all add: abs_fresh subst_fresh)

lemma bs_beta:
  assumes "M1 \<longrightarrow>* M2" "N1 \<longrightarrow>* N2"
  shows "(lam [x]. M1) $ N1 \<longrightarrow>* M2 [x ::= N2]"
proof-
  obtain y :: var where y: "y \<sharp> (x,M1,M2,N1,N2)"
    using exists_fresh [of "(x,M1,M2,N1,N2)"]
    using fs_var1 by blast
  have "(lam [x]. M1) $ N1 = (lam [y]. ([(y,x)]\<bullet>M1)) $ N1"
    apply (simp add: lambda.inject alpha, rule disjI2, auto)
    using y apply (meson fresh_atm fresh_prodD(1))
    apply (simp add: perm_swap)
    apply (rule perm_fresh_lambda, simp add: y)
    done
  also have "\<dots> \<longrightarrow>* ([(y,x)]\<bullet>M2)[y ::= N2]"
    by (rule, simp add: y, simp add: assms bstar.eqvt, rule assms)
  also have "\<dots> = M2[x ::= N2]"
    by (auto simp add: subst_rename y)
  finally show "(lam [x]. M1) $ N1 \<longrightarrow>* M2 [x ::= N2]"
    by simp
qed

lemma elim_pb_var: "Var x \<Rightarrow>\<beta> N \<Longrightarrow> N = Var x"
by (cases rule: par_beta.cases, auto)

lemma elim_pb_abs:
  assumes "lam [x]. M \<Rightarrow>\<beta> N'" "x \<sharp> N'"
  obtains N where "M \<Rightarrow>\<beta> N" "N' = lam [x]. N"
using assms
apply (cases rule: par_beta.cases, auto simp add: abs_fresh lambda.inject alpha)
by (metis fresh_bij par_beta.eqvt perm_swap(2) swap_simps(1))

lemma elim_pb_app:
  assumes "M1 $ M2 \<Rightarrow>\<beta> N"
  obtains N1 N2 where "N = N1 $ N2" "M1 \<Rightarrow>\<beta> N1" "M2 \<Rightarrow>\<beta> N2"
     | x P P' L where "M1 = lam[x]. P" "P \<Rightarrow>\<beta> P'" "N = P'[x ::= L]" "M2 \<Rightarrow>\<beta> L" "x \<sharp> (M2,L)"
using assms
apply (cases rule: par_beta.cases, auto simp add: lambda.inject)
done

lemma elim_pb_app_nonabs:
  assumes "M1 $ M2 \<Rightarrow>\<beta> N" "nonabs M1"
  obtains N1 N2 where "N = N1 $ N2" "M1 \<Rightarrow>\<beta> N1" "M2 \<Rightarrow>\<beta> N2"
using assms
apply (cases rule: par_beta.cases, auto simp add: lambda.inject)
done

lemma elim_pb_app_beta:
  assumes "(lam [x]. M1) $ M2 \<Rightarrow>\<beta> N" "x \<sharp> (M2,N)"
  obtains N1 N2 where "N = (lam [x]. N1) $ N2" "M1 \<Rightarrow>\<beta> N1" "M2 \<Rightarrow>\<beta> N2"
  | N1 N2 where "N = N1[x ::= N2]" "M1 \<Rightarrow>\<beta> N1" "M2 \<Rightarrow>\<beta> N2"
using assms
apply (cases rule: par_beta.strong_cases [of _ _ _ x x], auto)
apply (auto simp add: lambda.inject)
apply (erule elim_pb_abs, simp add: fresh_prod, simp)
apply (simp add: abs_fresh)
apply (simp add: abs_fresh abs_fun_eq1)
done

lemma pb_subst: "\<lbrakk> t1 \<Rightarrow>\<beta> s1; t2 \<Rightarrow>\<beta> s2 \<rbrakk> \<Longrightarrow> t1 [x ::= t2] \<Rightarrow>\<beta> s1 [x ::= s2]"
apply (nominal_induct avoiding: x t2 s2 rule: par_beta.strong_induct, auto)
  apply (rule, rule, simp, simp)
  apply (rule, simp)
  apply (simp add: fresh_atm pb_beta subst_gfresh' substitution)
done
    
lemma par_to_star: "\<lbrakk> t \<longrightarrow>* t1; t \<Rightarrow>\<beta> t2 \<rbrakk> \<Longrightarrow> t2 \<Rightarrow>\<beta> t1"
apply (nominal_induct avoiding: t2 rule: bstar.strong_induct)
  using elim_pb_var apply blast
  apply (erule elim_pb_abs, simp, simp, rule, simp)
  apply (erule elim_pb_app, simp, rule, simp, simp, simp)
  apply (erule elim_pb_app_beta, simp, simp, rule, simp, simp, simp)
  apply (simp, rule pb_subst, simp, simp)
done

lemma bstar_fresh:
  fixes x :: var
  assumes "M \<longrightarrow>* N"
  shows "x \<sharp> M \<Longrightarrow> x \<sharp> N"
using assms apply (nominal_induct rule: bstar.strong_induct, auto)
apply (auto simp add: abs_fresh subst_gfresh)
apply (auto simp add: subst_fresh)
done

lemma elim_bs_abs:
  assumes "lam [x]. t \<longrightarrow>* s"
  obtains t' where "t \<longrightarrow>* t'" "s = lam [x]. t'"
proof-
  have Q: "lam [x]. t \<longrightarrow>* s \<Longrightarrow> \<exists>t'. t \<longrightarrow>* t' \<and> s = lam [x]. t'"
    apply (cases rule: bstar.strong_cases [of _ _ _ x x], auto)
    apply (auto simp add: lambda.inject alpha bstar_fresh abs_fresh)
    done
  show "(\<And>t'. t \<longrightarrow>* t' \<Longrightarrow> s = lam [x].t' \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using Q [OF assms] by blast
qed

lemma lambda_nonabs_case:
  fixes M :: lambda
  shows "(nonabs M \<Longrightarrow> thesis) \<Longrightarrow> (\<And>x M'. M = lam [x]. M' \<Longrightarrow> thesis) \<Longrightarrow> thesis"
by (nominal_induct M rule: lambda.strong_induct, auto)

lemma star_exist:
  obtains t' where "t \<longrightarrow>* t'"
proof-
  have "\<exists>t'. t \<longrightarrow>* t'"
    apply (nominal_induct t rule: lambda.strong_induct, auto)
    apply (rule, rule)
    defer
    apply (rule, rule, simp)
    proof-
      fix M1 M2 N N'
      assume hyp: "M1 \<longrightarrow>* N" "M2 \<longrightarrow>* N'"
      show "\<exists>t'. M1 $ M2 \<longrightarrow>* t'"
        apply (rule_tac lambda_nonabs_case [of M1])
        apply (rule, rule, simp, rule hyp, rule hyp)
        proof-
          fix x M'
          assume M1: "M1 = lam [x].M'"
          then obtain N1 where N1: "N = lam [x].N1" "M' \<longrightarrow>* N1"
            using elim_bs_abs hyp(1) by blast
          have "M1 $ M2 \<longrightarrow>* N1 [x ::= N']"
            by (simp add: M1, rule bs_beta, simp add: N1, simp add: hyp)
          thus ?thesis by blast
        qed
    qed
  thus "(\<And>t'. t \<longrightarrow>* t' \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed
  
lemma par_confluent:
  assumes "t \<Rightarrow>\<beta> t1" "t \<Rightarrow>\<beta> t2"
  obtains s where "t1 \<Rightarrow>\<beta> s" "t2 \<Rightarrow>\<beta> s"
proof-
  obtain t' where t': "t \<longrightarrow>* t'"
    using star_exist by auto 
  have "t1 \<Rightarrow>\<beta> t'" "t2 \<Rightarrow>\<beta> t'"
    using par_to_star [OF t'] assms by auto
  thus "(\<And>s. t1 \<Rightarrow>\<beta> s \<Longrightarrow> t2 \<Rightarrow>\<beta> s \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

abbreviation long_par_beta (infixl "\<Longrightarrow>\<beta>" 50) where
  "long_par_beta == par_beta\<^sup>*\<^sup>*"

lemma long_pb_iff_long_b: "t \<Longrightarrow>\<beta> s \<longleftrightarrow> t \<longrightarrow>\<beta> s"
apply rule
apply (induct rule: rtranclp_induct)
  apply simp
  apply (rule rtranclp_trans, simp, simp add: par_to_longbeta)
apply (induct rule: rtranclp_induct)
  apply simp
  apply (rule rtranclp_trans, simp, rule r_into_rtranclp, simp add: one_to_par)
done

lemma CR:
  assumes "t \<longrightarrow>\<beta> t1" "t \<longrightarrow>\<beta> t2"
  obtains s where "t1 \<longrightarrow>\<beta> s" "t2 \<longrightarrow>\<beta> s"
proof-
  have CR_one_long: "\<And>t t1 t2. \<lbrakk> t \<Longrightarrow>\<beta> t2; t \<Rightarrow>\<beta> t1 \<rbrakk> \<Longrightarrow> \<exists>s. t1 \<Longrightarrow>\<beta> s \<and> t2 \<Rightarrow>\<beta> s"
    proof-
      fix t t1 t2
      show "\<lbrakk> t \<Longrightarrow>\<beta> t2; t \<Rightarrow>\<beta> t1 \<rbrakk> \<Longrightarrow> \<exists>s. t1 \<Longrightarrow>\<beta> s \<and> t2 \<Rightarrow>\<beta> s"
        proof (induct arbitrary: t1 rule: rtranclp_induct)
          fix t1 show "t \<Rightarrow>\<beta> t1 \<Longrightarrow> \<exists>s. t1 \<Longrightarrow>\<beta> s \<and> t \<Rightarrow>\<beta> s"
            by (rule par_confluent, rule pb_refl, simp, blast)
        next
          fix y z t1
          assume t: "t \<Longrightarrow>\<beta> y" "y \<Rightarrow>\<beta> z" and hyp: "\<And>t1. t \<Rightarrow>\<beta> t1 \<Longrightarrow> \<exists>s. t1 \<Longrightarrow>\<beta> s \<and> y \<Rightarrow>\<beta> s" and t2: "t \<Rightarrow>\<beta> t1"
          obtain s where s: "t1 \<Longrightarrow>\<beta> s" "y \<Rightarrow>\<beta> s" using hyp t t2 by blast
          obtain s' where s': "s \<Rightarrow>\<beta> s'" "z \<Rightarrow>\<beta> s'" using par_confluent [OF t(2) s(2)] by blast
          have "t1 \<Longrightarrow>\<beta> s'" "z \<Rightarrow>\<beta> s'"
            by (rule, rule s, rule s', rule s')
          thus "\<exists>s. t1 \<Longrightarrow>\<beta> s \<and> z \<Rightarrow>\<beta> s"
            by blast
        qed
    qed

  have CR_long_long: "\<lbrakk> t \<Longrightarrow>\<beta> t1; t \<Longrightarrow>\<beta> t2 \<rbrakk> \<Longrightarrow> \<exists>s. t1 \<Longrightarrow>\<beta> s \<and> t2 \<Longrightarrow>\<beta> s"
    apply (induct arbitrary: t2 rule: rtranclp_induct)
      apply (rule, rule, simp, simp)
      using CR_one_long apply (meson rtranclp.rtrancl_into_rtrancl)
    done

  have "t \<Longrightarrow>\<beta> t1" "t \<Longrightarrow>\<beta> t2"
    using assms by (simp add: long_pb_iff_long_b, simp add: long_pb_iff_long_b)
  hence "\<exists>s. t1 \<Longrightarrow>\<beta> s \<and> t2 \<Longrightarrow>\<beta> s"
    by (rule CR_long_long)
  hence "\<exists>s. t1 \<longrightarrow>\<beta> s \<and> t2 \<longrightarrow>\<beta> s"
    by (simp add: long_pb_iff_long_b)
  thus "(\<And>s. t1 \<longrightarrow>\<beta> s \<Longrightarrow> t2 \<longrightarrow>\<beta> s \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by blast
qed
end