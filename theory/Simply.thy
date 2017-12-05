theory Simply
imports Lambda
begin

section {* Simply typed *}

subsection {* Typing rules *}

nominal_datatype simply = TVar string | TArr simply simply (infixr "\<rightarrow>" 90)

inductive valid :: "(name \<times> simply) list \<Rightarrow> bool" where
  valid_nil: "valid []"
| valid_cons: "\<lbrakk> valid \<Gamma>; x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> valid ((x,T)#\<Gamma>)"

equivariance valid

lemma elim_valid_cons: "valid ((x,T)#\<Gamma>) \<Longrightarrow> valid \<Gamma> \<and> x \<sharp> \<Gamma>"
by (cases rule: valid.cases, auto)

lemma fresh_notin:
  fixes x :: name and \<Gamma> :: "(name \<times> simply) list"
  assumes "x \<sharp> \<Gamma>"
  shows "(x,y) \<notin> set \<Gamma>"
using assms
apply (induction \<Gamma> arbitrary: x, simp, simp add: fresh_list_cons)
apply (rule, auto simp add: fresh_prod fresh_atm)
done

lemma valid_ctx_unique:
  assumes "valid \<Gamma>" "(x,\<sigma>) \<in> set \<Gamma>" "(x,\<tau>) \<in> set \<Gamma>"
  shows "\<sigma> = \<tau>"
using assms apply (induction \<Gamma> arbitrary: x, auto)
  using fresh_notin apply simp
  using fresh_notin apply simp
done

inductive typed ("_ \<turnstile> _ : _" 40) where
  st_var: "\<lbrakk> valid \<Gamma>; (x,\<sigma>) \<in> set \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<sigma>"
| st_app: "\<lbrakk> \<Gamma> \<turnstile> M : (\<sigma> \<rightarrow> \<tau>); \<Gamma> \<turnstile> N : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App M N : \<tau>"
| st_abs: "\<lbrakk> x \<sharp> \<Gamma>; (x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (lam [x]. M) : (\<sigma> \<rightarrow> \<tau>)"

equivariance typed

lemma fresh_type:
  fixes x :: name
  and T :: simply
  shows "x \<sharp> T"
by (nominal_induct T rule:simply.strong_induct, simp_all add: fresh_string)
  
nominal_inductive typed
  by (simp_all add: fresh_type abs_fresh)

fun dom where
  "dom \<Gamma> = (\<lambda>(x,y). x) ` \<Gamma>"

subsubsection {* lemma *}
  
lemma weak_ctx:
  assumes "set \<Gamma> \<subseteq> set \<Gamma>'" "valid \<Gamma>'" "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma>' \<turnstile> M : \<sigma>"
using assms(1) assms(2) apply (nominal_induct avoiding: \<Gamma>' rule: typed.strong_induct [OF assms(3)])
apply (rule, simp, fastforce)
using st_app apply blast
apply (rule, simp, simp)
by (simp add: subset_insertI2 valid.intros(2))

lemma typed_valid: "\<Gamma> \<turnstile> M : A \<Longrightarrow> valid \<Gamma>"
apply (nominal_induct rule: typed.strong_induct, auto)
using elim_valid_cons by blast

lemma ctx_swap_head_typed: "(x,t) # (y,s) # \<Gamma> \<turnstile> M : A \<Longrightarrow> (y,s) # (x,t) # \<Gamma> \<turnstile> M : A"
proof (rule weak_ctx [of "(x,t) # (y,s) # \<Gamma>"], auto)
  assume "(x, t) # (y, s) # \<Gamma> \<turnstile> M : A"
  hence "valid ((x,t) # (y, s) # \<Gamma>)" by (simp add: typed_valid)
  hence "valid ((y,s) # \<Gamma>) \<and> x \<sharp> (y,\<Gamma>)"
    using elim_valid_cons
    by (meson fresh_list_cons fresh_prod)
  hence fresh: "valid \<Gamma>" "y \<sharp> \<Gamma>" "x \<noteq> y" "x \<sharp> \<Gamma>"
    using elim_valid_cons apply blast
    using \<open>valid ((y, s) # \<Gamma>) \<and> x \<sharp> (y, \<Gamma>)\<close> elim_valid_cons apply blast
    apply (metis \<open>valid ((x, t) # (y, s) # \<Gamma>)\<close> elim_valid_cons fresh_notin list.set_intros(1))
    by (simp add: \<open>valid ((y, s) # \<Gamma>) \<and> x \<sharp> (y, \<Gamma>)\<close>)
  show "valid ((y, s) # (x, t) # \<Gamma>)"
    apply (rule, rule, rule fresh, rule fresh)
    by (metis fresh(2) fresh(3) fresh_atm fresh_list_cons fresh_prod fresh_type)
qed    

subsubsection {* coherence *}

lemma par_ignore_prm:
  fixes \<pi> :: "name prm" and T :: simply
  shows "\<pi> \<bullet> T = T"
apply (nominal_induct T rule:simply.strong_induct, auto)
by (simp add: perm_string)

lemma typed_rename: "\<lbrakk> x \<sharp> \<Gamma>; y \<sharp> \<Gamma>; (x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>; lam [x].M = lam [y].M' \<rbrakk> \<Longrightarrow> (y,\<sigma>)#\<Gamma> \<turnstile> M' : \<tau>"
proof (simp add: lambda.inject)
  assume assms: "x \<sharp> \<Gamma>" "y \<sharp> \<Gamma>" "(x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>" "[x].M = [y].M'"
  have p: "[(x,y)] \<bullet> M = M'"
    by (smt abs_fresh(1) abs_perm alpha' assms(4) perm_fresh_fresh perm_swap(1))
  
  have "(x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>" by (rule assms) 
  then have "([(x,y)] \<bullet> ((x,\<sigma>)#\<Gamma>)) \<turnstile> ([(x,y)] \<bullet> M) : ([(x,y)] \<bullet> \<tau>)"
    by (rule eqvt)
  then have "((y,\<sigma>)# ([(x,y)] \<bullet> \<Gamma>)) \<turnstile> ([(x,y)] \<bullet> M) : \<tau>"
    by (simp add: par_ignore_prm swap_simps(1))
  then show "(y,\<sigma>)#\<Gamma> \<turnstile> M' : \<tau>"
    apply (subst p [symmetric])
    using assms(1) assms(2)
    by (simp add: perm_fresh_fresh)
qed

lemma gen_typed_valid: "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> valid \<Gamma>"
apply (nominal_induct rule: typed.strong_induct)
  apply (auto)
  by (metis list.distinct(1) list.inject valid.simps)

lemma gen_typed_var: "\<Gamma> \<turnstile> Var x : \<sigma> \<Longrightarrow> (x,\<sigma>) \<in> set \<Gamma>"
by (cases rule:typed.cases, auto simp add: lambda.inject)

lemma gen_typed_app_exist: "\<Gamma> \<turnstile> App M N : \<tau> \<Longrightarrow> \<exists>\<sigma>. (\<Gamma> \<turnstile> M : (\<sigma> \<rightarrow> \<tau>)) \<and> (\<Gamma> \<turnstile> N : \<sigma>)"
by (cases rule:typed.cases, auto simp add: lambda.inject)

lemma gen_typed_abs_exist: "\<lbrakk> \<Gamma> \<turnstile> lam [x]. M : \<rho>; x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> \<exists>\<sigma> \<tau>. ((x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>) \<and> (\<rho> = \<sigma> \<rightarrow> \<tau>)"
proof (cases rule:typed.cases, auto)
  fix xa \<sigma> Ma \<tau>
  assume assms: "\<Gamma> \<turnstile> lam [xa].Ma : \<sigma> \<rightarrow> \<tau>" "x \<sharp> \<Gamma>" "lam [x].M = lam [xa].Ma" "xa \<sharp> \<Gamma>" "(xa, \<sigma>)#\<Gamma> \<turnstile> Ma : \<tau>" "\<rho> = \<sigma> \<rightarrow> \<tau>"
  obtain y :: name where y: "y \<sharp> M"
    by (rule exists_fresh, rule fin_supp, auto)
  have "(x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>"
    by (rule typed_rename, rule assms(4), rule assms, rule assms, rule assms(3) [symmetric])
  then show "\<exists>\<sigma>' \<tau>'. ((x, \<sigma>') # \<Gamma> \<turnstile> M : \<tau>') \<and> (\<sigma> \<rightarrow> \<tau> = \<sigma>' \<rightarrow> \<tau>')"
    by auto
qed    

lemma gen_typed_app:
  assumes "\<Gamma> \<turnstile> M $ N : \<tau>"
  obtains \<sigma> where "\<Gamma> \<turnstile> M : (\<sigma> \<rightarrow> \<tau>)" "\<Gamma> \<turnstile> N : \<sigma>"
using gen_typed_app_exist [OF assms] by auto 

lemma gen_typed_abs:
  assumes "\<Gamma> \<turnstile> lam [x]. M : \<rho>" "x \<sharp> \<Gamma>"
  obtains \<sigma> \<tau> where "(x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>" "\<rho> = \<sigma> \<rightarrow> \<tau>"
using gen_typed_abs_exist [OF assms] by auto

subsubsection {* Soundness *}

lemma typed_var_unique: "(x,\<sigma>)#\<Gamma> \<turnstile> Var x : \<tau> \<Longrightarrow> \<sigma> = \<tau>"
apply (cases rule: typed.strong_cases, auto simp add: lambda.inject)
using elim_valid_cons apply (rule, simp)
  using fresh_notin apply auto
apply (generate_fresh name)
by (meson gen_typed_valid gen_typed_var list.set_intros(1) valid_ctx_unique)

lemma subst_typed: "\<lbrakk> (x,\<sigma>)#\<Gamma> \<turnstile> M : \<tau>; \<Gamma> \<turnstile> N : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> M[x::=N] : \<tau>"
apply (nominal_induct M avoiding: x N \<sigma> \<Gamma> arbitrary: \<tau> rule: lambda.strong_induct)
  apply (auto elim!: gen_typed_var)
  using typed_var_unique apply fastforce
  using gen_typed_var [of "(x,\<sigma>)#\<Gamma>" _ \<sigma>] apply simp
  apply (meson Pair_inject gen_typed_valid gen_typed_var set_ConsD st_var)
    using gen_typed_app_exist
    apply (meson st_app)
proof-
  fix name lambda x N \<sigma> \<Gamma> \<tau>
  assume name_fresh: "name \<sharp> x" "name \<sharp> N" "name \<sharp> \<sigma>" "name \<sharp> \<Gamma>"
  and IH: "\<And>b ba bb bc \<tau>. (b, bb) # bc \<turnstile> lambda : \<tau> \<Longrightarrow> bc \<turnstile> ba : bb \<Longrightarrow> bc \<turnstile> lambda[b::=ba] : \<tau>"
  and hyp: "(x, \<sigma>) # \<Gamma> \<turnstile> lam [name].lambda : \<tau>" "\<Gamma> \<turnstile> N : \<sigma>"
  
  obtain \<tau>1 \<tau>2 where tau: "\<tau> = \<tau>1 \<rightarrow> \<tau>2" "(name, \<tau>1) # (x, \<sigma>) # \<Gamma> \<turnstile> lambda : \<tau>2"
    by (metis fresh_list_cons fresh_prod fresh_type gen_typed_abs_exist hyp(1) name_fresh(1) name_fresh(4))
  have "(name,\<tau>1) # \<Gamma> \<turnstile> lambda[x::=N] : \<tau>2"
    apply (rule IH)
    apply (rule ctx_swap_head_typed)
    apply (rule tau)
    apply (rule weak_ctx [of \<Gamma>], auto)
    apply (rule, rule typed_valid, rule hyp, rule name_fresh, rule hyp)
    done
  thus "\<Gamma> \<turnstile> lam [name].lambda[x::=N] : \<tau>"
    apply (simp add: tau(1))
    by (simp add: name_fresh(4) st_abs)
qed

lemma preservation_one:
  assumes "M \<rightarrow>\<beta> M'"
  shows "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> M' : \<sigma>"
apply (nominal_induct avoiding: \<Gamma> arbitrary: \<sigma> rule: beta.strong_induct [OF assms])
apply (erule gen_typed_app, rule)
prefer 2 apply (simp, simp)
apply (erule gen_typed_app, rule)
apply (simp, simp)
apply (erule gen_typed_abs, simp, simp, rule, simp, simp)
apply (erule gen_typed_app, erule gen_typed_abs, simp)
apply (rule subst_typed, simp add: simply.inject, simp add: simply.inject)
done

lemma preservation:
  assumes "M \<longrightarrow>\<beta>* M'"
  shows "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> M' : \<sigma>"
by (induct rule: long_beta.induct [OF assms], auto simp add: preservation_one)

nominal_primrec Value :: "lambda \<Rightarrow> bool" where
  "Value (lam [_]._) = True"
  | "Value (Var _) = False"
  | "Value (App _ _) = False"
by (finite_guess+, rule+, fresh_guess+)

lemma Value_eqvt[eqvt]:
  fixes \<pi> :: "name prm" and M :: lambda
  shows "\<pi> \<bullet> Value M = Value (\<pi> \<bullet> M)"
by (nominal_induct M rule: lambda.strong_induct, auto)

lemma Value_abs:
  assumes "Value M"
  obtains x M' where "M = lam [x]. M'"
using assms by (nominal_induct M rule: lambda.strong_induct, auto)
  
lemma progress: "[] \<turnstile> M : \<sigma> \<Longrightarrow> Value M \<or> (\<exists>M'. M \<rightarrow>\<beta> M')"
proof-
  have "\<And>\<Gamma> thesis. \<lbrakk> \<Gamma> \<turnstile> M : \<sigma>; \<Gamma> = [] \<rbrakk> \<Longrightarrow> Value M \<or> (\<exists>M'. M \<rightarrow>\<beta> M')"
    proof-
      fix \<Gamma> thesis
      show "\<lbrakk> \<Gamma> \<turnstile> M : \<sigma>; \<Gamma> = [] \<rbrakk> \<Longrightarrow> Value M \<or> (\<exists>M'. M \<rightarrow>\<beta> M')"
        apply (nominal_induct rule: typed.strong_induct, auto)
        apply (erule Value_abs, simp, rule, rule b_beta)
        done
    qed
  thus "[] \<turnstile> M : \<sigma> \<Longrightarrow> Value M \<or> (\<exists>M'. M \<rightarrow>\<beta> M')" by simp
qed

theorem soundness:
  assumes "[] \<turnstile> M : \<sigma>" "M \<longrightarrow>\<beta>* M'"
  shows "Value M' \<or> (\<exists> M''. M' \<rightarrow>\<beta> M'')"
by (rule progress, rule preservation, rule assms, rule assms)

end
