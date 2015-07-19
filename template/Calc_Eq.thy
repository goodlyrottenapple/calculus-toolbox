theory (*calc_name_eq*)
imports Main (*calc_name*) (*calc_name_se*) "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

(*calc_structure_se_to_de*)


(*calc_structure_de_to_se*)


lemma DE_to_SE_Atprop_freevars[simp]:
  fixes t
  assumes "freevars t = {}"
  shows "\<exists>t'. DE_to_SE_Atprop t = Some t'"
using assms
by (induct t, simp+)

lemma SD_DS_Atprop_Id:
  fixes a :: Atprop
  defines "a' \<equiv> SE_to_DE_Atprop a"
  shows "case (DE_to_SE_Atprop a') of Some x \<Rightarrow> x = a"
using assms
by (metis (poly_guards_query) DE_to_SE_Atprop.simps(1) SE_to_DE_Atprop.simps option.simps(5))

lemma DS_SD_Atprop_Id:
  fixes a
  assumes "freevars a = {}"
  shows "case (DE_to_SE_Atprop a) of Some x \<Rightarrow> SE_to_DE_Atprop x = a"
using assms
by (metis (mono_tags) Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty DE_to_SE_Atprop.simps(1) SE_to_DE_Atprop.simps option.simps(5))

(*---------------------------*)

lemma DE_to_SE_Action_freevars[simp]:
  fixes t
  assumes "freevars t = {}"
  shows "\<exists>t'. DE_to_SE_Action t = Some t'"
using assms
by (induct t, simp+)

lemma SD_DS_Action_Id:
  fixes a :: Action
  defines "a' \<equiv> SE_to_DE_Action a"
  shows "case (DE_to_SE_Action a') of Some x \<Rightarrow> x = a"
using assms
by (metis (poly_guards_query) DE_to_SE_Action.simps(1) SE_to_DE_Action.simps option.simps(5))


lemma DS_SD_Action_Id:
  fixes a
  assumes "freevars a = {}"
  shows "case (DE_to_SE_Action a) of Some x \<Rightarrow> SE_to_DE_Action x = a"
using assms
by (metis (mono_tags) Action.exhaust freevars_Action.simps(1) insert_not_empty DE_to_SE_Action.simps(1) SE_to_DE_Action.simps option.simps(5))

(*---------------------------*)

lemma DE_to_SE_Agent_freevars[simp]:
  fixes t
  assumes "freevars t = {}"
  shows "\<exists>t'. DE_to_SE_Agent t = Some t'"
using assms
by (induct t, simp+)

lemma SD_DS_Agent_Id:
  fixes a :: Action
  defines "a' \<equiv> SE_to_DE_Agent a"
  shows "case (DE_to_SE_Agent a') of Some x \<Rightarrow> x = a"
using assms
by (metis (poly_guards_query) DE_to_SE_Agent.simps(1) SE_to_DE_Agent.simps option.simps(5))


lemma DS_SD_Agent_Id:
  fixes a
  assumes "freevars a = {}"
  shows "case (DE_to_SE_Agent a) of Some x \<Rightarrow> SE_to_DE_Agent x = a"
using assms
by (metis (mono_tags) Agent.exhaust freevars_Agent.simps(1) insert_not_empty DE_to_SE_Agent.simps(1) SE_to_DE_Agent.simps option.simps(5))





lemma DE_to_SE_Formula_freevars:
  fixes t
  assumes "freevars t = {}"
  shows "\<exists>t'. DE_to_SE_Formula t = Some t'"
using assms
apply (induct t)
apply simp_all
apply (case_tac x1a, simp_all)
using DE_to_SE_Action_freevars apply fastforce+
apply (case_tac x1a, simp_all)
using DE_to_SE_Agent_freevars apply fastforce+
using DE_to_SE_Atprop_freevars apply fastforce
apply (case_tac x2, auto)
by (case_tac x, simp_all)+


lemma SE_to_DE_Formula_freevars:
  fixes t
  shows "freevars (SE_to_DE_Formula t) = {}"
by (induct t) simp+

lemma SD_DS_Formula_Id:
  fixes a
  shows "case (DE_to_SE_Formula (SE_to_DE_Formula a)) of Some x \<Rightarrow> x = a"
apply (induct a)
by (simp add: option.case_eq_if)+


lemma DS_SD_Formula_Id:
  fixes a
  assumes "freevars a = {}"
  shows "case (DE_to_SE_Formula a) of Some x \<Rightarrow> SE_to_DE_Formula x = a"
using assms
apply (induct a)
apply simp_all
apply (case_tac x1a, simp_all)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x1a, simp_all)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x, simp_all)
apply (case_tac x2, simp_all add: option.case_eq_if)
apply (case_tac x, simp_all)
apply (case_tac x, simp_all)
done

lemma DS_SD_Formula_Id2:
  fixes a
  assumes "freevars a = {}"
  shows "SE_to_DE_Formula (the (DE_to_SE_Formula a)) = a"
using assms DE_to_SE_Formula_freevars DS_SD_Formula_Id by fastforce

lemma foldr_bigu_equiv[simp]:
  fixes x fu
  shows "foldr op \<union> (map fu x) {} = \<Union>(image fu (set x))"
by(induct x, simp_all)

lemma DE_to_SE_Structure_freevars:
  fixes t
  assumes "freevars t = {}"
  shows "\<exists>t'. DE_to_SE_Structure t = Some t'"
using assms
apply (induct t)
apply simp_all
apply (case_tac x1, simp_all)
using DE_to_SE_Action_freevars apply fastforce+
apply (case_tac x1, simp_all)
using DE_to_SE_Agent_freevars apply fastforce+
defer
apply (case_tac x2, auto)
using DE_to_SE_Formula_freevars apply fastforce
using DE_to_SE_Action_freevars apply fastforce
apply (case_tac x, auto)
proof -
case goal1 thus ?case
  proof(induct x, simp)
  case goal1 
    then obtain t' where t'_def: "DE_to_SE_Structure (;;\<^sub>S x) = Some t'" by auto
    from goal1(3) have "\<forall>e \<in> set x. freevars e = {}" by simp_all
    then have "\<forall>xa \<in> set x. \<exists>t'. DE_to_SE_Structure xa = Some t'" by (simp add: goal1(2))
    then have "\<exists>x'. DE_to_SE_Structure (;;\<^sub>S x) = Some (Structure_Bigcomma x')"
    proof(induct x, simp)
    case goal1 
      then have "\<exists>x'. DE_to_SE_Structure (;;\<^sub>S x) = Some (;;\<^sub>S x')" by simp
      then obtain x' where x'_def: "DE_to_SE_Structure (;;\<^sub>S x) = Some (;;\<^sub>S x')" by auto
      from goal1 obtain a' where a'_def: "DE_to_SE_Structure (a) = Some a'" by auto
      with x'_def have "DE_to_SE_Structure (;;\<^sub>S (a # x)) = Some (;;\<^sub>S (a'#x'))" by simp
      thus ?case by simp
    qed
    then obtain x' where x'_def: "DE_to_SE_Structure (;;\<^sub>S x) = Some (Structure_Bigcomma x')" by auto
    with goal1 obtain a' where a'_def: "DE_to_SE_Structure a = Some a'" by fastforce
    with t'_def x'_def  have "DE_to_SE_Structure (DEAK_Core.Structure_Bigcomma (a#x)) = Some (Structure_Bigcomma (a'#x'))" by auto
    thus ?case by simp
  qed
qed

lemma SE_to_DE_Structure_freevars:
  fixes t
  shows "freevars (SE_to_DE_Structure t) = {}"
by (induct t rule: SE_to_DE_Structure.induct, simp_all add: SE_to_DE_Formula_freevars)



lemma SD_DS_Structure_Id:
  fixes a :: Structure
  shows "\<exists>x. (DE_to_SE_Structure (SE_to_DE_Structure a)) = Some x \<and> x = a"
apply (induct a)
apply (auto simp add: option.case_eq_if)
defer
using DE_to_SE_Formula_freevars SE_to_DE_Formula_freevars apply blast
apply (metis (mono_tags, lifting) SD_DS_Formula_Id option.simps(5))
proof -
case goal1 thus ?case by(induct x, auto)
qed


lemma SD_DS_Structure_Id2:
  fixes a :: Structure
  shows "the (DE_to_SE_Structure (SE_to_DE_Structure a)) = a"
using SD_DS_Structure_Id by auto

lemma DS_SD_Structure_Id:
  fixes a
  assumes "freevars a = {}"
  shows "\<exists>x. (DE_to_SE_Structure a) = Some x \<and> SE_to_DE_Structure x = a"
using assms
apply (induct a)
apply simp_all
apply (case_tac x1, simp_all)
apply (metis (mono_tags, lifting) DE_to_SE_Action_freevars DS_SD_Action_Id SE_to_DE_Structure.simps(2) option.simps(5))
apply (metis (mono_tags, lifting) DE_to_SE_Action_freevars DS_SD_Action_Id SE_to_DE_Structure.simps(1) option.simps(5))

apply (case_tac x1, simp_all)
apply (metis (mono_tags, lifting) DE_to_SE_Agent_freevars DS_SD_Agent_Id SE_to_DE_Structure.simps(3) option.simps(5))
apply (metis (mono_tags, lifting) DE_to_SE_Agent_freevars DS_SD_Agent_Id SE_to_DE_Structure.simps(4) option.simps(5))
defer
apply (case_tac x2, simp_all)
apply auto
apply (simp add: DE_to_SE_Formula_freevars DS_SD_Formula_Id2 option.case_eq_if)
apply (case_tac x, simp_all)
apply (case_tac x, simp_all)
proof -
case goal1 thus ?case
  proof(induct x, simp)
  case goal1 
    then have assms: "\<exists>xx. DE_to_SE_Structure (;;\<^sub>S x) = Some xx \<and> SE_to_DE_Structure xx = ;;\<^sub>S x" "\<exists>xx. DE_to_SE_Structure a = Some xx \<and> SE_to_DE_Structure xx = a" by simp_all
    then obtain a' where a'_def: "DE_to_SE_Structure a = Some a' \<and> SE_to_DE_Structure a' = a" by auto
    from assms obtain list where list_def: "DE_to_SE_Structure (;;\<^sub>S x) = Some list \<and> SE_to_DE_Structure list = ;;\<^sub>S x" by auto
    with assms
    obtain x' where x'_def: "list = (Structure_Bigcomma x')"
      by (smt DEAK_Core.Structure.distinct(16) DEAK_Core.Structure.distinct(28) DEAK_Core.Structure.distinct(30) DEAK_Core.Structure.distinct(34) DEAK_Core.Structure.distinct(36) DEAK_Core.Structure.distinct(4) SE_to_DE_Structure.elims)
      (* get rid of smt!!! *)
    with a'_def list_def have "DE_to_SE_Structure (;;\<^sub>S (a # x)) = Some (Structure_Bigcomma (a'#x'))" by simp
    thus ?case using a'_def list_def x'_def by auto
  qed
qed


lemma DS_SD_Structure_Id2:
  fixes a
  assumes "freevars a = {}"
  shows "SE_to_DE_Structure (the (DE_to_SE_Structure a)) = a"
using assms DS_SD_Structure_Id by fastforce



lemma DE_to_SE_Sequent_freevars:
  fixes l r
  assumes "freevars (l \<turnstile>\<^sub>S r) = {}"
  shows "\<exists>l' r'. DE_to_SE_Sequent (l \<turnstile>\<^sub>S r) = Some (l' \<turnstile>\<^sub>S r')"
by (metis (no_types, lifting) DE_to_SE_Sequent.simps(1) DS_SD_Structure_Id assms freevars_Sequent.simps(1) image_is_empty option.simps(5) sup_eq_bot_iff)

lemma DE_to_SE_Sequent_freevars2:
  fixes s
  assumes "DE_to_SE_Sequent s = None"
  shows "freevars s \<noteq> {} \<or> (\<exists>s'. s = Sequent_Structure s')"
using DE_to_SE_Sequent_freevars by (metis DE_to_SE_Sequent.elims assms option.distinct(1))


(*lemma DE_to_SE_Sequent_freevars3:
  fixes X Y
  assumes "freevars ((Z\<^sub>S I\<^sub>S) \<turnstile>\<^sub>S (B\<^sub>S X \<rightarrow>\<^sub>S Y)) = {}"
  shows "\<exists>(X'::Structure) Y'::Structure. DE_to_SE_Sequent (Z\<^sub>S I\<^sub>S \<turnstile>\<^sub>S B\<^sub>S X \<rightarrow>\<^sub>S Y) = Some (I\<^sub>S \<turnstile>\<^sub>S X' \<rightarrow>\<^sub>S Y')"
proof -
  obtain ss :: "DEAK_Core.Structure \<Rightarrow> DEAK_Core_SE.Structure" where
    f1: "DE_to_SE_Structure (B\<^sub>S X \<rightarrow>\<^sub>S Y) = Some (ss (B\<^sub>S X \<rightarrow>\<^sub>S Y))"
    by (metis (no_types) DE_to_SE_Structure_freevars assms bot_eq_sup_iff freevars_Sequent.simps(1) image_is_empty)
  hence f2: "(case DE_to_SE_Structure Y of None \<Rightarrow> None | Some s \<Rightarrow> case DE_to_SE_Structure X of None \<Rightarrow> None | Some sa \<Rightarrow> Some (sa \<rightarrow>\<^sub>S s)) \<noteq> None"
    by force
  have f3: "DE_to_SE_Sequent (Z\<^sub>S I\<^sub>S \<turnstile>\<^sub>S B\<^sub>S X \<rightarrow>\<^sub>S Y) = Some (I\<^sub>S \<turnstile>\<^sub>S ss (B\<^sub>S X \<rightarrow>\<^sub>S Y))"
    using f1 by simp
  have f4: "\<forall>z f za. if za = None then (case za of None \<Rightarrow> z\<Colon>DEAK_Core_SE.Structure option | Some (x\<Colon>DEAK_Core_SE.Structure) \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
    by fastforce
  hence f5: "(case DE_to_SE_Structure Y of None \<Rightarrow> None | Some s \<Rightarrow> case DE_to_SE_Structure X of None \<Rightarrow> None | Some sa \<Rightarrow> Some (sa \<rightarrow>\<^sub>S s)) = (case DE_to_SE_Structure X of None \<Rightarrow> None | Some s \<Rightarrow> Some (s \<rightarrow>\<^sub>S the (DE_to_SE_Structure Y)))"
    using f2 by meson
  hence "(case DE_to_SE_Structure X of None \<Rightarrow> None | Some s \<Rightarrow> Some (s \<rightarrow>\<^sub>S the (DE_to_SE_Structure Y))) \<noteq> None"
    using f2 by presburger
  thus ?thesis
    using f5 f4 f3 f1 by (metis DE_to_SE_Structure.simps(9) option.sel)
qed*)

fun SE_to_DE_Locale :: "Locale \<Rightarrow> DEAK.Locale" where
"SE_to_DE_Locale (CutFormula f) = DEAK.CutFormula (SE_to_DE_Formula f)" |
"SE_to_DE_Locale (Premise s) = DEAK.Premise (SE_to_DE_Sequent s)" |
"SE_to_DE_Locale (Part s) = DEAK.Part (SE_to_DE_Structure s)" |
"SE_to_DE_Locale (RelAKA a) = DEAK.RelAKA (\<lambda>ac. \<lambda>ag. (map (SE_to_DE_Action) (a (the (DE_to_SE_Action ac)) (the (DE_to_SE_Agent ag)))))" |
"SE_to_DE_Locale (PreFormula a f) = DEAK.PreFormula (SE_to_DE_Action a) (SE_to_DE_Formula f)" |
"SE_to_DE_Locale Empty = DEAK.Empty"


lemma what_the1[simp]: "foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False = (\<exists>x\<in>set loc. set (prod.snd (der x r s)) = set (map concl l) \<and> Fail \<noteq> prod.fst (der x r s))"
by(induct loc, simp_all)

lemma isProofTreeWoMacro_concl_freevars_aux[simp]:
  fixes loc s r l n pt
  assumes "isProofTreeWoMacro loc (s \<Longleftarrow> PT(r) l)" "r \<noteq> RuleMacro n pt"
  shows "foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False"
using assms by (cases r, auto)

lemma isProofTreeWoMacro_concl_freevars[simp]:
  fixes loc s r l
  assumes "isProofTreeWoMacro loc (s \<Longleftarrow> PT(r) l)"
  shows "\<exists>x\<in>set loc. set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)"
proof (rule ccontr)
assume assm:  "\<not> (\<exists>x\<in>set loc. set (prod.snd (der x r s)) = set (map concl l) \<and> Fail \<noteq> prod.fst (der x r s))"
  with assms show False
  apply(cases r)
  using assm isProofTreeWoMacro_concl_freevars_aux what_the1 by blast+
qed

lemma der_imp_ruleMatch:
  fixes l r s
  assumes "der l r s \<noteq> (Fail, [])"
  shows "ruleMatch (fst (rule l r)) s"
proof -
  have f1: "(case DEAK.snd (rule l r) s of None \<Rightarrow> (Fail, []) | Some ss \<Rightarrow> if ruleMatch (DEAK.fst (rule l r)) s then case cond (rule l r) of None \<Rightarrow> (r, map (replaceAll (match (DEAK.fst (rule l r)) s)) ss) | Some p \<Rightarrow> if p s then (r, map (replaceAll (match (DEAK.fst (rule l r)) s)) ss) else (Fail, []) else (Fail, [])) \<noteq> (Fail, [])"
    using assms by auto
  have f2: "\<forall>p f z. if z = None then (case z of None \<Rightarrow> p\<Colon>Rule \<times> DEAK_Core.Sequent list | Some (x\<Colon>DEAK_Core.Sequent list) \<Rightarrow> f x) = p else (case z of None \<Rightarrow> p | Some x \<Rightarrow> f x) = f (the z)"
    by fastforce
  hence "DEAK.snd (rule l r) s \<noteq> None"
    using f1 by meson
  hence "der l r s = (if ruleMatch (DEAK.fst (rule l r)) s then case cond (rule l r) of None \<Rightarrow> (r, map (replaceAll (match (DEAK.fst (rule l r)) s)) (the (DEAK.snd (rule l r) s))) | Some p \<Rightarrow> if p s then (r, map (replaceAll (match (DEAK.fst (rule l r)) s)) (the (DEAK.snd (rule l r) s))) else (Fail, []) else (Fail, []))"
    using f2 by auto
  thus ?thesis
    using assms by presburger
qed

lemma isProofTree_concl_freevars[simp]:
  fixes pt loc
  assumes "isProofTreeWoMacro loc pt"
  shows "freevars (concl pt) = {}"
apply(cases pt)
apply(case_tac x2)
apply simp_all
using assms der_imp_ruleMatch isProofTreeWoMacro_concl_freevars ruleMatch_def
apply (metis (no_types) Pair_inject prod.exhaust_sel)+
done

lemma replace_Structure_aux_freevars_unchanged:
  fixes X Y free
  assumes "freevars X = {}"
  shows "replace_Structure_aux (?\<^sub>S free) Y X = X" (*"replace_Structure ((?\<^sub>S free), Y) X = X"*)
using assms apply(induct X, auto)
proof -
case goal1 
  thus ?case by (induct x, auto)
qed

lemma SE_to_DE_Empty_redundant :
  fixes t
  shows "[Empty] \<turnstile>d t \<Longrightarrow> [] \<turnstile>d t"
apply (induction "[Empty]" t rule:derivable.induct)
by (auto intro: derivable.intros)


lemma SE_to_DE_subset_loc :
  fixes t l l'
  assumes "l \<turnstile>d t" "set l \<subseteq> set l'"
  shows "l' \<turnstile>d t"
using assms apply (induction l t rule:derivable.induct)
apply (auto intro: derivable.intros)
apply (meson Swapout_L subsetCE)
by (meson Swapout_R subsetCE)


lemma DS_SD_Sequent_Id :
  fixes seq seq'
  assumes "freevars seq = {}" "DE_to_SE_Sequent seq = Some (seq')"
  shows "seq = SE_to_DE_Sequent seq'"
using assms apply(induct seq, simp_all)
using DS_SD_Structure_Id2 by (metis (mono_tags, lifting) SE_to_DE_Sequent.simps option.case_eq_if option.distinct(1) option.sel)




method metis_stuff uses add = 
  (metis DE_to_SE_Formula.simps DE_to_SE_Formula_freevars DS_SD_Sequent_Id SE_to_DE_Sequent.simps SE_to_DE_Action.simps option.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps add isProofTree_concl_freevars),
  (metis SE_to_DE_Structure_freevars empty_iff)+





lemma replace_Atprop_no_freevars:
  fixes X::DEAK_Core.Atprop
  assumes "freevars X = {}"
  shows "replace a X = X"
using assms apply (induction X arbitrary:a)
apply auto
by (metis Atprop.simps(5) DE_to_SE_Atprop.elims replace_Atprop_aux.simps(1) replace_Atprop_aux.simps(2))

lemma replace_Action_no_freevars:
  fixes X::DEAK_Core.Action
  assumes "freevars X = {}"
  shows "replace a X = X"
using assms apply(induct X arbitrary:a)
by auto

lemma replace_Agent_no_freevars:
  fixes X::DEAK_Core.Agent
  assumes "freevars X = {}"
  shows "replace a X = X"
using assms apply(induct X arbitrary:a)
by auto

lemma replace_Formula_no_freevars0:
  fixes X::DEAK_Core.Formula
  assumes "freevars X = {}"
  shows "replace_Formula_aux a b X = X"
using assms apply(induct X)
apply (auto)
apply (case_tac x1a)
apply (auto)
apply((induct a;induct b, auto),(simp add: replace_Action_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Action_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Action_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Action_no_freevars))
apply (case_tac x1a)
apply (auto)
apply((induct a;induct b, auto),(simp add: replace_Agent_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Agent_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Agent_no_freevars))
apply((induct a;induct b, auto),(simp add: replace_Agent_no_freevars))
apply(induct a;induct b, auto)
using replace_Atprop_no_freevars apply auto[1]
apply(induct a;induct b, auto)
by (simp add: replace_Action_no_freevars)




lemma replace_Formula_no_freevars:
  fixes X::DEAK_Core.Formula
  assumes "freevars X = {}"
  shows "replace a X = X"
using assms apply(induct X arbitrary:a)
apply (auto)
apply (case_tac x1a)
apply (auto)
apply((case_tac a;case_tac b, auto),(simp add: replace_Action_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Action_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Action_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Action_no_freevars))
apply (case_tac x1a)
apply (auto)
apply((case_tac a;case_tac b, auto),(simp add: replace_Agent_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Agent_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Agent_no_freevars))
apply((case_tac a;case_tac b, auto),(simp add: replace_Agent_no_freevars))
apply(case_tac a;case_tac b, auto)
using replace_Atprop_no_freevars apply auto[1]
apply(case_tac a;case_tac b, auto)
by (simp add: replace_Action_no_freevars)


lemma replace_Structure_no_freevars0:
  fixes X::DEAK_Core.Structure
  assumes "freevars X = {}"
  shows "replace_Structure_aux a b X = X"
using assms apply(induct X arbitrary:a b)
apply simp_all
apply (case_tac x1)
apply simp_all
apply(case_tac a, simp_all)
apply(case_tac x5, simp_all)
apply(case_tac b, simp_all)
apply(case_tac x5a, simp_all)
apply (simp add: replace_Action_no_freevars)+
apply(case_tac a, simp_all)
apply(case_tac x5, simp_all)
apply(case_tac b, simp_all)
apply(case_tac x5a, simp_all)
apply (simp add: replace_Action_no_freevars)+
apply(case_tac a, simp_all)
apply(case_tac x5, simp_all)
apply(case_tac b, simp_all)
apply(case_tac x5a, simp_all)
apply (simp add: replace_Agent_no_freevars)+
defer
apply(induct_tac a, simp_all)
apply(induct_tac b, simp_all)
using replace_Formula_no_freevars apply auto
apply(case_tac a, simp_all)
apply(case_tac x5, simp_all)
apply(case_tac b, simp_all)
apply(case_tac x5a, simp_all)
apply (simp add: replace_Action_no_freevars)+
proof -
case goal1 thus ?case by(induct x, auto)
qed

method se_to_de_tac for tree::'a uses add = 
  (rule exI [where x=tree]), 
  (auto simp add: add ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged),
  (insert SD_DS_Structure_Id replace_Structure_no_freevars0 SE_to_DE_Structure_freevars)?,
  auto?


lemma replace_match_X_t_Y:
  fixes X Y
  assumes "freevars (X \<turnstile>\<^sub>S Y) = {}"
  shows "replaceAll (match (?\<^sub>S ''X'' \<turnstile>\<^sub>S ?\<^sub>S ''Y'') (X \<turnstile>\<^sub>S Y)) (?\<^sub>S ''X'' \<turnstile>\<^sub>S ?\<^sub>S ''Y'') = (X \<turnstile>\<^sub>S Y)"
using assms 
apply(induction Y)
by (auto simp add: m_clash_def replace_Structure_aux_freevars_unchanged)

lemma atom_SE_to_DE_equiv:
  fixes seq
  assumes "atom seq"
  shows "DEAK.atom (SE_to_DE_Sequent seq)"
using assms apply(induct seq rule: atom.induct)
proof -
case goal1 
  thus ?case 
  apply(induction l)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
defer
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  using DEAK.atom.simps(1) apply(cases "DEAK_SE.atom (l \<turnstile>\<^sub>S r)", fastforce, force)
  proof (rule ccontr)
  case goal1 
    from goal1(2) have "\<not>atom (x \<^sub>S \<turnstile>\<^sub>S r)"
    proof (cases x, auto)
    case goal1 thus ?case
      proof(induct r, auto)
      case goal1 thus ?case by(induct x, auto)
      qed
    qed
    thus ?case using goal1(1) by blast
  qed
qed



lemma replace_Bigcomma_list_no_freevars: 
  fixes list x y
  assumes "freevars (;;\<^sub>S list) = {}"
  shows "replace_Structure_list_aux x y list = list"
using assms DEAK_Eq.replace_Structure_no_freevars0 by(induct list, auto)

    
  
lemma SE_to_DE:
  fixes t
  assumes "[Empty] \<turnstile>d t"
  shows "\<exists>pt. DE_to_SE_Sequent (concl pt) = Some t \<and> isProofTreeWoMacro [DEAK.Empty] pt"
using assms
proof (induction "[Empty]" t)
(*case (Id p) thus ?case
   by (base_case "(Atprop p \<^sub>F \<^sub>S \<turnstile>\<^sub>S Atprop p \<^sub>F \<^sub>S) \<Longleftarrow> PT (RuleZer Id) []" add: assms)
next

case (I_impR X Y)
  then obtain pt X' Y' where assms: "DE_to_SE_Sequent (concl pt) = Some (X \<turnstile>\<^sub>S Y)" "isProofTreeWoMacro [DEAK.Locale.Empty] pt" "(concl pt) = X' \<turnstile>\<^sub>S Y'" using DS_SD_Sequent_Id by force
  show ?case
  by (base_case "((Z\<^sub>S I\<^sub>S) \<turnstile>\<^sub>S (B\<^sub>S X' \<rightarrow>\<^sub>S Y')) \<Longleftarrow>PT (RuleStruct I_impR) [pt]" add: assms)
next

case (I_impR2 X Y)
  then obtain pt where assms: "DE_to_SE_Sequent (concl pt) = Some (I\<^sub>S \<turnstile>\<^sub>S X \<rightarrow>\<^sub>S Y) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] pt" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (X \<turnstile>\<^sub>S Y)) \<Longleftarrow>PT (RuleStruct I_impR2) [pt]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
  using SD_DS_Structure_Id apply auto
  using DS_SD_Sequent_Id assms isProofTree_concl_freevars by (fastforce, fastforce, fastforce)

next

case (Bigcomma_Nil_R2 X)
  then obtain pt X' where assms: "DE_to_SE_Sequent (concl pt) = Some (X \<turnstile>\<^sub>S I\<^sub>S)" "isProofTreeWoMacro [DEAK.Locale.Empty] pt" "(concl pt) = X' \<turnstile>\<^sub>S (Z\<^sub>S I\<^sub>S)" using DS_SD_Sequent_Id by force
  show ?case
  by (base_case "(X' \<turnstile>\<^sub>S (;;\<^sub>S [])) \<Longleftarrow>PT (RuleBigcomma Bigcomma_Nil_R2) [pt]" add: assms)

next


case SingleCut thus ?case by simp
next
*)

case (Bigcomma_Nil_R2 Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Y \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S (;;\<^sub>S [])))) \<Longleftarrow>PT (RuleBigcomma Bigcomma_Nil_R2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Bigcomma_Nil_R Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Y \<turnstile>\<^sub>S (;;\<^sub>S []))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S I\<^sub>S))) \<Longleftarrow>PT (RuleBigcomma Bigcomma_Nil_R) [aa]" add: assms)
  proof -
  case goal1 
    then have "concl aa = SE_to_DE_Sequent (Y \<turnstile>\<^sub>S ;;\<^sub>S [])"
      using DS_SD_Sequent_Id assms isProofTree_concl_freevars by blast
    thus ?case by force
  qed
next
case (Bigcomma_Nil_L2 Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((;;\<^sub>S []) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleBigcomma Bigcomma_Nil_L2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Bigcomma_Nil_L Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((;;\<^sub>S []) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((I\<^sub>S \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleBigcomma Bigcomma_Nil_L) [aa]" add: assms)
  proof -
  case goal1
    then have "concl aa = ;;\<^sub>S [] \<turnstile>\<^sub>S SE_to_DE_Structure Y"
      using DS_SD_Sequent_Id assms isProofTree_concl_freevars
      by (metis SE_to_DE_Sequent.simps SE_to_DE_Structure.simps(5) list.simps(8))
    thus ?case by force
  qed
next



case (Comma_impL_disp X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S Y)))) \<Longleftarrow>PT (RuleDisp Comma_impL_disp) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Comma_impR_disp2 Y X Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleDisp Comma_impR_disp2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_comma_disp2 Z Y X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((Z \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (X ;\<^sub>S Y)))) \<Longleftarrow>PT (RuleDisp ImpL_comma_disp2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_comma_disp2 X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (X ;\<^sub>S Y)))) \<Longleftarrow>PT (RuleDisp ImpR_comma_disp2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_comma_disp Z X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S (X ;\<^sub>S Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleDisp ImpR_comma_disp) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_comma_disp Z X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S (X ;\<^sub>S Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((Z \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleDisp ImpL_comma_disp) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Comma_impR_disp X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z)))) \<Longleftarrow>PT (RuleDisp Comma_impR_disp) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Comma_impL_disp2 X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleDisp Comma_impL_disp2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Back_forw_A X a Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (forwA\<^sub>S a Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backA\<^sub>S a X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleDispAct Back_forw_A) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Forw_back_A2 X a Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (backA\<^sub>S a Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleDispAct Forw_back_A2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Forw_back_A a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backA\<^sub>S a Y)))) \<Longleftarrow>PT (RuleDispAct Forw_back_A) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Back_forw_A2 a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((backA\<^sub>S a X) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwA\<^sub>S a Y)))) \<Longleftarrow>PT (RuleDispAct Back_forw_A2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Back_forw_K2 a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((backK\<^sub>S a X) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwK\<^sub>S a Y)))) \<Longleftarrow>PT (RuleDispK Back_forw_K2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Back_forw_K X a Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (forwK\<^sub>S a Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backK\<^sub>S a X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleDispK Back_forw_K) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Forw_back_K2 X a Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (backK\<^sub>S a Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwK\<^sub>S a X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleDispK Forw_back_K2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Forw_back_K a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((forwK\<^sub>S a X) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backK\<^sub>S a Y)))) \<Longleftarrow>PT (RuleDispK Forw_back_K) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Grishin_R2 W X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((W \<turnstile>\<^sub>S ((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((W \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z))))) \<Longleftarrow>PT (RuleGrish Grishin_R2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Grishin_R W X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((W \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((W \<turnstile>\<^sub>S ((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z)))) \<Longleftarrow>PT (RuleGrish Grishin_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Grishin_L X Y Z W)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W))) \<Longleftarrow>PT (RuleGrish Grishin_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Grishin_L2 X Y Z W)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W))) \<Longleftarrow>PT (RuleGrish Grishin_L2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Bot_R X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (\<bottom>\<^sub>F \<^sub>S)))) \<Longleftarrow>PT (RuleOp Bot_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Top_L X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((\<top>\<^sub>F \<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleOp Top_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (DImpR_L A B Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((A \<^sub>S) \<rightarrow>\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((A >-\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleOp DImpR_L) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis DE_to_SE_Formula.simps(13) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(13) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_R Z B A)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((B \<^sub>S) \<leftarrow>\<^sub>S (A \<^sub>S)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S ((B \<leftarrow>\<^sub>F A) \<^sub>S)))) \<Longleftarrow>PT (RuleOp ImpL_R) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(11) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(11) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (DImpL_R Y B A X)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some (((A \<^sub>S) \<turnstile>\<^sub>S X)) \<and> (isProofTreeWoMacro [DEAK.Locale.Empty] aa)" "DE_to_SE_Sequent (concl bb) = Some ((Y \<turnstile>\<^sub>S (B \<^sub>S))) \<and> (isProofTreeWoMacro [DEAK.Locale.Empty] bb)" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (((Y \<leftarrow>\<^sub>S X) \<turnstile>\<^sub>S ((B -<\<^sub>F A) \<^sub>S)))) \<Longleftarrow>PT (RuleOp DImpL_R) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(12) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Formula.simps(12) SE_to_DE_Structure.simps(7) SE_to_DE_Structure.simps(9) option.simps(5))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (And_L A B Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((A \<^sub>S) ;\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((A \<and>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleOp And_L) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
  using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
  apply (metis DE_to_SE_Formula.simps(10) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(10) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_R Z A B)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((A \<^sub>S) \<rightarrow>\<^sub>S (B \<^sub>S)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S ((A \<rightarrow>\<^sub>F B) \<^sub>S)))) \<Longleftarrow>PT (RuleOp ImpR_R) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(15) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(15) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Or_L B Y A X)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some (((A \<^sub>S) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" "DE_to_SE_Sequent (concl bb) = Some (((B \<^sub>S) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] bb" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((A \<or>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S (X ;\<^sub>S Y)))) \<Longleftarrow>PT (RuleOp Or_L) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis DE_to_SE_Formula.simps(14) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(14) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Or_R Z A B)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((A \<^sub>S) ;\<^sub>S (B \<^sub>S)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S ((A \<or>\<^sub>F B) \<^sub>S)))) \<Longleftarrow>PT (RuleOp Or_R) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(14) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Formula.simps(14) SE_to_DE_Structure.simps(9) option.simps(5))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_L B Y X A)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (A \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" "DE_to_SE_Sequent (concl bb) = Some (((B \<^sub>S) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] bb" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((A \<rightarrow>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y)))) \<Longleftarrow>PT (RuleOp ImpR_L) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(15) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(15) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (DImpL_L B A Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((B \<^sub>S) \<leftarrow>\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((B -<\<^sub>F A) \<^sub>S) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleOp DImpL_L) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
  apply (metis DE_to_SE_Formula.simps(12) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Formula.simps(12) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (And_R Y B X A)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (A \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" "DE_to_SE_Sequent (concl bb) = Some ((Y \<turnstile>\<^sub>S (B \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] bb" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (((X ;\<^sub>S Y) \<turnstile>\<^sub>S ((A \<and>\<^sub>F B) \<^sub>S)))) \<Longleftarrow>PT (RuleOp And_R) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (no_types, lifting) DE_to_SE_Formula.simps(10) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Formula.simps(10) SE_to_DE_Structure.simps(6) SE_to_DE_Structure.simps(9) option.simps(5))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (DImpR_R Y B A X)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some (((A \<^sub>S) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" "DE_to_SE_Sequent (concl bb) = Some ((Y \<turnstile>\<^sub>S (B \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] bb" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (((X \<rightarrow>\<^sub>S Y) \<turnstile>\<^sub>S ((A >-\<^sub>F B) \<^sub>S)))) \<Longleftarrow>PT (RuleOp DImpR_R) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis (mono_tags, lifting) DE_to_SE_Formula.simps(13) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Formula.simps(13) SE_to_DE_Structure.simps(8) SE_to_DE_Structure.simps(9) option.simps(5))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_L B Y X A)
  then obtain aa bb where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (A \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" "DE_to_SE_Sequent (concl bb) = Some (((B \<^sub>S) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] bb" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((B \<leftarrow>\<^sub>F A) \<^sub>S) \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X)))) \<Longleftarrow>PT (RuleOp ImpL_L) [aa, bb]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis DE_to_SE_Formula.simps(11) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Formula.simps(11) SE_to_DE_Structure.simps(9) option.simps(5))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Top_R )
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (I\<^sub>S \<turnstile>\<^sub>S (\<top>\<^sub>F \<^sub>S))) \<Longleftarrow>PT (RuleOp Top_R) []"])
  by (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
next

case (Bot_L )
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent (((\<bottom>\<^sub>F \<^sub>S) \<turnstile>\<^sub>S I\<^sub>S))) \<Longleftarrow>PT (RuleOp Bot_L) []"])
  by (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
next

case (FdiamA_L a A X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((forwA\<^sub>S a (A \<^sub>S)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (rule exI [where x="(SE_to_DE_Sequent ((((fdiamA\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleOpAct FdiamA_L) [aa]"])
  apply (auto simp add: assms ruleMatch_def m_clash_def replace_Structure_aux_freevars_unchanged)
	using SD_DS_Structure_Id replace_Formula_no_freevars0 replace_Structure_no_freevars0 SE_to_DE_Structure_freevars SE_to_DE_Formula_freevars apply auto
	apply (metis DE_to_SE_Formula.simps(2) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Action.simps SE_to_DE_Formula.simps(2) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
	using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (One_R a)
  show ?case
  by (se_to_de_tac "(SE_to_DE_Sequent (((Phi\<^sub>S a) \<turnstile>\<^sub>S ((One\<^sub>F a) \<^sub>S)))) \<Longleftarrow>PT (RuleOpAct One_R) []" add: assms)
next
case (FboxA_R X a A)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (forwA\<^sub>S a (A \<^sub>S)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S ((fboxA\<^sub>F a A) \<^sub>S)))) \<Longleftarrow>PT (RuleOpAct FboxA_R) [aa]" add: assms)
  apply (metis (no_types, lifting) DE_to_SE_Formula.simps(1) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Action.simps SE_to_DE_Formula.simps(1) SE_to_DE_Structure.simps(9) option.simps(5))
  using SE_to_DE_Formula_freevars apply auto
  by (metis DS_SD_Sequent_Id SE_to_DE_Action.elims SE_to_DE_Sequent.simps SE_to_DE_Structure.simps(1) SE_to_DE_Structure.simps(9) assms isProofTree_concl_freevars)
  next

case (FboxA_L A X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((A \<^sub>S) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((fboxA\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S (forwA\<^sub>S a X)))) \<Longleftarrow>PT (RuleOpAct FboxA_L) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis DE_to_SE_Formula.simps(1) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Action.elims SE_to_DE_Formula.simps(1) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (One_L a X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((Phi\<^sub>S a) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((One\<^sub>F a) \<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleOpAct One_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FdiamA_R X A a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (A \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a X) \<turnstile>\<^sub>S ((fdiamA\<^sub>F a A) \<^sub>S)))) \<Longleftarrow>PT (RuleOpAct FdiamA_R) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis (no_types, lifting) DE_to_SE_Formula.simps(2) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Action.simps SE_to_DE_Formula.simps(2) SE_to_DE_Structure.simps(1) SE_to_DE_Structure.simps(9) option.simps(5))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (FboxK_L A X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((A \<^sub>S) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((fboxK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S (forwK\<^sub>S a X)))) \<Longleftarrow>PT (RuleOpK FboxK_L) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis DE_to_SE_Formula.simps(5) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Agent.simps SE_to_DE_Formula.simps(5) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FdiamK_R X A a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (A \<^sub>S))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwK\<^sub>S a X) \<turnstile>\<^sub>S ((fdiamK\<^sub>F a A) \<^sub>S)))) \<Longleftarrow>PT (RuleOpK FdiamK_R) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis (no_types, lifting) DE_to_SE_Formula.simps(6) DE_to_SE_Formula_freevars DE_to_SE_Structure.simps(10) SE_to_DE_Agent.simps SE_to_DE_Formula.simps(6) SE_to_DE_Structure.simps(4) SE_to_DE_Structure.simps(9) option.simps(5))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FboxK_R X a A)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (forwK\<^sub>S a (A \<^sub>S)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S ((fboxK\<^sub>F a A) \<^sub>S)))) \<Longleftarrow>PT (RuleOpK FboxK_R) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis (no_types, lifting) DE_to_SE_Formula.simps(5) DE_to_SE_Structure.simps(10) SE_to_DE_Agent.simps SE_to_DE_Formula.simps(5) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1) option.simps(5))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FdiamK_L a A X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((forwK\<^sub>S a (A \<^sub>S)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((fdiamK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleOpK FdiamK_L) [aa]" add: assms)
  using SE_to_DE_Formula_freevars replace_Formula_no_freevars0 apply auto
  apply (metis DE_to_SE_Formula.simps(6) DE_to_SE_Structure.simps(10) SD_DS_Structure_Id2 SE_to_DE_Agent.simps SE_to_DE_Formula.simps(6) SE_to_DE_Structure.simps(9) option.case_eq_if option.distinct(1))
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (W_impL_R X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X \<leftarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct W_impL_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_I X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S I\<^sub>S))) \<Longleftarrow>PT (RuleStruct ImpL_I) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (W_impL_L X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S X)))) \<Longleftarrow>PT (RuleStruct W_impL_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_I2 Y X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct ImpR_I2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (E_R X Y1 Y2)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (Y1 ;\<^sub>S Y2))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (Y2 ;\<^sub>S Y1)))) \<Longleftarrow>PT (RuleStruct E_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (IW_R X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct IW_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (IW_L Y X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct IW_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_L2 X Y Z W)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X ;\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((X ;\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W))) \<Longleftarrow>PT (RuleStruct A_L2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (E_L X1 X2 Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X1 ;\<^sub>S X2) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X2 ;\<^sub>S X1) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct E_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_R W X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((W \<turnstile>\<^sub>S ((X ;\<^sub>S Y) ;\<^sub>S Z))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((W \<turnstile>\<^sub>S (X ;\<^sub>S (Y ;\<^sub>S Z))))) \<Longleftarrow>PT (RuleStruct A_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (W_impR_R X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z)))) \<Longleftarrow>PT (RuleStruct W_impR_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (C_L X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X ;\<^sub>S X) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct C_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (C_R X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S (Y ;\<^sub>S Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct C_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpR_I X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S I\<^sub>S))) \<Longleftarrow>PT (RuleStruct ImpR_I) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (W_impR_L X Z Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((Z \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct W_impR_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_L X Y Z W)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((X ;\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((X ;\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W))) \<Longleftarrow>PT (RuleStruct A_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_R2 W X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((W \<turnstile>\<^sub>S (X ;\<^sub>S (Y ;\<^sub>S Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((W \<turnstile>\<^sub>S ((X ;\<^sub>S Y) ;\<^sub>S Z)))) \<Longleftarrow>PT (RuleStruct A_R2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (I_impR2 X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct I_impR2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (I_impL X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((I\<^sub>S \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X)))) \<Longleftarrow>PT (RuleStruct I_impL) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (I_impR X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((I\<^sub>S \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y)))) \<Longleftarrow>PT (RuleStruct I_impR) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (ImpL_I2 X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct ImpL_I2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (I_impL2 Y X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStruct I_impL2) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (A_nec_L X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backA\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructAct A_nec_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_mon_L a X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((backA\<^sub>S a X) ;\<^sub>S (backA\<^sub>S a Y)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backA\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleStructAct A_mon_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Mon_A_R Z a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((forwA\<^sub>S a X) ;\<^sub>S (forwA\<^sub>S a Y)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (forwA\<^sub>S a (X ;\<^sub>S Y))))) \<Longleftarrow>PT (RuleStructAct Mon_A_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Nec_A_L X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructAct Nec_A_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FS_A_L a Y Z X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((forwA\<^sub>S a Y) \<rightarrow>\<^sub>S (forwA\<^sub>S a Z)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructAct FS_A_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FS_A_R X a Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S ((forwA\<^sub>S a Y) \<rightarrow>\<^sub>S (forwA\<^sub>S a Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwA\<^sub>S a (Y \<rightarrow>\<^sub>S Z))))) \<Longleftarrow>PT (RuleStructAct FS_A_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_mon_R Z a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((backA\<^sub>S a X) ;\<^sub>S (backA\<^sub>S a Y)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (backA\<^sub>S a (X ;\<^sub>S Y))))) \<Longleftarrow>PT (RuleStructAct A_mon_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_FS_R X a Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S ((backA\<^sub>S a Y) \<rightarrow>\<^sub>S (backA\<^sub>S a Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backA\<^sub>S a (Y \<rightarrow>\<^sub>S Z))))) \<Longleftarrow>PT (RuleStructAct A_FS_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Nec_A_R X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwA\<^sub>S a I\<^sub>S)))) \<Longleftarrow>PT (RuleStructAct Nec_A_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Mon_A_L a X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((forwA\<^sub>S a X) ;\<^sub>S (forwA\<^sub>S a Y)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleStructAct Mon_A_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_FS_L a Y Z X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((backA\<^sub>S a Y) \<rightarrow>\<^sub>S (backA\<^sub>S a Z)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructAct A_FS_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (A_nec_R X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backA\<^sub>S a I\<^sub>S)))) \<Longleftarrow>PT (RuleStructAct A_nec_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (Reduce_R Y a X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Y \<turnstile>\<^sub>S ((Phi\<^sub>S a) \<rightarrow>\<^sub>S (forwA\<^sub>S a X)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S (forwA\<^sub>S a X)))) \<Longleftarrow>PT (RuleStructEA Reduce_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (CompA_R Y a X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Y \<turnstile>\<^sub>S (forwA\<^sub>S a (backA\<^sub>S a X)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Y \<turnstile>\<^sub>S ((Phi\<^sub>S a) \<rightarrow>\<^sub>S X)))) \<Longleftarrow>PT (RuleStructEA CompA_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Balance X Y a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a X) \<turnstile>\<^sub>S (forwA\<^sub>S a Y)))) \<Longleftarrow>PT (RuleStructEA Balance) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (CompA_L a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some (((forwA\<^sub>S a (backA\<^sub>S a X)) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((((Phi\<^sub>S a) ;\<^sub>S X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStructEA CompA_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Reduce_L a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((Phi\<^sub>S a) ;\<^sub>S (forwA\<^sub>S a X)) \<turnstile>\<^sub>S Y)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y))) \<Longleftarrow>PT (RuleStructEA Reduce_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next

case (K_nec_R X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backK\<^sub>S a I\<^sub>S)))) \<Longleftarrow>PT (RuleStructK K_nec_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Nec_K_L X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwK\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructK Nec_K_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (K_mon_L a X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((backK\<^sub>S a X) ;\<^sub>S (backK\<^sub>S a Y)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backK\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleStructK K_mon_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Mon_K_L a X Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((forwK\<^sub>S a X) ;\<^sub>S (forwK\<^sub>S a Y)) \<turnstile>\<^sub>S Z)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwK\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z))) \<Longleftarrow>PT (RuleStructK Mon_K_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FS_K_L a Y Z X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((forwK\<^sub>S a Y) \<rightarrow>\<^sub>S (forwK\<^sub>S a Z)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((forwK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructK FS_K_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (FS_K_R X a Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S ((forwK\<^sub>S a Y) \<rightarrow>\<^sub>S (forwK\<^sub>S a Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwK\<^sub>S a (Y \<rightarrow>\<^sub>S Z))))) \<Longleftarrow>PT (RuleStructK FS_K_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Mon_K_R Z a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((forwK\<^sub>S a X) ;\<^sub>S (forwK\<^sub>S a Y)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (forwK\<^sub>S a (X ;\<^sub>S Y))))) \<Longleftarrow>PT (RuleStructK Mon_K_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (K_mon_R Z a X Y)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((Z \<turnstile>\<^sub>S ((backK\<^sub>S a X) ;\<^sub>S (backK\<^sub>S a Y)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((Z \<turnstile>\<^sub>S (backK\<^sub>S a (X ;\<^sub>S Y))))) \<Longleftarrow>PT (RuleStructK K_mon_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (K_FS_L a Y Z X)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((((backK\<^sub>S a Y) \<rightarrow>\<^sub>S (backK\<^sub>S a Z)) \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructK K_FS_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (Nec_K_R X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S I\<^sub>S)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (forwK\<^sub>S a I\<^sub>S)))) \<Longleftarrow>PT (RuleStructK Nec_K_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (K_FS_R X a Y Z)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((X \<turnstile>\<^sub>S ((backK\<^sub>S a Y) \<rightarrow>\<^sub>S (backK\<^sub>S a Z)))) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent ((X \<turnstile>\<^sub>S (backK\<^sub>S a (Y \<rightarrow>\<^sub>S Z))))) \<Longleftarrow>PT (RuleStructK K_FS_R) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next
case (K_nec_L X a)
  then obtain aa where assms: "DE_to_SE_Sequent (concl aa) = Some ((I\<^sub>S \<turnstile>\<^sub>S X)) \<and> isProofTreeWoMacro [DEAK.Locale.Empty] aa" by auto
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (((backK\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X))) \<Longleftarrow>PT (RuleStructK K_nec_L) [aa]" add: assms)
  using SE_to_DE_Action.simps SE_to_DE_Agent.simps SE_to_DE_Structure.simps SE_to_DE_Sequent.simps by (metis DS_SD_Sequent_Id assms isProofTree_concl_freevars)+
next


case (Id p)
  show ?case
  by (se_to_de_tac "(SE_to_DE_Sequent ((((p \<^sub>F) \<^sub>S) \<turnstile>\<^sub>S ((p \<^sub>F) \<^sub>S)))) \<Longleftarrow>PT (RuleZer Id) []" add: assms)
next
case (Atom seq)
  show ?case
  apply (se_to_de_tac "(SE_to_DE_Sequent (seq)) \<Longleftarrow>PT (RuleZer Atom) []" add: assms)
proof -
case goal1
  assume a1: "freevars (SE_to_DE_Sequent seq) = {}"
  obtain ss :: "DEAK_Core.Sequent \<Rightarrow> DEAK_Core_SE.Sequent \<Rightarrow> DEAK_Core_SE.Structure" and ssa :: "DEAK_Core.Sequent \<Rightarrow> DEAK_Core_SE.Sequent \<Rightarrow> DEAK_Core_SE.Structure" where
    "\<forall>x0 x1. (\<exists>v2 v3. x1 = v2 \<turnstile>\<^sub>S v3 \<and> x0 = SE_to_DE_Structure v2 \<turnstile>\<^sub>S SE_to_DE_Structure v3) = (x1 = ss x0 x1 \<turnstile>\<^sub>S ssa x0 x1 \<and> x0 = SE_to_DE_Structure (ss x0 x1) \<turnstile>\<^sub>S SE_to_DE_Structure (ssa x0 x1))"
    by moura
  hence f2: "\<forall>s sa. SE_to_DE_Sequent s \<noteq> sa \<or> s = ss sa s \<turnstile>\<^sub>S ssa sa s \<and> sa = SE_to_DE_Structure (ss sa s) \<turnstile>\<^sub>S SE_to_DE_Structure (ssa sa s)"
    by (meson SE_to_DE_Sequent.elims)
  hence f3: "seq = ss (SE_to_DE_Sequent seq) seq \<turnstile>\<^sub>S ssa (SE_to_DE_Sequent seq) seq \<and> SE_to_DE_Sequent seq = SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq) \<turnstile>\<^sub>S SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)"
    by presburger
  obtain ssb :: "DEAK_Core.Structure \<Rightarrow> DEAK_Core.Structure \<Rightarrow> DEAK_Core_SE.Structure" and ssc :: "DEAK_Core.Structure \<Rightarrow> DEAK_Core.Structure \<Rightarrow> DEAK_Core_SE.Structure" where
    f4: "\<forall>s sa. freevars (s \<turnstile>\<^sub>S sa) \<noteq> {} \<or> DE_to_SE_Sequent (s \<turnstile>\<^sub>S sa) = Some (ssb sa s \<turnstile>\<^sub>S ssc sa s)"
    using DE_to_SE_Sequent_freevars by moura
  hence "SE_to_DE_Sequent seq = SE_to_DE_Sequent (ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)))"
    using f3 a1 by (metis DS_SD_Sequent_Id)
  hence "ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) = ss (SE_to_DE_Sequent seq) (ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq))) \<turnstile>\<^sub>S ssa (SE_to_DE_Sequent seq) (ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq))) \<and> SE_to_DE_Sequent seq = SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) (ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)))) \<turnstile>\<^sub>S SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) (ssb (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq)) \<turnstile>\<^sub>S ssc (SE_to_DE_Structure (ssa (SE_to_DE_Sequent seq) seq)) (SE_to_DE_Structure (ss (SE_to_DE_Sequent seq) seq))))"
    using f2 by (metis (no_types))
  thus ?case
    using f4 f3 a1 by (metis DEAK_Core.Sequent.inject(1) SD_DS_Structure_Id2)
next
case goal2 with replace_match_X_t_Y show ?case by (metis DEAK.atom.elims(2))
next
case goal3 thus ?case by (metis (no_types) DEAK_Core_SE.Sequent.exhaust SE_to_DE_Sequent.simps equals0D freevars_Sequent.simps(1) image_is_empty sup_eq_bot_iff)
next
case goal4 with atom_SE_to_DE_equiv show ?case using Atom.hyps by auto
qed
next

(*SE_to_DE_Empty_lemma*)

end