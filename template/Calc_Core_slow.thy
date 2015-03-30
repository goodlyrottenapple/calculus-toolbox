theory (*calc_name_core*)
imports Main "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin


(*calc_structure*)

class Varmatch =
  (* match takes a string occurring in a pattern and a term and returns the string 
     with a matching subterm. Never returns a list longer than 1. *)  
  fixes "match" :: "'a \<Rightarrow> 'a \<Rightarrow> ('a * 'a) list"
  fixes "freevars" :: "'a \<Rightarrow> 'a set"
  (* first argument matches return-type of match *)
  fixes "replace" :: "('a * 'a) \<Rightarrow> 'a \<Rightarrow> 'a"


definition m_clash :: "'a \<times> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" (infix "\<inter>m" 400) where 
"x \<inter>m y \<equiv> \<exists>a \<in> set y. fst a = fst x \<and> snd a \<noteq> snd x"

lemma m_clash_simp[simp] : "set (map fst m1) \<inter> set (map fst m2) = {} \<longrightarrow> (\<forall>x \<in> set m1. \<not>(x \<inter>m m2))"
unfolding m_clash_def by auto

fun merge :: "('a * 'b) list \<Rightarrow> ('a * 'b) list  \<Rightarrow> ('a * 'b) list " (infix "@m" 400) where
"[] @m y = y" |
"(x#xs) @m y = ( if x \<inter>m y
                 then [a \<leftarrow> xs. fst a \<noteq> fst x] @m [a \<leftarrow> y . fst a \<noteq> fst x] 
                 else x#(xs @m y) )"

lemma merge_simp[simp] :
  fixes m1 m2
  assumes "(\<forall>a\<in>set m1. case a of (x, y) \<Rightarrow> x = y)"
  and "\<forall>a\<in>set m2. case a of (x, y) \<Rightarrow> x = y"
  shows "set (m1 @m m2) = set m1 \<union> set m2"
using assms(1)
proof (induct m1)
  case Nil
    show ?case by simp
next
  case (Cons x xs)
    have "\<forall>a\<in>set xs. case a of (a, b) \<Rightarrow> a = b"
      by (metis Cons.prems(1) contra_subsetD set_subset_Cons)
    with Cons(1) have 1: "set (xs @m m2) = set xs \<union> set m2" by simp
    { assume "\<not>(x \<inter>m m2)"
      then have "set ((x # xs) @m m2) = set (x#xs @m m2)" by simp
      with 1 have ?case by simp }
    { assume "(x \<inter>m m2)"
      then have "\<exists>a \<in> set m2. fst a = fst x \<and> snd a \<noteq> snd x" unfolding m_clash_def by simp
      then obtain a where 2: "a \<in> set m2" and 3: "fst a = fst x" and 4: "snd a \<noteq> snd x" by auto
      then have False by (metis (full_types) Cons.prems(1) assms(2) fst_conv insertI1 old.prod.exhaust set_simps(2) snd_eqD split_beta)
      then have ?case .. }
    thus ?case
      by (metis `\<not> x \<inter>m m2 \<Longrightarrow> set ((x # xs) @m m2) = set (x # xs) \<union> set m2`)
qed 


lemma merge_simp2[simp] :
  fixes m1 m2
  assumes "set (map fst m1) \<inter> set (map fst m2) = {}"
  shows "set (m1 @m m2) = set m1 \<union> set m2"
using assms
proof (induct m1)
case Nil
  show ?case by simp
next
case (Cons x xs)
  then have "set (map fst xs) \<inter> set (map fst m2) = {}" by simp
  with Cons(1) have 1: "set (xs @m m2) = set xs \<union> set m2" by simp
  with Cons(2) have "\<not>(x \<inter>m m2)" by (metis insertCI m_clash_simp set_simps(2))
  then have "set ((x # xs) @m m2) = set( x#(xs @m m2) )" by simp
  then have "set ((x # xs) @m m2) = set(xs @m m2) \<union> {x}" by simp
  with 1 have "set ((x # xs) @m m2) = set xs \<union> set m2 \<union> {x}" by simp
  thus ?case by simp
qed

fun(in Varmatch) replaceAll :: "('a * 'a) list \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "replaceAll Nil mtch = mtch"
| "replaceAll (x # xs) mtch = replaceAll xs (replace x mtch)"

lemma replaceAll_simp: "(replaceAll [(x, r)] m) \<equiv> (replace (x, r) m)" by auto


definition(in Varmatch) ruleMatch :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"ruleMatch r m = (if freevars m = {} then (replaceAll (match r m) r) = m else False)"

(*lemma(in Varmatch) ruleMatch_simp[simp]: "freevars m = {} \<longrightarrow> ruleMatch r m \<equiv> (replaceAll (match r m) r) = m"*)



class Varmatch_preserving = Varmatch +
  assumes inv: "a = (replaceAll (match a a) a)"

instantiation Atprop :: Varmatch
begin   
  fun match_Atprop :: "Atprop \<Rightarrow> Atprop \<Rightarrow> (Atprop * Atprop) list"
  where
    "match_Atprop (Atprop_Freevar free) mtch = [((Atprop_Freevar free), mtch)]" |
    "match_Atprop _ _ = []"

  fun freevars_Atprop :: "Atprop \<Rightarrow> Atprop set"
  where
    "freevars_Atprop (Atprop_Freevar var) = {(Atprop_Freevar var)}" |
    "freevars_Atprop _ = {}" 
  
  fun replace_Atprop :: "(Atprop * Atprop) \<Rightarrow> Atprop \<Rightarrow> Atprop"
  where
    "replace_Atprop ((Atprop_Freevar x), mtch) (Atprop_Freevar free) = (if x = free then mtch else (Atprop_Freevar free))" |
    "replace_Atprop _ pttrn = pttrn"

  
instance ..
end

instantiation Action :: Varmatch
begin   
  fun match_Action :: "Action \<Rightarrow> Action \<Rightarrow> (Action * Action) list"
  where
    "match_Action (Action_Freevar free) mtch = [((Action_Freevar free), mtch)]" |
    "match_Action _ _ = []"

  fun freevars_Action :: "Action \<Rightarrow> Action set"
  where
    "freevars_Action (Action_Freevar var) = {(Action_Freevar var)}" |
    "freevars_Action _ = {}" 
  
  fun replace_Action :: "(Action * Action) \<Rightarrow> Action \<Rightarrow> Action"
  where
    "replace_Action ((Action_Freevar x), mtch) (Action_Freevar free) = (if x = free then mtch else (Action_Freevar free))" |
    "replace_Action _ pttrn = pttrn"

  
instance ..
end

instantiation Agent :: Varmatch
begin   
  fun match_Agent :: "Agent \<Rightarrow> Agent \<Rightarrow> (Agent * Agent) list"
  where
    "match_Agent (Agent_Freevar free) mtch = [((Agent_Freevar free), mtch)]" |
    "match_Agent _ _ = []"

  fun freevars_Agent :: "Agent \<Rightarrow> Agent set"
  where
    "freevars_Agent (Agent_Freevar var) = {(Agent_Freevar var)}" |
    "freevars_Agent _ = {}" 
  
  fun replace_Agent :: "(Agent * Agent) \<Rightarrow> Agent \<Rightarrow> Agent"
  where
    "replace_Agent ((Agent_Freevar x), mtch) (Agent_Freevar free) = (if x = free then mtch else (Agent_Freevar free))" |
    "replace_Agent _ pttrn = pttrn"

  
instance ..
end


instantiation Formula :: Varmatch
begin   
  fun match_Formula :: "Formula \<Rightarrow> Formula \<Rightarrow> (Formula * Formula) list"
  where
    "match_Formula (Formula_Atprop rule) (Formula_Atprop atprop) = map (\<lambda>(x,y). (Formula_Atprop x, Formula_Atprop y)) (match rule atprop)"
  | "match_Formula (Formula_Bin var11 op1 var12) (Formula_Bin var21 op2 var22) = (if op1 = op2 then (match var11 var21) @m (match var12 var22) else [])"
  | "match_Formula (Formula_Freevar free) mtch = [((Formula_Freevar free), mtch)]"

  | "match_Formula (Formula_Action_Formula op1 act1 form1) (Formula_Action_Formula op2 act2 form2) = (if op1 = op2 then map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match act1 act2) @m (match form1 form2) else [])"
  | "match_Formula (Formula_Agent_Formula op1 ag1 form1) (Formula_Agent_Formula op2 ag2 form2) = (if op1 = op2 then map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match ag1 ag2) @m (match form1 form2) else [])"
  | "match_Formula (Formula_Precondition act1) (Formula_Precondition act2) = map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match act1 act2)"
  | "match_Formula _ _ = []"
  
  fun freevars_Formula :: "Formula \<Rightarrow> Formula set"
  where
    "freevars_Formula (Formula_Atprop var) = image (\<lambda>x. Formula_Atprop x) (freevars var)"
  | "freevars_Formula (Formula_Bin var1 _ var2) = (freevars var1) \<union> (freevars var2)"
  | "freevars_Formula (Formula_Freevar var) = {(Formula_Freevar var)}"

  | "freevars_Formula (Formula_Action_Formula _ act1 form1) = image (\<lambda>x. Formula_Action x) (freevars act1) \<union> (freevars form1)"
  | "freevars_Formula (Formula_Agent_Formula _ ag1 form1) = image (\<lambda>x. Formula_Agent x) (freevars ag1) \<union> (freevars form1)"
  | "freevars_Formula (Formula_Precondition act1) = image (\<lambda>x. Formula_Action x) (freevars act1)"
  | "freevars_Formula _ = {}"

  fun replace_Formula :: "(Formula * Formula) \<Rightarrow> Formula \<Rightarrow> Formula"
  where
    "replace_Formula ((Formula_Atprop x), (Formula_Atprop rep)) (Formula_Atprop atprop) = Formula_Atprop (replace (x, rep) atprop)"
  | "replace_Formula (x, rep) (Formula_Bin var1 op1 var2) = Formula_Bin (replace (x, rep) var1) op1 (replace (x, rep) var2)"
  | "replace_Formula (x, mtch) (Formula_Freevar free) = (if x = (Formula_Freevar free) then mtch else (Formula_Freevar free))"

  | "replace_Formula ((Formula_Action x), (Formula_Action rep)) (Formula_Action_Formula op1 act1 form1) = Formula_Action_Formula op1 (replace (x, rep) act1) (replace ((Formula_Action x), (Formula_Action rep)) form1)"
  | "replace_Formula ((Formula_Agent x), (Formula_Agent rep)) (Formula_Agent_Formula op1 ag1 form1) = Formula_Agent_Formula op1 (replace (x, rep) ag1) (replace ((Formula_Agent x), (Formula_Agent rep)) form1)"

  | "replace_Formula (x, rep) (Formula_Action_Formula op1 act1 form1) = Formula_Action_Formula op1 act1 (replace (x, rep) form1)"
  | "replace_Formula (x, rep) (Formula_Agent_Formula op1 ag1 form1) = Formula_Agent_Formula op1 ag1 (replace (x, rep) form1)"

  | "replace_Formula ((Formula_Action x), (Formula_Action rep)) (Formula_Precondition act1) = Formula_Precondition (replace (x, rep) act1)"

  | "replace_Formula (_, _) y = y" 
instance ..
end

instantiation Structure :: Varmatch
begin   
  fun match_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> (Structure * Structure) list"
  where
(*(*uncommentL?Structure_Formula*)  "match_Structure (Structure_Formula rule) (Structure_Formula form) = map (\<lambda>(x,y). (Structure_Formula x, Structure_Formula y)) (match rule form)" |(*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Bin*)  "match_Structure (Structure_Bin var11 op1 var12) (Structure_Bin var21 op2 var22) = (if op1 = op2 then (match var11 var21) @m (match var12 var22) else [])" |(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Freevar*)  "match_Structure (Structure_Freevar free) mtch = [((Structure_Freevar free), mtch)]" |(*uncommentR?Structure_Freevar*)*)
  
  "match_Structure (Structure_Action_Structure op1 act1 struct1) (Structure_Action_Structure op2 act2 struct2) = (if op1 = op2 then map (\<lambda>(x,y). (Structure_Formula (Formula_Action x), Structure_Formula (Formula_Action y))) (match act1 act2) @m (match struct1 struct2) else [])" |
  "match_Structure (Structure_Agent_Structure op1 ag1 struct1) (Structure_Agent_Structure op2 ag2 struct2) = (if op1 = op2 then map (\<lambda>(x,y). (Structure_Formula (Formula_Agent x), Structure_Formula (Formula_Agent y))) (match ag1 ag2) @m (match struct1 struct1) else [])" |
  "match_Structure (Structure_Phi act1) (Structure_Phi act2) = map (\<lambda>(x,y). (Structure_Formula (Formula_Action x), Structure_Formula (Formula_Action y))) (match act1 act2)" |

  "match_Structure _ _ = []"
  
  fun freevars_Structure :: "Structure \<Rightarrow> Structure set"
  where
(*(*uncommentL?Structure_Formula*)  "freevars_Structure (Structure_Formula var) = image (\<lambda>x. Structure_Formula x) (freevars var)" |(*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Bin*)  "freevars_Structure (Structure_Bin var1 _ var2) = (freevars var1) \<union> (freevars var2)" |(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Freevar*)  "freevars_Structure (Structure_Freevar var) = {(Structure_Freevar var)}" |(*uncommentR?Structure_Freevar*)*)
  "freevars_Structure (Structure_Action_Structure _ act1 struct) = image (\<lambda>x. Structure_Formula (Formula_Action x)) (freevars act1) \<union> (freevars struct)" |
  "freevars_Structure (Structure_Agent_Structure _ ag1 struct) = image (\<lambda>x. Structure_Formula (Formula_Agent x)) (freevars ag1) \<union> (freevars struct)" |
  "freevars_Structure (Structure_Phi act1) = image (\<lambda>x. Structure_Formula (Formula_Action x)) (freevars act1)" |

  "freevars_Structure _ = {}"

  fun replace_Structure :: "(Structure * Structure) \<Rightarrow> Structure \<Rightarrow> Structure"
  where
(*(*uncommentL?Structure_Formula*)  "replace_Structure ((Structure_Formula x), (Structure_Formula rep)) (Structure_Formula form) = Structure_Formula (replace (x, rep) form)" |(*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Bin*)  "replace_Structure (x, rep) (Structure_Bin var1 op1 var2) = Structure_Bin (replace (x, rep) var1) op1 (replace (x, rep) var2)" |(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Freevar*)  "replace_Structure (x, mtch) (Structure_Freevar free) = (if x = (Structure_Freevar free) then mtch else (Structure_Freevar free))" |(*uncommentR?Structure_Freevar*)*)

  "replace_Structure ((Structure_Formula (Formula_Action x)), (Structure_Formula (Formula_Action rep))) (Structure_Action_Structure op1 act1 struct) = Structure_Action_Structure op1 (replace (x, rep) act1) (replace ((Structure_Formula (Formula_Action x)), (Structure_Formula (Formula_Action rep))) struct)" |
  "replace_Structure ((Structure_Formula (Formula_Agent x)), (Structure_Formula (Formula_Agent rep))) (Structure_Agent_Structure op1 ag1 struct) = Structure_Agent_Structure op1 (replace (x, rep) ag1) (replace ((Structure_Formula (Formula_Agent x)), (Structure_Formula (Formula_Agent rep))) struct)" |

  "replace_Structure (x, rep) (Structure_Action_Structure op1 act1 struct) = Structure_Action_Structure op1 act1 (replace (x, rep) struct)" |
  "replace_Structure (x, rep) (Structure_Agent_Structure op1 ag1 struct) = Structure_Agent_Structure op1 ag1 (replace (x, rep) struct)" |

  "replace_Structure ((Structure_Formula (Formula_Action x)), (Structure_Formula (Formula_Action rep))) (Structure_Phi act1) = Structure_Phi (replace (x, rep) act1)" |
  "replace_Structure (_, _) y = y"

instance ..
end

lemma inv_Atprop[simp]:
  fixes a::Atprop
  assumes "free \<in> set (match a a)"
  shows "a = replace free a"
by (cases a, metis replace_Atprop.simps(3))
(metis assms in_set_insert insert_Nil match_Atprop.simps(1) not_Cons_self2 replace_Atprop.simps(1) set_ConsD)


lemma inv_Atprop_2[simp]:
  fixes a::Atprop
  shows "a = replaceAll (match a a) a"
by (cases a, metis match_Atprop.simps(2) replaceAll.simps(1), simp)


lemma freevars_replace_Atprop_simp[simp]: "free \<notin> freevars (a::Atprop) \<longrightarrow> replace (free,free) a = a" 
by (induct a) (cases free, auto, metis Atprop.exhaust replace_Atprop.simps(1) replace_Atprop.simps(2))


lemma freevars_replace_Atprop_simp2 : "free \<in> freevars (a::Atprop) \<longrightarrow> replace (free,free) a = a"
by (induct a) (cases free, auto)

lemma match_Atprop_simp : "\<forall>(x, y) \<in> set (match (a::Atprop) a). x = y"
by (cases a) auto



lemma inv_Action[simp]:
  fixes a::Action
  assumes "free \<in> set (match a a)"
  shows "a = replace free a"
by (cases a, metis replace_Action.simps(3))
(metis assms in_set_insert insert_Nil match_Action.simps(1) not_Cons_self2 replace_Action.simps(1) set_ConsD)


lemma inv_Action_2[simp]:
  fixes a::Action
  shows "a = replaceAll (match a a) a"
by (cases a, metis match_Action.simps(2) replaceAll.simps(1), simp)


lemma freevars_replace_Action_simp[simp]: "free \<notin> freevars (a::Action) \<longrightarrow> replace (free,free) a = a" 
by (induct a) (cases free, auto, metis Action.exhaust replace_Action.simps(1) replace_Action.simps(2))

lemma freevars_replace_Action_simp2 : "free \<in> freevars (a::Action) \<longrightarrow> replace (free,free) a = a"
by (induct a) (cases free, auto)

lemma match_Action_simp : "\<forall>(x, y) \<in> set (match (a::Action) a). x = y"
by (cases a) auto





lemma inv_Agent[simp]:
  fixes a::Agent
  assumes "free \<in> set (match a a)"
  shows "a = replace free a"
by (cases a, metis replace_Agent.simps(3))
(metis assms in_set_insert insert_Nil match_Agent.simps(1) not_Cons_self2 replace_Agent.simps(1) set_ConsD)


lemma inv_Agent_2[simp]:
  fixes a::Agent
  shows "a = replaceAll (match a a) a"
by (cases a, metis match_Agent.simps(2) replaceAll.simps(1), simp)


lemma freevars_replace_Agent_simp[simp]: "free \<notin> freevars (a::Agent) \<longrightarrow> replace (free,free) a = a" 
by (induct a) (cases free, auto, metis Agent.exhaust replace_Agent.simps(1) replace_Agent.simps(2))

lemma freevars_replace_Agent_simp2 : "free \<in> freevars (a::Agent) \<longrightarrow> replace (free,free) a = a"
by (induct a) (cases free, auto)

lemma match_Agent_simp : "\<forall>(x, y) \<in> set (match (a::Agent) a). x = y"
by (cases a) auto





lemma freevars_replace_Formula_simp[simp]: "free \<notin> freevars (a::Formula) \<longrightarrow> replace (free,free) a = a" 
apply (induct a)
apply (cases a)
apply (simp_all)
apply (cases free)
apply auto
apply (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
apply (cases free)
apply auto
apply (metis freevars_replace_Agent_simp freevars_replace_Agent_simp2)
apply (cases free)
apply auto
apply (metis freevars_replace_Atprop_simp freevars_replace_Atprop_simp2)
apply (cases free)
apply auto
apply (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
done

lemma freevars_replace_Formula_simp2 : "free \<in> freevars (a::Formula) \<longrightarrow> replace (free,free) a = a"
proof (rule, induct a)
  case (Formula_Atprop x)
    have 0: "freevars (Formula_Atprop x) = image (\<lambda>x. Formula_Atprop x) (freevars x)" by simp
    then obtain afree where "afree \<in> freevars x" "Formula_Atprop afree = free"
      by (metis Formula_Atprop.prems freevars_Formula.simps(1) imageE)
    then have "replace (free, free) (Formula_Atprop x) = Formula_Atprop (replace (afree, afree) x)" by (metis replace_Formula.simps(1))
    thus ?case
      by (metis freevars_replace_Atprop_simp freevars_replace_Atprop_simp2)
next
  case (Formula_Freevar x)
    show ?case by simp
next
  case (Formula_Bin x c y)
    have 1: "free \<in> freevars (Formula_Bin x c y) \<longrightarrow> replace (free, free) x = x"
    proof rule
      assume "free \<in> freevars (Formula_Bin x c y)"
    { assume "free \<notin> freevars x" then have "replace (free, free) x = x" using freevars_replace_Formula_simp by simp }
      thus "replace (free, free) x = x" by (metis Formula_Bin.hyps(1))
    qed
    have 2: "free \<in> freevars (Formula_Bin x c y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Formula_Bin x c y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Formula_simp by simp }
      thus "replace (free, free) y = y" by (metis Formula_Bin.hyps(2))
    qed
    have "free \<in> freevars (Formula_Bin x c y) \<longrightarrow> replace (free, free) (Formula_Bin x c y) = Formula_Bin (replace (free, free) x) c (replace (free, free) y)" by (metis replace_Formula.simps)
    with 1 2 show ?case by (metis Formula_Bin.prems)
next
    case (Formula_Action x)
    show ?case by simp
next
  case (Formula_Agent x)
    show ?case by simp
next
  case (Formula_Precondition x)
    have 0: "freevars (Formula_Precondition x) = image (\<lambda>x. Formula_Action x) (freevars x)" by simp
    then obtain afree where "afree \<in> freevars x" "Formula_Action afree = free" 
      by (metis Formula_Precondition.prems freevars_Formula.simps(6) imageE)
    then have "replace (free, free) (Formula_Precondition x) = Formula_Precondition (replace (afree, afree) x)" by (metis replace_Formula.simps(34))
    thus ?case by (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
next
  case (Formula_Action_Formula c x y)
    have 1: "free \<in> freevars (Formula_Action_Formula c x y) \<longrightarrow> replace (free, free) (Formula_Action x) = (Formula_Action x)" by simp
    have 2: "free \<in> freevars (Formula_Action_Formula c x y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Formula_Action_Formula c x y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Formula_simp by simp }
      thus "replace (free, free) y = y" by (metis Formula_Action_Formula.hyps)
    qed
    with 1 have "free \<in> freevars (Formula_Action_Formula c x y) \<longrightarrow> replace (free, free) (Formula_Action_Formula c x y) = Formula_Action_Formula c x (replace (free, free) y)"
      by (cases free, simp_all) (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
    with 2 show ?case by (metis Formula_Action_Formula.prems)
next
  case (Formula_Agent_Formula c x y)
    have 1: "free \<in> freevars (Formula_Agent_Formula c x y) \<longrightarrow> replace (free, free) (Formula_Agent x) = (Formula_Agent x)" by simp
    have 2: "free \<in> freevars (Formula_Agent_Formula c x y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Formula_Agent_Formula c x y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Formula_simp by simp }
      thus "replace (free, free) y = y" by (metis Formula_Agent_Formula.hyps)
    qed
    with 1 have "free \<in> freevars (Formula_Agent_Formula c x y) \<longrightarrow> replace (free, free) (Formula_Agent_Formula c x y) = Formula_Agent_Formula c x (replace (free, free) y)"
      by (cases free, simp_all) (metis freevars_replace_Agent_simp freevars_replace_Agent_simp2)
    with 2 show ?case by (metis Formula_Agent_Formula.prems)
qed



lemma match_Formula_simp : "\<forall>(x, y) \<in> set (match (a::Formula) a). x = y"
proof (induct a)
  case (Formula_Atprop x)
    have 0: "match (Formula_Atprop x) (Formula_Atprop x) = map (\<lambda>(x,y). (Formula_Atprop x, Formula_Atprop y)) (match x x)" by simp
    have "\<forall>a\<in>set (match x x). case a of (x, y) \<Rightarrow> x = y" by (metis match_Atprop_simp)
    then have "\<forall>a\<in>set( map (\<lambda>(x,y). (Formula_Atprop x, Formula_Atprop y)) (match x x)). case a of (x, y) \<Rightarrow> x = y" by auto
    with 0 show ?case using match_Atprop_simp by simp
next
  case (Formula_Freevar x)
    show ?case by auto
next
  case (Formula_Bin x c y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" "\<forall>(a, b) \<in> set (match y y). a = b" 
      by (metis Formula_Bin.hyps(1)) (metis Formula_Bin.hyps(2))
    have 0: "set (match (Formula_Bin x c y) (Formula_Bin x c y)) = set ((match x x) @m (match y y))" by simp
    from Formula_Bin have "set ((match x x) @m (match y y)) = set (match x x) \<union> set (match y y)" by simp
    with assms 0 show ?case by auto
next
  case (Formula_Action x)
    show ?case by simp
next
  case (Formula_Agent x)
    show ?case by simp
next
  case (Formula_Precondition x)
    have 0: "match (Formula_Precondition x) (Formula_Precondition x) = map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x)" by simp
    have "\<forall>a\<in>set (match x x). case a of (x, y) \<Rightarrow> x = y" by (metis match_Action_simp)
    then have "\<forall>a\<in>set( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x)). case a of (x, y) \<Rightarrow> x = y" by auto
    with 0 show ?case using match_Atprop_simp by simp
next
  case (Formula_Action_Formula c x y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Action_simp by simp
    then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
    have 0: "set (match (Formula_Action_Formula c x y) (Formula_Action_Formula c x y)) = set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m (match y y) )" by simp
    with a Formula_Action_Formula have "set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) ) \<union> set (match y y)" by simp
    with assms 0 show ?case by (metis Formula_Action_Formula.hyps Un_iff a)
next
  case (Formula_Agent_Formula c x y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Agent_simp by simp
    then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
    have 0: "set (match (Formula_Agent_Formula c x y) (Formula_Agent_Formula c x y)) = set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m (match y y) )" by simp
    with a Formula_Agent_Formula have "set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) ) \<union> set (match y y)" by simp
    with assms 0 show ?case by (metis Formula_Agent_Formula.hyps Un_iff a)
qed

lemma inv_Formula[simp]:
  fixes a::Formula
  shows "\<forall>free \<in> set (match a a). a = replace free a"
proof (induct a)
  case (Formula_Atprop x)
    show ?case by auto
next
  case (Formula_Bin x c y)
    obtain z where 0: "z = (Formula_Bin x c y)" by simp
    have 1: "\<forall>free \<in> set (match z z). replace free z = Formula_Bin (replace free x) c (replace free y)"
      by (metis "0" old.prod.exhaust replace_Formula.simps)
    have "\<forall>free \<in> set (match z z). replace free x = x" "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Formula_simp by (metis (full_types) splitD)
      have x: "a \<notin> freevars x \<longrightarrow> replace (a,b) x = x" and "a \<in> freevars x \<longrightarrow> replace (a,b) x = x"
        by (metis eq freevars_replace_Formula_simp) (metis freevars_replace_Formula_simp2 eq)
      thus "replace (a, b) x = x" by auto
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Formula_simp) (metis freevars_replace_Formula_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    thus ?case by (metis "0" "1")
next
  case (Formula_Freevar x)
    show ?case by simp
next
  case (Formula_Action x)
    show ?case by simp
next
  case (Formula_Agent x)
    show ?case by simp
next
  case (Formula_Precondition x)
    show ?case by auto
next
  case (Formula_Action_Formula c x y)
    obtain z where 0: "z = (Formula_Action_Formula c x y)" by simp

    have 1: "\<forall>free \<in> set (match z z). replace free (Formula_Action x) = (Formula_Action x)" by auto
    have 2: "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Formula_simp by (metis (full_types) splitD)
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Formula_simp) (metis freevars_replace_Formula_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    
    have "\<forall>free \<in> set (match z z). replace free (Formula_Action_Formula c x y) = Formula_Action_Formula c x (replace free y)"
    proof auto
      fix a b
      assume assm: "(a,b) \<in> set (match z z)"
      then have eq: "a = b" using match_Formula_simp by (metis (full_types) splitD)

      from 0 have "match z z = map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m match y y" by simp 
      then have 3: "set (match z z) = set (map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m (match y y))" by simp 

      have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Action_simp by simp
      then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
      have 0: "set (match (Formula_Action_Formula c x y) (Formula_Action_Formula c x y)) = set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m (match y y) )" by simp
      with a match_Formula_simp have "set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x) ) \<union> set (match y y)" by simp
      with 3 eq 0 assm have ab_in_z: "(a,b) \<in> set (map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x)) \<union> set (match y y)" by simp

      { assume "(a,b) \<in> set (map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x))"
        then obtain a' b' where "Formula_Action a' = a" "Formula_Action b' = b" by auto
        then have 1: "replace (a,b) (Formula_Action_Formula c x y) = Formula_Action_Formula c (replace (a',b') x) (replace (a,b) y)" by auto
        have "(replace (a',b') x) = x" by (metis Formula.inject(1) `Formula_Action a' = a` `Formula_Action b' = b` eq freevars_replace_Action_simp freevars_replace_Action_simp2)
        with 1 have "replace (a,b) (Formula_Action_Formula c x y) = Formula_Action_Formula c x (replace (a,b) y)" by simp }
      { assume "(a,b) \<notin> set (map (\<lambda>(x,y). (Formula_Action x, Formula_Action y)) (match x x))"
        with ab_in_z have "(a,b) \<in> set (match y y)" by simp
        then have 1: "replace (a,b) (Formula_Action_Formula c x y) = Formula_Action_Formula c x (replace (a,b) y)"
          by (cases a, cases b, auto) (metis Formula.inject(1) eq freevars_replace_Action_simp freevars_replace_Action_simp2) }
      thus "replace (a,b) (Formula_Action_Formula c x y) = Formula_Action_Formula c x (replace (a,b) y)" 
        by (metis `(a, b) \<in> set (map (\<lambda>(x, y). (Formula_Action x, Formula_Action y)) (match x x)) \<Longrightarrow> replace (a, b) (ActF\<^sub>F c x y) = ActF\<^sub>F c x replace (a, b) y`)
    qed
    with 0 1 2 show ?case by simp
next
  case (Formula_Agent_Formula c x y)
    obtain z where 0: "z = (Formula_Agent_Formula c x y)" by simp

    have 1: "\<forall>free \<in> set (match z z). replace free (Formula_Agent x) = (Formula_Agent x)" by auto
    have 2: "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Formula_simp by (metis (full_types) splitD)
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Formula_simp) (metis freevars_replace_Formula_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    
    have "\<forall>free \<in> set (match z z). replace free (Formula_Agent_Formula c x y) = Formula_Agent_Formula c x (replace free y)"
    proof auto
      fix a b
      assume assm: "(a,b) \<in> set (match z z)"
      then have eq: "a = b" using match_Formula_simp by (metis (full_types) splitD)

      from 0 have "match z z = map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m match y y" by simp 
      then have 3: "set (match z z) = set (map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m (match y y))" by simp 

      have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Agent_simp by simp
      then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
      have 0: "set (match (Formula_Agent_Formula c x y) (Formula_Agent_Formula c x y)) = set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m (match y y) )" by simp
      with a match_Formula_simp have "set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x) ) \<union> set (match y y)" by simp
      with 3 eq 0 assm have ab_in_z: "(a,b) \<in> set (map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x)) \<union> set (match y y)" by simp

      { assume "(a,b) \<in> set (map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x))"
        then obtain a' b' where "Formula_Agent a' = a" "Formula_Agent b' = b" by auto
        then have 1: "replace (a,b) (Formula_Agent_Formula c x y) = Formula_Agent_Formula c (replace (a',b') x) (replace (a,b) y)" by auto
        have "(replace (a',b') x) = x" by (metis Formula.inject(3) `Formula_Agent a' = a` `Formula_Agent b' = b` eq freevars_replace_Agent_simp freevars_replace_Agent_simp2)
        with 1 have "replace (a,b) (Formula_Agent_Formula c x y) = Formula_Agent_Formula c x (replace (a,b) y)" by simp }
      { assume "(a,b) \<notin> set (map (\<lambda>(x,y). (Formula_Agent x, Formula_Agent y)) (match x x))"
        with ab_in_z have "(a,b) \<in> set (match y y)" by simp
        then have 1: "replace (a,b) (Formula_Agent_Formula c x y) = Formula_Agent_Formula c x (replace (a,b) y)"
          by (cases a, auto, cases b, auto) (metis Formula.inject(3) eq freevars_replace_Agent_simp freevars_replace_Agent_simp2) }
      thus "replace (a,b) (Formula_Agent_Formula c x y) = Formula_Agent_Formula c x (replace (a,b) y)"
        by (metis `(a, b) \<in> set (map (\<lambda>(x, y). (Formula_Agent x, Formula_Agent y)) (match x x)) \<Longrightarrow> replace (a, b) (AgF\<^sub>F c x y) = AgF\<^sub>F c x replace (a, b) y` eq)
    qed
    with 0 1 2 show ?case by simp
qed


lemma inv_Formula2_aux[simp]: 
fixes a::Formula and list
assumes "set list \<subseteq> set (match a a)"
shows "replaceAll list a = a"
using assms
by (induct list a rule:replaceAll.induct, simp) (metis insert_subset inv_Formula replaceAll.simps(2) set_simps(2))

lemma inv_Formula2: "replaceAll (match a a) a = (a::Formula)" by simp





lemma freevars_replace_Structure_simp : "free \<notin> freevars (a::Structure) \<longrightarrow> replace (free,free) a = a"
proof (rule, induct a)
  case Structure_Formula thus ?case by (cases free, auto) (metis freevars_replace_Formula_simp freevars_replace_Formula_simp2)
next
  case Structure_Zer thus ?case by simp
next
  case Structure_Bin thus ?case by simp
next
  case Structure_Freevar thus ?case by simp
next
  case (Structure_Phi act)
    thus ?case
    apply(cases free, cases act, simp_all, case_tac Formula, simp_all, case_tac Action, simp_all)
    by (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
next
  case (Structure_Action_Structure op a s)
    thus ?case 
    apply(cases free, cases s, cases a, simp_all, case_tac Formula, simp_all, case_tac Action, simp_all)
    by (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
next
  case (Structure_Agent_Structure op a s)
    thus ?case 
    apply(cases free, cases s, cases a, simp_all, case_tac Formula, simp_all, case_tac Agent, simp_all)
    by (metis freevars_replace_Agent_simp freevars_replace_Agent_simp2)
qed

lemma freevars_replace_Structure_simp2 : "free \<in> freevars (a::Structure) \<longrightarrow> replace (free,free) a = a"
proof (rule, induct a)
(*(*uncommentL?Structure_Formula*)
  case (Structure_Formula x)
    have 0: "freevars (Structure_Formula x) = image (\<lambda>x. Structure_Formula x) (freevars x)" by simp
    then obtain ffree where "ffree \<in> freevars x"
      by (metis Structure_Formula.prems freevars_Structure.simps(1) imageE)
    with 0 have "replace (free, free) (Structure_Formula x) = Structure_Formula (replace (ffree, ffree) x)" 
    proof -
      have "replace (ffree, ffree) x = x" by (metis `ffree \<in> freevars x` freevars_replace_Formula_simp2)
      thus "replace (free, free) (x \<^sub>S) = replace (ffree, ffree) x \<^sub>S" using Structure_Formula.prems freevars_replace_Formula_simp2 by auto
    qed
    thus ?case
      by (metis freevars_replace_Formula_simp freevars_replace_Formula_simp2)
(*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Zer*)
next
  case (Structure_Zer c)
    thus ?case by simp
(*uncommentR?Structure_Zer*)*)
next
  case (Structure_Freevar x)
    thus ?case by simp
next
  case (Structure_Bin x c y)
    have 1: "free \<in> freevars (Structure_Bin x c y) \<longrightarrow> (replace (free, free) x) = x"
    proof rule
      assume "free \<in> freevars (Structure_Bin x c y)"
    { assume "free \<notin> freevars x" then have "replace (free, free) x = x" using freevars_replace_Structure_simp by simp }
      thus "replace (free, free) x = x" by (metis Structure_Bin.hyps(1))
    qed
    have 2: "free \<in> freevars (Structure_Bin x c y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Structure_Bin x c y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Structure_simp by simp }
      thus "replace (free, free) y = y" by (metis Structure_Bin.hyps(2))
    qed
    have "free \<in> freevars (Structure_Bin x c y) \<longrightarrow> replace (free, free) (Structure_Bin x c y) = Structure_Bin (replace (free, free) x) c (replace (free, free) y)" by (metis replace_Structure.simps(2))
    thus ?case by (metis "1" "2" Structure_Bin.prems)
next
  case (Structure_Phi a)
    thus ?case by(cases free, simp_all, case_tac Formula, simp_all, case_tac Action, simp_all) (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
next
  case (Structure_Action_Structure c x y)
    have 1: "free \<in> freevars (Structure_Action_Structure c x y) \<longrightarrow> replace (free, free) (Structure_Formula (Formula_Action x)) = (Structure_Formula (Formula_Action x))" by(cases free, simp_all)
    have 2: "free \<in> freevars (Structure_Action_Structure c x y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Structure_Action_Structure c x y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Structure_simp by simp }
      thus "replace (free, free) y = y" by (metis Structure_Action_Structure.hyps)
    qed
    with 1 have "free \<in> freevars (Structure_Action_Structure c x y) \<longrightarrow> replace (free, free) (Structure_Action_Structure c x y) = Structure_Action_Structure c x (replace (free, free) y)"
      by (cases free, simp_all, case_tac Formula, simp_all, case_tac Action, simp_all) (metis freevars_replace_Action_simp freevars_replace_Action_simp2)
    with 2 show ?case by (metis Structure_Action_Structure.prems)
next
  case (Structure_Agent_Structure c x y)
    have 1: "free \<in> freevars (Structure_Agent_Structure c x y) \<longrightarrow> replace (free, free) (Structure_Formula (Formula_Agent x)) = (Structure_Formula (Formula_Agent x))" by(cases free, simp_all)
    have 2: "free \<in> freevars (Structure_Agent_Structure c x y) \<longrightarrow> replace (free, free) y = y"
    proof 
      assume "free \<in> freevars (Structure_Agent_Structure c x y)"
    { assume "free \<notin> freevars y" then have "replace (free, free) y = y" using freevars_replace_Structure_simp by simp }
      thus "replace (free, free) y = y" by (metis Structure_Agent_Structure.hyps)
    qed
    with 1 have "free \<in> freevars (Structure_Agent_Structure c x y) \<longrightarrow> replace (free, free) (Structure_Agent_Structure c x y) = Structure_Agent_Structure c x (replace (free, free) y)"
      by (cases free, simp_all, case_tac Formula, simp_all, case_tac Agent, simp_all) (metis freevars_replace_Agent_simp freevars_replace_Agent_simp2)
    with 2 show ?case by (metis Structure_Agent_Structure.prems)
qed


lemma match_Structure_simp : "\<forall>(x, y) \<in> set (match (a::Structure) a). x = y"
proof (induct a)
  case (Structure_Formula x)
    have 0: "match (Structure_Formula x) (Structure_Formula x) = map (\<lambda>(x,y). (Structure_Formula x, Structure_Formula y)) (match x x)" by simp
    have "\<forall>a\<in>set (match x x). case a of (x, y) \<Rightarrow> x = y" by (metis match_Formula_simp)
    then have "\<forall>a\<in>set( map (\<lambda>(x,y). (Structure_Formula x, Structure_Formula y)) (match x x)). case a of (x, y) \<Rightarrow> x = y" by auto
    with 0 show ?case using match_Formula_simp by simp
next
  case (Structure_Zer x)
    show ?case by auto
next
  case (Structure_Freevar x)
    show ?case by auto
next
  case (Structure_Bin x c y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" "\<forall>(a, b) \<in> set (match y y). a = b" 
      by (metis Structure_Bin.hyps(1)) (metis Structure_Bin.hyps(2))
    have 0: "set (match (Structure_Bin x c y) (Structure_Bin x c y)) = set ((match x x) @m (match y y))" by simp
    from Structure_Bin have "set ((match x x) @m (match y y)) = set (match x x) \<union> set (match y y)" by simp
    with assms 0 show ?case by auto
next
  case (Structure_Phi x)
    have 0: "match (Structure_Phi x) (Structure_Phi x) = map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x)" by simp
    have "\<forall>a\<in>set (match x x). case a of (x, y) \<Rightarrow> x = y" by (metis match_Action_simp)
    then have "\<forall>a\<in>set( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
    with 0 show ?case using match_Atprop_simp by simp
next
  case (Structure_Action_Structure c x y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Action_simp by simp
    then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
    have 0: "set (match (Structure_Action_Structure c x y) (Structure_Action_Structure c x y)) = set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x) @m (match y y) )" by simp
    with a Structure_Action_Structure have "set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y))) (match x x) ) \<union> set (match y y)" by simp
    with assms 0 show ?case by (metis Structure_Action_Structure.hyps Un_iff a)
next
  case (Structure_Agent_Structure c x y)
    have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Agent_simp by simp
    then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y))) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
    have 0: "set (match (Structure_Agent_Structure c x y) (Structure_Agent_Structure c x y)) = set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y))) (match x x) @m (match y y) )" by simp
    with a Structure_Agent_Structure have "set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y))) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y))) (match x x) ) \<union> set (match y y)" by simp
    with assms 0 show ?case by (metis Structure_Agent_Structure.hyps Un_iff a)
qed

lemma inv_Structure[simp]:
  fixes a::Structure
  shows "\<forall>free \<in> set (match a a). a = replace free a"
proof (induct a)
  case (Structure_Formula x)
    thus ?case by auto
next
  case (Structure_Zer x)
    show ?case by simp
next
  case (Structure_Bin x c y)
    obtain z where 0: "z = (Structure_Bin x c y)" by simp
    have 1: "\<forall>free \<in> set (match z z). replace free z = Structure_Bin (replace free x) c (replace free y)"
      by (metis "0" old.prod.exhaust replace_Structure.simps(2))
    have "\<forall>free \<in> set (match z z). replace free x = x" "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Structure_simp by (metis (full_types) splitD)
      have x: "a \<notin> freevars x \<longrightarrow> replace (a,b) x = x" and "a \<in> freevars x \<longrightarrow> replace (a,b) x = x"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) x = x" by auto
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    thus ?case by (metis "0" "1")
next
  case (Structure_Freevar x)
    show ?case by simp
next
  case(Structure_Phi x)
    show ?case by auto
next
  case (Structure_Action_Structure c x y)
    obtain z where 0: "z = (Structure_Action_Structure c x y)" by simp

    have 1: "\<forall>free \<in> set (match z z). replace free (Structure_Formula(Formula_Action x)) = (Structure_Formula(Formula_Action x))"
    apply (rule)
    apply(case_tac free, auto)
    apply(case_tac aa, auto)
    apply(case_tac ba, auto)
    done

    have 2: "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Structure_simp by (metis (full_types) splitD)
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    
    have "\<forall>free \<in> set (match z z). replace free (Structure_Action_Structure c x y) = Structure_Action_Structure c x (replace free y)"
    proof auto
      fix a b
      assume assm: "(a,b) \<in> set (match z z)"
      then have eq: "a = b" using match_Structure_simp by (metis (full_types) splitD)

      from 0 have "match z z = map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) @m match y y" by simp 
      then have 3: "set (match z z) = set (map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) @m (match y y))" by simp 

      have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Action_simp by simp
      then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
      have 0: "set (match (Structure_Action_Structure c x y) (Structure_Action_Structure c x y)) = set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) @m (match y y) )" by simp
      with a match_Structure_simp have "set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x) ) \<union> set (match y y)" by simp
      with 3 eq 0 assm have ab_in_z: "(a,b) \<in> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x)) \<union> set (match y y)" by simp

      { assume "(a,b) \<in> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x))"
        then obtain a' b' where fact: "Structure_Formula(Formula_Action a') = a" "Structure_Formula (Formula_Action b') = b" by auto
        then have 1: "replace (a,b) (Structure_Action_Structure c x y) = Structure_Action_Structure c (replace (a',b') x) (replace (a,b) y)" by auto
        with fact have "(replace (a',b') x) = x" by (metis Formula.inject(1) Structure.inject(4) eq freevars_replace_Action_simp freevars_replace_Action_simp2)
        with 1 have "replace (a,b) (Structure_Action_Structure c x y) = Structure_Action_Structure c x (replace (a,b) y)" by simp }
      { assume "(a,b) \<notin> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Action x), Structure_Formula(Formula_Action y)) ) (match x x))"
        with ab_in_z have "(a,b) \<in> set (match y y)" by simp
        then have 1: "replace (a,b) (Structure_Action_Structure c x y) = Structure_Action_Structure c x (replace (a,b) y)"
          apply (cases a, auto, case_tac Formula, simp_all)
          apply (cases b, auto, case_tac Formulaa, simp_all) by (metis Formula.inject(1) Structure.inject(4) eq freevars_replace_Action_simp freevars_replace_Action_simp2) }
      thus "replace (a,b) (Structure_Action_Structure c x y) = Structure_Action_Structure c x (replace (a,b) y)" 
        by (metis `(a, b) \<in> set (map (\<lambda>(x, y). (Formula_Action x \<^sub>S, Formula_Action y \<^sub>S)) (match x x)) \<Longrightarrow> replace (a, b) (ActS\<^sub>S c x y) = ActS\<^sub>S c x replace (a, b) y`)
    qed
    with 0 1 2 show ?case by simp
next
    case (Structure_Agent_Structure c x y)
    obtain z where 0: "z = (Structure_Agent_Structure c x y)" by simp

    have 1: "\<forall>free \<in> set (match z z). replace free (Structure_Formula(Formula_Agent x)) = (Structure_Formula(Formula_Agent x))"
    apply (rule)
    apply(case_tac free, auto)
    apply(case_tac aa, auto)
    apply(case_tac ba, auto)
    done

    have 2: "\<forall>free \<in> set (match z z). replace free y = y"
    proof auto
      fix a b
      assume "(a, b) \<in> set (match z z)"
      then have eq: "a = b" using match_Structure_simp by (metis (full_types) splitD)
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    
    have "\<forall>free \<in> set (match z z). replace free (Structure_Agent_Structure c x y) = Structure_Agent_Structure c x (replace free y)"
    proof auto
      fix a b
      assume assm: "(a,b) \<in> set (match z z)"
      then have eq: "a = b" using match_Structure_simp by (metis (full_types) splitD)

      from 0 have "match z z = map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) @m match y y" by simp 
      then have 3: "set (match z z) = set (map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) @m (match y y))" by simp 

      have assms: "\<forall>(a, b) \<in> set (match x x). a = b" using match_Agent_simp by simp
      then have a: "\<forall>a\<in>set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) ). case a of (x, y) \<Rightarrow> x = y" by auto
      have 0: "set (match (Structure_Agent_Structure c x y) (Structure_Agent_Structure c x y)) = set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) @m (match y y) )" by simp
      with a match_Structure_simp have "set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) @m (match y y)) = 
      set ( map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x) ) \<union> set (match y y)" by simp
      with 3 eq 0 assm have ab_in_z: "(a,b) \<in> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x)) \<union> set (match y y)" by simp

      { assume "(a,b) \<in> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x))"
        then obtain a' b' where fact: "Structure_Formula(Formula_Agent a') = a" "Structure_Formula (Formula_Agent b') = b" by auto
        then have 1: "replace (a,b) (Structure_Agent_Structure c x y) = Structure_Agent_Structure c (replace (a',b') x) (replace (a,b) y)" by auto
        with fact have "(replace (a',b') x) = x" by (metis Formula.inject(3) Structure.inject(4) eq freevars_replace_Agent_simp freevars_replace_Agent_simp2)
        with 1 have "replace (a,b) (Structure_Agent_Structure c x y) = Structure_Agent_Structure c x (replace (a,b) y)" by simp }
      { assume "(a,b) \<notin> set (map (\<lambda>(x,y). (Structure_Formula(Formula_Agent x), Structure_Formula(Formula_Agent y)) ) (match x x))"
        with ab_in_z have "(a,b) \<in> set (match y y)" by simp
        then have 1: "replace (a,b) (Structure_Agent_Structure c x y) = Structure_Agent_Structure c x (replace (a,b) y)"
          apply (cases a, auto, case_tac Formula, simp_all)
          apply (cases b, auto, case_tac Formulaa, simp_all) by (metis Formula.inject(3) Structure.inject(4) eq freevars_replace_Agent_simp freevars_replace_Agent_simp2) }
      thus "replace (a,b) (Structure_Agent_Structure c x y) = Structure_Agent_Structure c x (replace (a,b) y)" 
        by (metis `(a, b) \<in> set (map (\<lambda>(x, y). (Formula_Agent x \<^sub>S, Formula_Agent y \<^sub>S)) (match x x)) \<Longrightarrow> replace (a, b) (AgS\<^sub>S c x y) = AgS\<^sub>S c x replace (a, b) y`)
    qed
    with 0 1 2 show ?case by simp
qed


lemma inv_Structure2_aux[simp]: 
fixes a::Structure and list
assumes "set list \<subseteq> set (match a a)"
shows "replaceAll list a = a"
using assms
by (induct list a rule:replaceAll.induct, simp) (metis insert_subset inv_Structure replaceAll.simps(2) set_simps(2))

lemma inv_Structure2: "replaceAll (match a a) a = (a::Structure)" by simp




instantiation Sequent :: Varmatch
begin   
  fun match_Sequent :: "Sequent \<Rightarrow> Sequent \<Rightarrow> (Sequent * Sequent) list"
  where
    "match_Sequent (Sequent var11 var12) (Sequent var21 var22) = (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) ((match var11 var21) @m (match var12 var22)))"
  | "match_Sequent _ _ = []"
  
  fun freevars_Sequent :: "Sequent \<Rightarrow> Sequent set"
  where
    "freevars_Sequent (Sequent var1 var2) = image (\<lambda>x. Sequent_Structure x) (freevars var1 \<union> freevars var2)"
  | "freevars_Sequent _ = {}"

  fun replace_Sequent :: "(Sequent * Sequent) \<Rightarrow> Sequent \<Rightarrow> Sequent"
  where
    "replace_Sequent ((Sequent_Structure x), (Sequent_Structure rep))  (Sequent var1 var2) = Sequent (replace (x, rep) var1) (replace (x, rep) var2)"
  | "replace_Sequent (_, _) y = y" 
instance ..
end


lemma inv_Sequent[simp]:
  fixes a::Sequent
  shows "\<forall>free \<in> set (match a a). a = replace free a"
proof (induct a)
  case (Sequent_Structure x)
    thus ?case by auto
next
  case (Sequent x y)
    have "\<forall>(a, b) \<in> set (match x x @m match y y). replace (a, b) x = x"  "\<forall>(a, b) \<in> set (match x x @m match y y). replace (a, b) y = y"
    proof auto
      fix a b
      assume 0: "(a, b) \<in> set (match x x @m match y y)"
      have "\<forall>(a, b) \<in> set (match x x). a = b" "\<forall>(a, b) \<in> set (match y y). a = b" by (metis match_Structure_simp)+
      with 0 have eq: "a = b" by auto
      have "a \<notin> freevars x \<longrightarrow> replace (a, b) x = x" and "a \<in> freevars x \<longrightarrow> replace (a, b) x = x"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) x = x" by auto
      from eq have "a \<notin> freevars y \<longrightarrow> replace (a,b) y = y" "a \<in> freevars y \<longrightarrow> replace (a,b) y = y"
        by (metis eq freevars_replace_Structure_simp) (metis freevars_replace_Structure_simp2 eq)
      thus "replace (a, b) y = y" by auto
    qed
    thus ?case by auto
qed


lemma inv_Sequent2_aux[simp]: 
fixes a::Sequent and list
assumes "set list \<subseteq> set (match a a)"
shows "replaceAll list a = a"
using assms
by (induct list a rule:replaceAll.induct, simp) (metis insert_subset inv_Sequent replaceAll.simps(2) set_simps(2))

lemma inv_Sequent2: "replaceAll (match a a) a = (a::Sequent)" by simp

definition "export = (Atprop ''A'')\<^sub>F\<^sub>S \<turnstile>\<^sub>S (Atprop ''A'')\<^sub>F\<^sub>S"

export_code open export in Scala
module_name (*calc_name*) file (*export_path*)
end
