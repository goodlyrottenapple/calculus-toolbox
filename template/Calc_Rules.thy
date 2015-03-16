theory (*calc_name*)
imports Main (*calc_name*)_Core "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

datatype RuleZer = 
(*RuleZer*) |
Prem
 
datatype RuleU = 
(*RuleU*)

datatype RuleDisp = 
(*RuleDisp*)

datatype RuleOp = 
(*RuleOp*)

datatype RuleBin = 
(*RuleBin*)

datatype RuleCut = Cut

datatype Rule = RuleZer RuleZer
              | RuleU RuleU
              | RuleDisp RuleDisp
              | RuleOp RuleOp
              | RuleBin RuleBin
              | RuleCut RuleCut
              | Fail

datatype Prooftree = Zer Sequent RuleZer ("_ \<Longleftarrow> Z (_)" [350, 350] 350)
                   | Unary Sequent RuleU Prooftree ("_  \<Longleftarrow> U (_) _"  [350, 350] 350)
                   | Display Sequent RuleDisp Prooftree ("_  \<Longleftarrow> D (_) _"  [341, 341] 350)
                   | Operational Sequent RuleOp  Prooftree ("_ \<Longleftarrow> Op (_) _"  [341, 341] 350)
                   | Binary Sequent RuleBin Prooftree Prooftree ("_  \<Longleftarrow> B (_) _ ; _"  [341, 341] 350)
                   | Cutt Sequent Formula Prooftree Prooftree ("_  \<Longleftarrow> C (_) _ ; _"  [341, 341] 350) (* this pt is different because instead of containing the rule in brackets, it contains the cut formula used in the cut rule*)

fun concl :: "Prooftree \<Rightarrow> Sequent" where
"concl (s \<Longleftarrow> Z(_)) = s" |
"concl (s \<Longleftarrow> U(_) _) = s" |
"concl (s \<Longleftarrow> D(_) _) = s" |
"concl (s \<Longleftarrow> Op(_) _) = s" |
"concl (s \<Longleftarrow> B(_) _ ; _) = s" |
"concl (s \<Longleftarrow> C(_) _ ; _) = s" 

datatype ruleder = ruleder Sequent "Sequent list" (infix "\<Longrightarrow>RD" 300)

fun rule :: "Rule \<Rightarrow> ruleder"
where
(*RuleZer/list*)
(*RuleU/list*)
(*RuleDisp/list*)
(*RuleOp/list*)
(*RuleBin/list*)
"rule _ = ?\<^sub>S''X'' \<turnstile>\<^sub>S ?\<^sub>S''Y'' \<Longrightarrow>RD []"

fun fst :: "ruleder \<Rightarrow> Sequent" and snd :: "ruleder \<Rightarrow> Sequent list"  where
"fst (ruleder x _) = x" |
"snd (ruleder _ y) = y"

fun der :: "Rule \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der (RuleCut Cut) s = (Fail, [])" | (* added this so that normal der cannot accept a cut rule *)
"der r s = (if (ruleMatch (fst (rule r)) s) 
              then (r, map (replaceAll (match (fst (rule r)) s) ) (snd (rule r))) 
              else (Fail, []))"


(*der cut applies a supplied structure if the cut rule is used - a bit hacky atm *) 
fun der_cut :: "Rule \<Rightarrow> Formula \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der_cut (RuleCut Cut) cutForm s = (if (ruleMatch (fst (rule (RuleCut Cut))) s) 
   then ((RuleCut Cut), map (replaceAll (match (fst (rule (RuleCut Cut))) s @ (map (\<lambda>(x,y). (Sequent_Structure (Structure_Formula x), Sequent_Structure (Structure_Formula y))) (match (?\<^sub>F''A'') cutForm))) ) (snd (rule (RuleCut Cut)))) 
   else (Fail, []))" |
"der_cut _ _ _ = (Fail, [])"

fun isProofTree :: "Prooftree \<Rightarrow> bool" where
"isProofTree (s \<Longleftarrow> Z(r)) = ruleMatch (fst (rule (RuleZer r))) s" | (*for modularity, perhaps this should be changed back to a definition like the ones below later...i changed it because it makes proofs in the eq file for the id case easier*)
"isProofTree (s \<Longleftarrow> U(r) t) = (isProofTree t \<and> (case (der (RuleU r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTree (s \<Longleftarrow> D(r) t) = (isProofTree t \<and> (case (der (RuleDisp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTree (s \<Longleftarrow> Op(r) t) = (isProofTree t \<and> (case (der (RuleOp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTree (s \<Longleftarrow> B(r) t1 ; t2) = (isProofTree t1 \<and> isProofTree t2 \<and> (case (der (RuleBin r) s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))" |
"isProofTree (s \<Longleftarrow> C(r) t1 ; t2) = False"

fun isProofTreeWCut :: "Prooftree \<Rightarrow> bool" where
"isProofTreeWCut (s \<Longleftarrow> C(f) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der_cut (RuleCut Cut) f s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))" |
"isProofTreeWCut (s \<Longleftarrow> Z(r)) = ruleMatch (fst (rule (RuleZer r))) s" | 
"isProofTreeWCut (s \<Longleftarrow> U(r) t) = (isProofTreeWCut t \<and> (case (der (RuleU r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> D(r) t) = (isProofTreeWCut t \<and> (case (der (RuleDisp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> Op(r) t) = (isProofTreeWCut t \<and> (case (der (RuleOp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> B(r) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der (RuleBin r) s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))"

lemma isProofTree_concl_freevars[simp]:
  fixes pt
  assumes "isProofTree pt"
  shows "freevars (concl pt) = {}"
proof (cases pt)
case (Zer s r)
  from assms have 1: "ruleMatch (fst (rule (RuleZer r))) s" by (metis (poly_guards_query) Zer isProofTree.simps(1))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Zer concl.simps(1))
next
case (Unary s r t)
  with assms  have "(der (RuleU r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleU r))) s" by (metis der.simps(3))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Unary concl.simps(2))
next
case (Display s r t)
  with assms  have "(der (RuleDisp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleDisp r))) s" by (metis der.simps(4))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Display concl.simps(3))
next
case (Operational s r t)
  with assms  have "(der (RuleOp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleOp r))) s" by (metis der.simps(5))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Operational concl.simps(4))
next
case (Binary s r t1 t2)
  with assms  have "(der (RuleBin r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleBin r))) s" by (metis der.simps(6))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Binary concl.simps(5))
next
case (Cutt s r t1 t2)
  then have False by (metis assms isProofTree.simps(6))
  thus ?thesis ..
qed

(*
- equality of shallow and deep terms
  - for every deep-term with a valid proof tree there is an equivalent shallow-term in the set derivable
  - shallow\<Rightarrow>deep possible induction proof on the rules of the shallow embedding set*)

definition "ruleList = (*rule_list*)"

lemma Atprop_without_Freevar[simp]: "\<And>a. freevars a = {} \<Longrightarrow> \<exists>q. a = Atprop q"
  by (metis Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty)


(*perhaps things bellow should be moved to a separate utils file?? *)

fun replaceLPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceLPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) rep ; t2)" |
"replaceLPT pt rep = pt"

fun replaceRPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceRPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) t1 ; rep)" |
"replaceRPT pt rep = pt"

fun ant :: "Sequent \<Rightarrow> Structure" and consq :: "Sequent \<Rightarrow> Structure" where
"ant (Sequent x y) = x" |
"ant (Sequent_Structure x) = x" |
"consq (Sequent x y) = y"|
"consq (Sequent_Structure x) = x"

export_code open der isProofTree isProofTreeWCut ruleList replaceLPT replaceRPT concl ant consq in Scala
module_name (*calc_name*) file "(*export_path*)(*calc_name*).scala"
end
