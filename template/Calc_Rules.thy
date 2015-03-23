theory (*calc_name*)
imports Main (*calc_name_core*) "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

(*calc_structure_rules*)


datatype ruleder = ruleder Sequent "Sequent \<Rightarrow> Sequent list" (infix "\<Longrightarrow>RD" 300) |
                   ruleder_cond "Sequent \<Rightarrow> bool" Sequent "Sequent \<Rightarrow> Sequent list" ("_ \<Longrightarrow>C _ \<Longrightarrow>RD _" 300)


fun is_epmod :: "Formula \<Rightarrow> Atprop option" where
"is_epmod (Formula_Atprop p) = Some p"|
"is_epmod (Formula_Action_Formula _ _ f) = is_epmod f"|
"is_epmod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom ((l)\<^sub>S \<turnstile>\<^sub>S (r)\<^sub>S) = ( (is_epmod l) \<noteq> None \<and> (is_epmod l) = (is_epmod r) )"|
"atom _ = False"


fun swapin :: "(Action \<Rightarrow> Agent => Action => bool) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> bool" where
"swapin fun m s = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) (match m s) of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) (match m s) of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> 
                            (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''beta'') \<^sub>S) ) (match m s) of 
                                Some (_, Sequent_Structure (Formula_Action beta \<^sub>S)) \<Rightarrow> fun alpha a beta
                              |  _ \<Rightarrow> False )
                       | _ \<Rightarrow> False)
                 | _ \<Rightarrow> False)"



datatype Locale = Cut_Formula Formula | 
                  RelAKA "Action \<Rightarrow> Agent => Action => bool" |
                  Swapout "Action \<Rightarrow> Agent => Action => bool" "Action list" |
                  Empty

fun rule :: "Locale \<Rightarrow> Rule \<Rightarrow> ruleder"
where
(*rules_rule_fun*)
"rule _ (RuleZer Atom) = ( atom \<Longrightarrow>C 
  ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. [])
)"|
"rule (RelAKA rel) (RuleU swapInL) = ( (swapin rel ( B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) ;\<^sub>S (?\<^sub>S''Y'')  \<turnstile>\<^sub>S (?\<^sub>S''Y'') )) \<Longrightarrow>C 
  ( B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) ;\<^sub>S (?\<^sub>S''Y'')  \<turnstile>\<^sub>S (?\<^sub>S''Y'') ) \<Longrightarrow>RD (\<lambda>x. [])
)"|



"rule (Cut_Formula f) (RuleCut SingleCut) = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. [((?\<^sub>S ''X'') \<turnstile>\<^sub>S f \<^sub>S),(f \<^sub>S \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])"|
"rule _ _ = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. [])"

(*
((Phi alpha) ; forwK a (forwA beta X) \<turnstile> Y
*)
fun fst :: "ruleder \<Rightarrow> Sequent" and snd :: "ruleder \<Rightarrow> (Sequent \<Rightarrow> Sequent list)" and cond :: "ruleder \<Rightarrow> (Sequent \<Rightarrow> bool) option" where
"fst (ruleder x _) = x" |
"fst (ruleder_cond _ x _) = x" |
"snd (ruleder _ y) = y" |
"snd (ruleder_cond _ _ y) = y" |
"cond (ruleder_cond c _ _) = Some c" |
"cond (ruleder _ _) = None"

fun der :: "Locale \<Rightarrow> Rule \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der l r s =( if (ruleMatch (fst (rule l r)) s) then 
              case cond (rule l r) of 
                None \<Rightarrow> ( r, map (replaceAll (match (fst (rule l r)) s) ) ((snd (rule l r)) s) )
              | Some condition \<Rightarrow> ( if condition s 
                              then (r, map (replaceAll (match (fst (rule l r)) s) ) ((snd (rule l r)) s) )
                              else (Fail, []) )
            else (Fail, []) )"


(*(*uncommentL?RuleCut-BEGIN*)*)(*uncommentL?RuleCut-END*)
(*der cut applies a supplied formula if the cut rule is used - a bit hacky atm *) 
(*fun der_cut :: "Rule \<Rightarrow> Formula \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der_cut (RuleCut RuleCut.SingleCut) cutForm s = (if (ruleMatch (fst (rule (RuleCut RuleCut.SingleCut))) s) 
   then ((RuleCut RuleCut.SingleCut), map (replaceAll (match (fst (rule (RuleCut RuleCut.SingleCut))) s @ (map (\<lambda>(x,y). (Sequent_Structure (Structure_Formula x), Sequent_Structure (Structure_Formula y))) (match (?\<^sub>F''A'') cutForm))) ) (snd (rule (RuleCut RuleCut.SingleCut)))) 
   else (Fail, []))" |
"der_cut _ _ _ = (Fail, [])"*)
(*uncommentR?RuleCut-BEGIN*)(*(*uncommentR?RuleCut-END*)*)


fun isProofTree :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTree loc (s \<Longleftarrow> L(r)) = foldr (op \<or>) (map (\<lambda>l. (der l (RuleZer r) s) \<noteq> (Fail, [])) loc) False" |
"isProofTree loc (s \<Longleftarrow> B(r) l) = ( 
  foldr (op \<and>) (map (isProofTree loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"

(*"isProofTree loc (s \<Longleftarrow> B(r) l) = ( foldr (op \<and>) (map (isProofTree loc) l) True \<and> set (Product_Type.snd (der r s)) = set (map concl l) )"*)

(*
fun isProofTreeWCut :: "Prooftree \<Rightarrow> bool" where
"isProofTreeWCut (s \<Longleftarrow> C(f) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der_cut (RuleCut RuleCut.SingleCut) f s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))" |
"isProofTreeWCut (s \<Longleftarrow> Z(r)) = ruleMatch (fst (rule (RuleZer r))) s" | 
"isProofTreeWCut (s \<Longleftarrow> U(r) t) = (isProofTreeWCut t \<and> (case (der (RuleU r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> D(r) t) = (isProofTreeWCut t \<and> (case (der (RuleDisp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> O(r) t) = (isProofTreeWCut t \<and> (case (der (RuleOp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> B(r) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der (RuleBin r) s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))"

lemma isProofTree_concl_freevars[simp]:
  fixes pt
  assumes "isProofTree pt"
  shows "freevars (concl pt) = {}"
proof (cases pt)
case (Zer s r)
  from assms have 1: "ruleMatch (fst (rule (RuleZer r))) s" by (metis (poly_guards_query) Zer isProofTree.simps(1))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Zer concl.simps)
next
case (Unary s r t)
  with assms  have "(der (RuleU r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleU r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Unary concl.simps)
next
case (Display s r t)
  with assms  have "(der (RuleDisp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleDisp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Display concl.simps)
next
case (Operational s r t)
  with assms  have "(der (RuleOp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleOp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Operational concl.simps(4))
next
case (Binary s r t1 t2)
  with assms  have "(der (RuleBin r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleBin r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Binary concl.simps)
next
case (Cut s r t1 t2)
  then have False by (metis assms isProofTree.simps)
  thus ?thesis ..
qed
*)
(*
- equality of shallow and deep terms
  - for every deep-term with a valid proof tree there is an equivalent shallow-term in the set derivable
  - shallow\<Rightarrow>deep possible induction proof on the rules of the shallow embedding set*)

definition "ruleList = (*rules_rule_list*)"

lemma Atprop_without_Freevar[simp]: "\<And>a. freevars a = {} \<Longrightarrow> \<exists>q. a = Atprop q"
  by (metis Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty)

(*
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
*)
export_code open der isProofTree isProofTreeWCut ruleList replaceLPT replaceRPT concl ant consq in Scala
module_name (*calc_name*) file (*export_path*)
end
