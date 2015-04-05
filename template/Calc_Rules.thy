theory (*calc_name*)
imports Main (*calc_name_core*) "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

(*calc_structure_rules*)

fun concl :: "Prooftree \<Rightarrow> Sequent" where
"concl (a \<Longleftarrow> PT ( b ) c) = a"

datatype ruleder = ruleder      Sequent "Sequent \<Rightarrow> Sequent list option" (infix "\<Longrightarrow>RD" 300) |
                   ruleder_cond "Sequent \<Rightarrow> bool" Sequent "Sequent \<Rightarrow> Sequent list option" ("_ \<Longrightarrow>C _ \<Longrightarrow>RD _" 300)


fun is_epmod :: "Formula \<Rightarrow> Atprop option" where
"is_epmod (Formula_Atprop p) = Some p"|
"is_epmod (Formula_Action_Formula _ _ f) = is_epmod f"|
"is_epmod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom ((l)\<^sub>S \<turnstile>\<^sub>S (r)\<^sub>S) = ( (is_epmod l) \<noteq> None \<and> (is_epmod l) = (is_epmod r) )"|
"atom _ = False"

fun relAKACheck :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> bool" where
"relAKACheck fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> 
                            (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''beta'') \<^sub>S) ) mlist of 
                                Some (_, Sequent_Structure (Formula_Action beta \<^sub>S)) \<Rightarrow> (case List.find ( \<lambda>(x::Action). x = beta ) (fun alpha a) of Some res \<Rightarrow> True | None \<Rightarrow> False)
                              |  _ \<Rightarrow> False )
                       | _ \<Rightarrow> False)
                 | _ \<Rightarrow> False)"

fun betaList :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> (Action list)" where
"betaList fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> fun alpha a
                       | _ \<Rightarrow> [])
                 | _ \<Rightarrow> [])"

fun swapin :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> bool" where
"swapin fun m s = relAKACheck fun (match m s)"


fun bigcomma_cons_L :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L ( (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y ) = Some [(;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L _ = None"

fun bigcomma_cons_L2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L2 ( ;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y ) = Some [((B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L2 _ = None"


fun bigcomma_cons_R :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R ( Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) ) = Some [(Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs))]"|
"bigcomma_cons_R _ = None"

fun bigcomma_cons_R2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R2 ( Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs) ) = Some [(Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)))]"|
"bigcomma_cons_R2 _ = None"

(*
value"replaceAll (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#(match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) X))) (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
value"(AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (ActS\<^sub>S (forwA\<^sub>S) (Action ''beta'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) (ActS\<^sub>S (forwA\<^sub>S) (Action ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"(ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))"
*)
fun swapout_L_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L_aux relAKA [] seq ( X \<turnstile>\<^sub>S ;;\<^sub>S [] ) = Some []" |
"swapout_L_aux relAKA (b#list) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = (
  case ( swapout_L_aux relAKA list seq ( X \<turnstile>\<^sub>S ;;\<^sub>S Ys ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_L_aux relAKA _ _ _ = None"

fun swapout_L :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L relAKA seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = 
    swapout_L_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) " |
"swapout_L _ _ _ = None"


fun swapout_R_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R_aux relAKA [] seq ( ;;\<^sub>S [] \<turnstile>\<^sub>S X ) = Some []" |
"swapout_R_aux relAKA (b#list) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = (
  case ( swapout_R_aux relAKA list seq ( ;;\<^sub>S Ys \<turnstile>\<^sub>S X ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_R_aux _ _ _ _ = None"


fun swapout_R :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R relAKA seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = 
    swapout_R_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) " |
"swapout_R _ _ _ = None"



(*
fun relAKAA :: "Action \<Rightarrow> Agent \<Rightarrow> Action \<Rightarrow> bool" where
"relAKAA (Action x) (Agent a) (Action y) = ((x = y) \<or> (x=''ep'' \<and> a = ''c'' \<and> y=''ew''))" |
"relAKAA _ _ _ = False"

definition "const_seq = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
definition "seq_empty = ((;;\<^sub>S []) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seq = ((;;\<^sub>S [((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)]) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seqO = (((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S) \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (Agent ''c'') ActS\<^sub>S forwA\<^sub>S (Action ''epa'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S) )"

definition "mtchList X b Y= (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))))"

definition "mList = mtchList ((ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S)))) (Action(''epa'')) ((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)"
value " match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO "
value "relAKACheck relAKAA (List.union (match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO) mList)"
value "swapout_R relAKAA [] const_seq seq_empty"
value "swapout_R relAKAA [Action(''epa'')] const_seq seq"


value"swapout_L rel blist ( (?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X'') )"
*)


datatype Locale = CutFormula Formula | 
                  Premise Sequent |
                  RelAKA "Action \<Rightarrow> Agent \<Rightarrow> Action list" |
                  Empty

(*rules_rule_fun*)

fun fst :: "ruleder \<Rightarrow> Sequent" and snd :: "ruleder \<Rightarrow> Sequent \<Rightarrow> Sequent list option" and cond :: "ruleder \<Rightarrow> (Sequent \<Rightarrow> bool) option" where
"fst (ruleder x _) = x" |
"fst (ruleder_cond _ x _) = x" |
"snd (ruleder _ y) = y" |
"snd (ruleder_cond _ _ y) = y" |
"cond (ruleder_cond c _ _) = Some c" |
"cond (ruleder _ _) = None"

fun der :: "Locale \<Rightarrow> Rule \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der l r s =( case (snd (rule l r)) s of
                None \<Rightarrow> (Fail, [])
              | Some conclusion \<Rightarrow> 
                  if (ruleMatch (fst (rule l r)) s) then 
                    case cond (rule l r) of 
                      None \<Rightarrow> ( r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                    | Some condition \<Rightarrow> ( if condition s 
                        then (r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                        else (Fail, []) )
                  else (Fail, []) )"


(*(*uncommentL?RuleCut*)
(*der cut applies a supplied formula if the cut rule is used - a bit hacky atm *) 
(*fun der_cut :: "Rule \<Rightarrow> Formula \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der_cut (RuleCut RuleCut.SingleCut) cutForm s = (if (ruleMatch (fst (rule (RuleCut RuleCut.SingleCut))) s) 
   then ((RuleCut RuleCut.SingleCut), map (replaceAll (match (fst (rule (RuleCut RuleCut.SingleCut))) s @ (map (\<lambda>(x,y). (Sequent_Structure (Structure_Formula x), Sequent_Structure (Structure_Formula y))) (match (?\<^sub>F''A'') cutForm))) ) (snd (rule (RuleCut RuleCut.SingleCut)))) 
   else (Fail, []))" |
"der_cut _ _ _ = (Fail, [])"*)
(*uncommentR?RuleCut*)*)

primrec ant :: "Sequent \<Rightarrow> Structure" where
"ant (Sequent x y) = x" |
"ant (Sequent_Structure x) = x"
primrec consq :: "Sequent \<Rightarrow> Structure" where
"consq (Sequent x y) = y"|
"consq (Sequent_Structure x) = x"

fun replaceIntoPT_aux :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree \<Rightarrow> Prooftree" and 
  replaceIntoPT_list :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree list \<Rightarrow> Prooftree list" where 
"replaceIntoPT_aux list (Prooftree c (RuleMacro s pt) ptlist) = Prooftree (replaceAll list c) (RuleMacro s (replaceIntoPT_aux list pt)) (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_aux list (Prooftree c r ptlist) = Prooftree (replaceAll list c) r (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_list list [] = []" |
"replaceIntoPT_list list (l#ist) = (replaceIntoPT_aux list l)#(replaceIntoPT_list list ist)"

fun replaceIntoPT :: "Sequent \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceIntoPT seq (Prooftree c r ptlist) = replaceIntoPT_aux (match c seq) (Prooftree c r ptlist)"


fun collectPremises :: "Prooftree \<Rightarrow> Sequent list" where
"collectPremises (Prooftree p (RuleZer Prem) []) = [p]" |
"collectPremises (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectPremises list) (collectPremises pt)" |
"collectPremises (Prooftree _ _ list) = foldr append (map collectPremises list) []"

fun collectPremisesToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectPremisesToLocale pt = map Premise (collectPremises pt)"

fun collectCutFormulas :: "Prooftree \<Rightarrow> Formula list" where
"collectCutFormulas (Prooftree _ (RuleCut _) [l, r]) = (
  (case (consq (concl l)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl r)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] else []) |  _ \<Rightarrow> []) |
    _ \<Rightarrow> (case (consq (concl r)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl l)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] else []) |  _ \<Rightarrow> []))
  )
)" |
"collectCutFormulas (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectCutFormulas list) (collectCutFormulas pt)" |
"collectCutFormulas (Prooftree _ _ list) = foldr append (map collectCutFormulas list) []"

fun collectCutFormulasToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectCutFormulasToLocale pt = map CutFormula (collectCutFormulas pt)"


fun isProofTree :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTree loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = (
  s = (concl pt) \<and> 
  isProofTree (append loc (collectPremisesToLocale pt)) pt \<and>
  set (collectPremises pt) = set (map concl ptlist) \<and>
  foldr (op \<and>) (map (isProofTree loc) ptlist) True
)"|
"isProofTree loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTree loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"

fun isProofTreeWithCut :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWithCut loc pt = isProofTree (append loc (collectCutFormulasToLocale pt)) pt"

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
*)

primrec rulifyAgent :: "Agent \<Rightarrow> Agent" where
"rulifyAgent (Agent a) = Agent_Freevar a" |
"rulifyAgent (Agent_Freevar a) = Agent_Freevar a"

primrec rulifyAction :: "Action \<Rightarrow> Action" where
"rulifyAction (Action a) = Action_Freevar a" |
"rulifyAction (Action_Freevar a) = Action_Freevar a"


fun rulifyFormula :: "Formula \<Rightarrow> Formula" where
"rulifyFormula (Formula_Atprop(Atprop (f#a))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (Formula_Freevar (f#a)) else (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
"rulifyFormula (Formula_Bin x c y) = (Formula_Bin (rulifyFormula x) c (rulifyFormula y))" |
"rulifyFormula (Formula_Agent_Formula c a x) = (Formula_Agent_Formula c (rulifyAgent a) (rulifyFormula x) )" |
"rulifyFormula (Formula_Action_Formula c a x) = (Formula_Action_Formula c (rulifyAction a) (rulifyFormula x) )" |
"rulifyFormula (Formula_Precondition a) = (Formula_Precondition (rulifyAction a))" |
"rulifyFormula x = x"



fun rulifyStructure :: "Structure \<Rightarrow> Structure" where
"rulifyStructure (Structure_Formula (Formula_Atprop(Atprop (f#a)))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (
  if f = CHR ''F'' then Structure_Formula (Formula_Freevar (f#a)) else Structure_Freevar (f#a)
  ) else Structure_Formula (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
"rulifyStructure (Structure_Formula x) = Structure_Formula (rulifyFormula x)" | 
"rulifyStructure (Structure_Bin x c y) = (Structure_Bin (rulifyStructure x) c (rulifyStructure y))" |
"rulifyStructure (Structure_Agent_Structure c a x) = (Structure_Agent_Structure c (rulifyAgent a) (rulifyStructure x) )" |
"rulifyStructure (Structure_Action_Structure c a x) = (Structure_Action_Structure c (rulifyAction a) (rulifyStructure x) )" |
"rulifyStructure (Structure_Bigcomma list) = (Structure_Bigcomma (map rulifyStructure list))" |
"rulifyStructure (Structure_Phi a) = (Structure_Phi (rulifyAction a))" |
"rulifyStructure x = x"

primrec rulifySequent :: "Sequent \<Rightarrow> Sequent" where
"rulifySequent (Sequent x y) = Sequent (rulifyStructure x) (rulifyStructure y)"|
"rulifySequent (Sequent_Structure x) = (Sequent_Structure x)"

fun rulifyProoftree :: "Prooftree \<Rightarrow> Prooftree" where
"rulifyProoftree (Prooftree s r list) = (Prooftree (rulifySequent s) r (map rulifyProoftree list))"


export_code open der isProofTree ruleList ant consq rulifyProoftree replaceIntoPT isProofTreeWithCut in Scala
module_name (*calc_name*) file (*export_path*)
end
