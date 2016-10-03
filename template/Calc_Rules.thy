theory (*calc_name*)
imports Main (*calc_name_core*) "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

(*calc_structure_rules*)

(*This function simply returns the sequent at the root of a proof tree *)
fun concl :: "Prooftree \<Rightarrow> Sequent" where
"concl (a \<Longleftarrow> PT ( b ) c) = a"

datatype ruleder = ruleder      Sequent "Sequent \<Rightarrow> Sequent list option" (infix "\<Longrightarrow>RD" 300) |
                   ruleder_cond "Sequent \<Rightarrow> bool" Sequent "Sequent \<Rightarrow> Sequent list option" ("_ \<Longrightarrow>C _ \<Longrightarrow>RD _" 300)


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)
(*This function is an auxillary function which tries to unwrap any Structure_Action_Structure constructors and 
will return an Atprop if the structure contains no other constructors otherwise it will return None*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_Action_Structure _ _ s) = is_act_mod s"|
"is_act_mod _ = None"

(*The atom function is used by the atom rule. to check that the sequent is of a certain form.*)
fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"|
"atom _ = False"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)*)

(*(*uncommentL?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent*)
(*relAKACheck takes in a an action structure and a list deconstructed parts of a sequent and checks
whether the list contains an Action alpha, Agent a and Action beta that are in the action structure*)

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

fun swapin :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> bool" where
"swapin fun m s = relAKACheck fun (match m s)"
(*uncommentR?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent*)*)

(*(*uncommentL?Structure_Bigcomma*)
(* These are custom rules for the bigcomma *)
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
(*uncommentR?Structure_Bigcomma*)*)


(*(*uncommentL?RuleSwapout*)
fun swapout_L' :: "Action list \<Rightarrow> Action \<Rightarrow> Agent \<Rightarrow> Structure \<Rightarrow> Structure list \<Rightarrow> Sequent list option" where
"swapout_L' [] alpha a X [] = Some ([])" |
"swapout_L' (beta#actionList) alpha a X [] = None" |
"swapout_L' [] alpha a X (Y # Ys) = None" |
"swapout_L' (beta#actionList) alpha a X (Y # Ys) = (case swapout_L' actionList alpha a X Ys of 
   Some list \<Rightarrow> Some ((AgS\<^sub>S forwK\<^sub>S a ActS\<^sub>S forwA\<^sub>S beta X \<turnstile>\<^sub>S Y) #list) | None \<Rightarrow> None )"

fun swapout_L :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L relAKA ( ActS\<^sub>S forwA\<^sub>S alpha (AgS\<^sub>S forwK\<^sub>S a X ) \<turnstile>\<^sub>S ;;\<^sub>S list ) = swapout_L' (relAKA alpha a) alpha a X list" |
"swapout_L _ _ = None"

fun swapout_R' :: "Action list \<Rightarrow> Action \<Rightarrow> Agent \<Rightarrow> Structure \<Rightarrow> Structure list \<Rightarrow> Sequent list option" where
"swapout_R' [] alpha a X [] = Some ([])" |
"swapout_R' (beta#actionList) alpha a X [] = None" |
"swapout_R' [] alpha a X (Y # Ys) = None" |
"swapout_R' (beta#actionList) alpha a X (Y # Ys) = (case swapout_R' actionList alpha a X Ys of 
   Some list \<Rightarrow> Some ((Y \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S a ActS\<^sub>S forwA\<^sub>S beta X) #list) | None \<Rightarrow> None )"

fun swapout_R :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R relAKA ( ;;\<^sub>S list \<turnstile>\<^sub>S ActS\<^sub>S forwA\<^sub>S alpha (AgS\<^sub>S forwK\<^sub>S a X ) ) = swapout_R' (relAKA alpha a) alpha a X list" |
"swapout_R _ _ = None"
(*uncommentR?RuleSwapout*)*)


(*(*uncommentL?Pre_L*)
fun pre_l :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_l a ((One\<^sub>F alpha)\<^sub>S \<turnstile>\<^sub>S X) = (a = alpha)"|
"pre_l a _ = False"
(*uncommentR?Pre_L*)*)

(*(*uncommentL?Pre_R*)
fun pre_r :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_r a (X \<turnstile>\<^sub>S (One\<^sub>F alpha)\<^sub>S) = (a = alpha)"|
"pre_r a _ = False"
(*uncommentR?Pre_R*)*)


datatype Locale = (*(*uncommentL?Formula?RuleCut*)
                  CutFormula Formula |
                  (*uncommentR?Formula?RuleCut*)*)
                  (*(*uncommentL?Sequent*)
                  Premise Sequent |
                  (*uncommentR?Sequent*)*)
                  (*(*uncommentL?Structure*)
                  Part Structure |
                  (*uncommentR?Structure*)*)
                  (*(*uncommentL?Action?Agent*)
                  RelAKA "Action \<Rightarrow> Agent \<Rightarrow> Action list" | 
                  (*uncommentR?Action?Agent*)*)
                  (*(*uncommentL?Action?Formula*)
                  PreFormula Action Formula |
                  (*uncommentR?Action?Formula*)*)
                  (*(*uncommentL?Agent*)
                  LAgent Agent |
                  (*uncommentR?Agent*)*)
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


primrec ant :: "Sequent \<Rightarrow> Structure" where
"ant (Sequent x y) = x" |
"ant (Sequent_Structure x) = x"
primrec consq :: "Sequent \<Rightarrow> Structure" where
"consq (Sequent x y) = y"|
"consq (Sequent_Structure x) = x"


(*collectPremises returns all the leaves of a prooftree where the Prem rule has been applied *)
fun collectPremises :: "Prooftree \<Rightarrow> Sequent list" where
"collectPremises (Prooftree p (RuleZer Prem) []) = [p]" |
"collectPremises (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectPremises list) []" |
"collectPremises (Prooftree _ _ list) = foldr append (map collectPremises list) []"

fun collectPremisesToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectPremisesToLocale pt = map Premise (collectPremises pt)"

(*collectCutFormulas returns all cut formulas used in a prooftree,
by checking for a matching branch on the left and the right hand side of the turnstyle of the two leaves *)

fun collectCutFormulas :: "Prooftree \<Rightarrow> Formula list" where
"collectCutFormulas (Prooftree _ (RuleCut _) [l, r]) = (
  (case (consq (concl l)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl r)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r) ) |
    _ \<Rightarrow> (case (consq (concl r)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl l)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r)))
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


fun isProofTreeWoMacro :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = False"|
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTreeWoMacro loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"

fun isProofTreeWithCut :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWithCut loc pt = isProofTree (append loc (collectCutFormulasToLocale pt)) pt"


definition "ruleList = (*rules_rule_list*)"

lemma Atprop_without_Freevar[simp]: "\<And>a. freevars a = {} \<Longrightarrow> \<exists>q. a = Atprop q"
  by (metis Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty)


(* The rulify_ definitions are used for creating macros in the UI,
by turning a proof tree of concrete terms into a proof tree containing free variables.
This is done by converting every leaf of a Sequent into a Freevar term of the highest level of that term 
(i.e. if a sequent contains an atprop it it will be turned into a sequent freevar). *)

(*(*uncommentL?Agent?Agent_Freevar*)
primrec rulifyAgent :: "Agent \<Rightarrow> Agent" where
"rulifyAgent (Agent a) = Agent_Freevar a" |
"rulifyAgent (Agent_Freevar a) = Agent_Freevar a"
(*uncommentR?Agent?Agent_Freevar*)*)

(*(*uncommentL?Action?Action_Freevar*)
primrec rulifyAction :: "Action \<Rightarrow> Action" where
"rulifyAction (Action a) = Action_Freevar a" |
"rulifyAction (Action_Freevar a) = Action_Freevar a"
(*uncommentR?Action?Action_Freevar*)*)

(*(*uncommentL?Formula*)
fun rulifyFormula :: "Formula \<Rightarrow> Formula" where
(*(*uncommentL?Formula_Atprop*)
"rulifyFormula (Formula_Atprop(Atprop (f#a))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (Formula_Freevar (f#a)) else (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Formula_Atprop*)*)
(*(*uncommentL?Formula_Un*)
"rulifyFormula (Formula_Un c y) = (Formula_Un c (rulifyFormula y))" |
(*uncommentR?Formula_Un*)*)
(*uncommentR?Formula_Bin*)*)
(*(*uncommentL?Formula_Bin*)
"rulifyFormula (Formula_Bin x c y) = (Formula_Bin (rulifyFormula x) c (rulifyFormula y))" |
(*uncommentR?Formula_Bin*)*)
(*(*uncommentL?Formula_Agent_Formula*)
"rulifyFormula (Formula_Agent_Formula c a x) = (Formula_Agent_Formula c (rulifyAgent a) (rulifyFormula x) )" |
(*uncommentR?Formula_Agent_Formula*)*)
(*(*uncommentL?Formula_Action_Formula*)
"rulifyFormula (Formula_Action_Formula c a x) = (Formula_Action_Formula c (rulifyAction a) (rulifyFormula x) )" |
(*uncommentR?Formula_Action_Formula*)*)
(*(*uncommentL?Formula_Precondition*)
"rulifyFormula (Formula_Precondition a) = (Formula_Precondition (rulifyAction a))" |
(*uncommentR?Formula_Precondition*)*)
"rulifyFormula x = x"
(*uncommentR?Formula*)*)

(*(*uncommentL?Structure*)
(*if the leaf is a formula with a name beginning with 'F', 
the term will be turned into a Formula_Freevar, else it will become a Structure_Freevar*)

fun rulifyStructure :: "Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Formula?Formula_Atprop*)
"rulifyStructure (Structure_Formula (Formula_Atprop(Atprop (f#a)))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (
  if f = CHR ''F'' then Structure_Formula (Formula_Freevar (f#a)) else Structure_Freevar (f#a)
  ) else Structure_Formula (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Structure_Formula?Formula_Atprop*)*)
(*(*uncommentL?Structure_Formula*)
"rulifyStructure (Structure_Formula x) = Structure_Formula (rulifyFormula x)" | 
(*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Bin*)
"rulifyStructure (Structure_Bin x c y) = (Structure_Bin (rulifyStructure x) c (rulifyStructure y))" |
(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Agent_Structure*)
"rulifyStructure (Structure_Agent_Structure c a x) = (Structure_Agent_Structure c (rulifyAgent a) (rulifyStructure x) )" |
(*uncommentR?Structure_Agent_Structure*)*)
(*(*uncommentL?Structure_Action_Structure*)
"rulifyStructure (Structure_Action_Structure c a x) = (Structure_Action_Structure c (rulifyAction a) (rulifyStructure x) )" |
(*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Bigcomma*)
"rulifyStructure (Structure_Bigcomma list) = (Structure_Bigcomma (map rulifyStructure list))" |
(*uncommentR?Structure_Bigcomma*)*)
(*(*uncommentL?Structure_Phi*)
"rulifyStructure (Structure_Phi a) = (Structure_Phi (rulifyAction a))" |
(*uncommentR?Structure_Phi*)*)
"rulifyStructure x = x"
(*uncommentR?Structure*)*)

(*(*uncommentL?Sequent*)
primrec rulifySequent :: "Sequent \<Rightarrow> Sequent" where
"rulifySequent (Sequent x y) = Sequent (rulifyStructure x) (rulifyStructure y)"|
"rulifySequent (Sequent_Structure x) = (Sequent_Structure x)"
(*uncommentR?Sequent*)*)

fun rulifyProoftree :: "Prooftree \<Rightarrow> Prooftree" where
"rulifyProoftree (Prooftree s (RuleMacro str pt) list) = Prooftree (rulifySequent s) (RuleMacro str (rulifyProoftree pt)) (map rulifyProoftree list)" |
"rulifyProoftree (Prooftree s r list) = (Prooftree (rulifySequent s) r (map rulifyProoftree list))"


(*This function is used to replace any freevar terms in a sequent by a given term, but does this throughout a whole prooftree.
The function is used when applying a macro, where the freevars are substituted by concrete terms of the sequent that the macro is being used on *)

fun replaceSequentIntoPT_aux :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree \<Rightarrow> Prooftree" and 
  replaceSequentIntoPT_list :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree list \<Rightarrow> Prooftree list" where 
"replaceSequentIntoPT_aux list (Prooftree c (RuleMacro s pt) ptlist) = Prooftree (replaceAll list c) (RuleMacro s (replaceSequentIntoPT_aux list pt)) (replaceSequentIntoPT_list list ptlist)" |
"replaceSequentIntoPT_aux list (Prooftree c r ptlist) = Prooftree (replaceAll list c) r (replaceSequentIntoPT_list list ptlist)" |
"replaceSequentIntoPT_list list [] = []" |
"replaceSequentIntoPT_list list (l#ist) = (replaceSequentIntoPT_aux list l)#(replaceSequentIntoPT_list list ist)"

fun replaceSequentIntoPT :: "Sequent \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceSequentIntoPT seq (Prooftree c r ptlist) = replaceSequentIntoPT_aux (match c seq) (Prooftree c r ptlist)"

(* The following two functions are used to turn a pt containing macros into a one which doesnt, by merging any proof trees found in RulMacro into the main pt*)
fun replacePTIntoPT :: "Prooftree list \<Rightarrow> Prooftree \<Rightarrow> Prooftree"  where
"replacePTIntoPT [] (Prooftree s (RuleZer Prem) []) = (Prooftree s (RuleZer Prem) [])" |
"replacePTIntoPT (l#ist) (Prooftree s (RuleZer Prem) []) = (if (concl l) = s then l else replacePTIntoPT ist (Prooftree s (RuleZer Prem) []))" |
"replacePTIntoPT list (Prooftree s r []) =  (Prooftree s r [])" |
"replacePTIntoPT list (Prooftree s r l) =  (Prooftree s r (map (replacePTIntoPT list) l))"

fun expandProoftree :: "Prooftree \<Rightarrow> Prooftree"  where
"expandProoftree (Prooftree _ (RuleMacro n (Prooftree s r l)) list) = (Prooftree s r (map (replacePTIntoPT (map expandProoftree list)) (map expandProoftree l)))" |
"expandProoftree (Prooftree s r list) = Prooftree s r (map expandProoftree list)"


(* collect_freevars_Structure and collect_freevars_Sequent are used to analyze the shape of a rule by the is_display_rule function *)
fun collect_freevars_Structure :: "Structure \<Rightarrow> Structure list" where
(*(*uncommentL?Structure_Formula*)  "collect_freevars_Structure (Structure_Formula f) = [Structure_Formula f]" (*uncommentR?Structure_Formula*)*)
(*(*uncommentL?Structure_Bin*) | "collect_freevars_Structure (Structure_Bin l _ r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" (*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Freevar*) | "collect_freevars_Structure (Structure_Freevar free) = [Structure_Freevar free]" (*uncommentR?Structure_Freevar*)*)
(*(*uncommentL?Structure_Action_Structure*) | "collect_freevars_Structure (Structure_Action_Structure oper ac struct) = [Structure_Formula (Formula_Action ac)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) | "collect_freevars_Structure (Structure_Agent_Structure oper ag struct) = [Structure_Formula (Formula_Agent ag)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Agent_Structure*)*)
(*(*uncommentL?Structure_Phi*) | "collect_freevars_Structure (Structure_Phi a) = [Structure_Phi a]"  (*uncommentR?Structure_Phi*)*)
(*(*uncommentL?Structure_Zer*) | "collect_freevars_Structure (Structure_Zer z) = [Structure_Zer z]" (*uncommentR?Structure_Zer*)*)
(*(*uncommentL?Structure_Bigcomma*) | "collect_freevars_Structure (Structure_Bigcomma list) = foldr (op @) (map collect_freevars_Structure list) []" (*uncommentR?Structure_Bigcomma*)*)


fun collect_freevars_Sequent :: "Sequent \<Rightarrow> Structure list" where
"collect_freevars_Sequent (Sequent l r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" |
"collect_freevars_Sequent (Sequent_Structure _) = []"


fun is_display_rule :: "Rule \<Rightarrow> Rule list" where
"is_display_rule r = 
(if (case (snd (rule Empty r) (fst (rule Empty r)) ) of Some list \<Rightarrow>
  (case list of h#rest \<Rightarrow>
  mset (collect_freevars_Sequent (fst (rule Empty r))) = 
  mset (collect_freevars_Sequent h ) | _ \<Rightarrow> False ) | _ \<Rightarrow> False )
then [r] 
else [])"

definition displayRules :: "Rule list" where
"displayRules = foldr (op @) (map is_display_rule ruleList) []"


(* The following definitions are used for the display_tac in the GUI *)

datatype polarity = Plus ("+p") | Minus ("-p") | N

fun polarity_weird_xor :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<or>p" 400) where
"polarity_weird_xor +p N = +p" |
"polarity_weird_xor -p N = -p" |
"polarity_weird_xor N x = x" |
"polarity_weird_xor +p _ = N" |
"polarity_weird_xor -p _ = N"


fun polarity_not :: "polarity \<Rightarrow> polarity" ( "\<not>p _") where
"polarity_not -p = +p" |
"polarity_not +p = -p" |
"polarity_not N = N"


fun polarity_weird_and :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<and>p" 400) where
"polarity_weird_and -p x = \<not>p x" |
"polarity_weird_and +p x = x" |
"polarity_weird_and N _ = N"

lemma polarity_weird_xor_comm: "a \<or>p b = b \<or>p a"
apply (cases a, (cases b, auto)+)
done

lemma polarity_weird_and_comm: "a \<and>p b = b \<and>p a"
apply (cases a, (cases b, auto)+)
done

(*this function defines the polarity of the different structural connectives in the display calculus*)
fun structure_Op_polarity :: "Structure_Bin_Op \<Rightarrow> (polarity \<times> polarity)" where
(*(*uncommentL?Structure_Comma*) 
   "structure_Op_polarity Structure_Comma = (+p, +p)"
(*uncommentR?Structure_Comma*)*)
(*(*uncommentL?Structure_ImpL*) 
 | "structure_Op_polarity Structure_ImpL = (+p, -p)"
(*uncommentR?Structure_ImpL*)*)
(*(*uncommentL?Structure_ImpR*) 
 | "structure_Op_polarity Structure_ImpR = (-p, +p)"
(*uncommentR?Structure_ImpR*)*)


(*we assume the structure appears in the sequent exactly once*)
fun polarity_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> polarity" where
(*(*uncommentL?Structure_Bin*) 
"polarity_Structure s (Structure_Bin l oper r) = (
  if l = s then prod.fst (structure_Op_polarity oper)
  else if r = s then prod.snd (structure_Op_polarity oper)
  else ((prod.fst (structure_Op_polarity oper)) \<and>p (polarity_Structure s l)) \<or>p ((prod.snd (structure_Op_polarity oper)) \<and>p (polarity_Structure s r)) )" | 
(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Action_Structure*) "polarity_Structure s (Structure_Action_Structure oper ac struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "polarity_Structure s (Structure_Agent_Structure oper ag struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Agent_Structure*)*)
"polarity_Structure s x = (if s = x then +p else N)"


fun polarity_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"polarity_Sequent s (Sequent lhs rhs) = (\<not>p(polarity_Structure s lhs)) \<or>p (polarity_Structure s rhs)" |
"polarity_Sequent s _ = N"

(*given a structure s we want to isolate and another structure s', where s is a subterm of s', 
this function will return a subterm of s' which has had the top most constructor removed. 
ie if s' = A ; Forw x B and s = B, partial_goal will return Forw x B*)
fun partial_goal :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin*) 
"partial_goal s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then l else r) | _ \<Rightarrow> l)" |
(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Action_Structure*) "partial_goal s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "partial_goal s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure*)*)
"partial_goal s x = x"

fun partial_goal_complement :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin*) 
"partial_goal_complement s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then r else l) | _ \<Rightarrow> r)" |
(*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Action_Structure*) "partial_goal_complement s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "partial_goal_complement s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure*)*)
"partial_goal_complement s x = x"


lemma partial_goal:
  fixes oper x y s
  shows "((partial_goal s (Structure_Bin x oper y)) = x) \<or> (partial_goal s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed

lemma partial_goal_complement:
  fixes oper x y s
  shows "((partial_goal_complement s (Structure_Bin x oper y)) = x) \<or> (partial_goal_complement s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) = x"
  by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed


lemma partial_goal_and_complement:
  fixes oper x y s
  defines "struct \<equiv> Structure_Bin x oper y"
  shows "( (partial_goal s struct) = x \<and> (partial_goal_complement s struct) = y ) \<or> 
         ( (partial_goal_complement s struct) = x \<and> (partial_goal s struct) = y )"
using struct_def
apply auto
apply (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))+
done

(*checks the polarity of a structure inside a sequent*)
fun position_in_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"position_in_Sequent s (Sequent l r) = (
  if s = l then -p
  else if (polarity_Structure s l) \<noteq> N then -p
  else if s = r then +p 
  else if (polarity_Structure s r) \<noteq> N then +p
  else N )" |
"position_in_Sequent s _ = N"


(*the following functions are used to create fresh names for an atprop, given a sequent. 
These functions are used by the ui for the display_tac tactic*)
fun fresh_name_aux :: "string list \<Rightarrow> string \<Rightarrow> string set \<Rightarrow> string" where
"fresh_name_aux [] s _ = s" |
"fresh_name_aux (x#xs) s full = (if (s@x) \<notin> full then s@x else (fresh_name_aux xs (s@x) full) )"


definition fresh_name :: "string list \<Rightarrow> string" where
"fresh_name list = fresh_name_aux list ''X'' (set list)"


fun collect_SFAtprop_names :: "Structure \<Rightarrow> string list" where
(*(*uncommentL?Structure_Formula?Formula_Atprop?Atprop*)  "collect_SFAtprop_names (Structure_Formula (Formula_Atprop (Atprop x))) = [x]" |(*uncommentR?Structure_Formula?Formula_Atprop?Atprop*)*)
(*(*uncommentL?Structure_Bin*) "collect_SFAtprop_names (Structure_Bin l oper r) = (collect_SFAtprop_names l) @ (collect_SFAtprop_names r)" | (*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Action_Structure*) "collect_SFAtprop_names (Structure_Action_Structure oper ac struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "collect_SFAtprop_names (Structure_Agent_Structure oper ag struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Agent_Structure*)*)
"collect_SFAtprop_names s = []"

fun replace_SFAtprop_into_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin*) "replace_SFAtprop_into_Structure sfa repl (Structure_Bin l oper r) = Structure_Bin (replace_SFAtprop_into_Structure sfa repl l) oper (replace_SFAtprop_into_Structure sfa repl r)" | (*uncommentR?Structure_Bin*)*)
(*(*uncommentL?Structure_Action_Structure*) "replace_SFAtprop_into_Structure sfa repl (Structure_Action_Structure oper ac struct) = Structure_Action_Structure oper ac (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Action_Structure*)*)
(*(*uncommentL?Structure_Agent_Structure*) "replace_SFAtprop_into_Structure sfa repl (Structure_Agent_Structure oper ag struct) = Structure_Agent_Structure oper ag (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Agent_Structure*)*)
"replace_SFAtprop_into_Structure sfa repl s = (if sfa = s then repl else s)"


fun replace_SFAtprop_into_Sequent :: "Structure \<Rightarrow> Structure \<Rightarrow> Sequent \<Rightarrow> Sequent" where
"replace_SFAtprop_into_Sequent sfa repl (Sequent l r) = Sequent (replace_SFAtprop_into_Structure sfa repl l) (replace_SFAtprop_into_Structure sfa repl r)" |
"replace_SFAtprop_into_Sequent sfa relp x = x"

fun replace_SFAtprop_into_PT :: "Structure \<Rightarrow> Structure \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replace_SFAtprop_into_PT sfa repl (Prooftree s r list) = (Prooftree (replace_SFAtprop_into_Sequent sfa repl s) r (map (replace_SFAtprop_into_PT sfa repl) list))"


fun sequent_fresh_name :: "Sequent \<Rightarrow> Structure" where
"sequent_fresh_name (Sequent l r) = (Structure_Formula (Formula_Atprop (Atprop (fresh_name ((collect_SFAtprop_names l)@(collect_SFAtprop_names r)) ))))" |
"sequent_fresh_name _ = (Structure_Formula (Formula_Atprop (Atprop ''X'')))"



export_code open der isProofTree ruleList displayRules ant consq rulifyProoftree replaceSequentIntoPT isProofTreeWithCut 
expandProoftree polarity_Sequent position_in_Sequent partial_goal partial_goal_complement sequent_fresh_name replace_SFAtprop_into_PT in Scala
module_name (*calc_name*) file (*export_path*)
end