theory (*calc_name_se*)
imports Main (*calc_name_core_se*)
begin

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
                  Empty


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_ForwA _ s) = is_act_mod s"|
"is_act_mod (Structure_BackA _ s) = is_act_mod s"|

"is_act_mod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula*)*)

(*calc_structure_rules_se*)

end