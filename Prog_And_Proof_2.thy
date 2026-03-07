(*  Title:      Prog_And_Proof_2.thy
    Author:     AP
*)

section "Chapter 2"

theory Prog_And_Proof_2
  imports Main
begin
(* 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)" 
value "1 - (2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
where 
  "add 0 n = n" 
| "add (Suc m) n = Suc(add m n)"

(* assoc *)
lemma add_assoc: "add (add m n) k = add m (add n k)"
  by (induct m) simp_all
  
lemma add_0: "add m 0 = m"
  by (induct m) simp_all

lemma zero_add: "m = add m 0"
  by (induct m) simp_all

lemma add_succ: "add m (Suc n) = Suc (add m n)"
  by (induct m)
  simp_all

(* comm *)
lemma add_com: "add m n = add n m"
  apply (induct_tac m)
  apply (simp_all)
  apply (rule sym)
  apply (rule add_0)
  apply (subst add_succ)
  apply (simp_all)
  done

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
"count x [] = 0"
|"count x (y # xs) = (count x xs) + (if x = y then 1 else 0)"

lemma count_not_increase: "count a (y#xs) \<le> (count a xs)+1"
  apply(induct xs)
  apply(auto)
  done

lemma nomore_as: "count a l \<le> length l" 
  apply(induct_tac l)
  apply(auto)
  done

(* 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where
"snoc [] a = [a]"
|"snoc (x # xs) a = x # (snoc xs a)"

fun rev_s :: "'a list \<Rightarrow> 'a list"
  where 
"rev_s [] = []"
|"rev_s (x # xs) = snoc (rev_s xs) x"

lemma rev_prop : "snoc (rev_s xs) x = rev_s (x # xs)"
  apply(auto)
  done 

lemma rev_lead: "rev_s (snoc xs a) = a# (rev_s xs)"
  apply(induct_tac xs)
  apply(unfold snoc.simps, unfold rev_s.simps, unfold snoc.simps)
  apply(rule refl)
  
  subgoal premises pr
    apply (subst pr(1))
    apply (unfold snoc.simps)
    apply (rule refl)
    done
  done

value "rev_s (rev_s [(1::nat), 2, 3])"

lemma rev_rev_by_snoc: "rev_s (rev_s xs) = xs"
  apply (induct_tac xs)
  apply (simp)
  apply(drule sym)
  subgoal premises p
    apply(subst (2) p(1))
    apply(unfold rev_s.simps)
    apply(rule rev_lead)
    done
  done


(* 2.5 *)
ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name nat} |> Option.map #ctrs\<close>

fun sum_up_to_n :: "nat \<Rightarrow> nat"
  where
  "sum_up_to_n 0 = 0"
| "sum_up_to_n (Nat.Suc n) = n + 1 + (sum_up_to_n n)"

value "sum_up_to_n 3"

lemma sum_sub: "sum_up_to_n n = (n * (n + 1)) div 2"
  apply (induct_tac n, simp)
  apply(unfold sum_up_to_n.simps)
  subgoal premises p
    apply(subst p(1), simp)
    done
  done

(* 2.6 *)
datatype 'a tree = Tip | Node " 'a tree" 'a " 'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree"
  where 
    "mirror Tip = Tip" | 
    "mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t" 
  apply(induction t rule: mirror.induct)  
   apply(auto)
  done 

fun contents :: "'a tree \<Rightarrow> 'a list"
  where
  "contents Tip = []"|
  "contents (Node l a r) = (contents l) @ [a] @ (contents r)"

definition sum_tree :: "nat tree \<Rightarrow> nat"
  where
  "sum_tree x = sum_list (contents x)"

value "sum_tree (Node (Node Tip 2 Tip) 1 Tip)"

(* 2.7 *)
fun preorder_grab :: "'a tree \<Rightarrow> 'a list"
  where 
  "preorder_grab Tip = []"|
  "preorder_grab (Node l a r) = a#preorder_grab(l)@preorder_grab(r)"

fun postorder_grab :: "'a tree \<Rightarrow> 'a list"
  where 
  "postorder_grab Tip = []"|
  "postorder_grab (Node l a r) = postorder_grab(l)@postorder_grab(r)@[a]"


lemma preordmir: "preorder_grab(mirror t) = rev (postorder_grab t)"
  apply(induct_tac t)
  (* works well apply(auto)*)
   apply(simp)
  subgoal premises pf
    apply(unfold mirror.simps, unfold preorder_grab.simps)
    apply(unfold postorder_grab.simps)
    apply(subst pf(2), subst pf(1))
    apply(simp)
  done
  done
(* 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where 
  "intersperse a [] = []"|
  "intersperse a (x#xs) = [x, a]@(intersperse a xs)"

lemma map_nat : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
   apply( induct_tac xs)
   apply( simp)
  subgoal premises pf
    apply (unfold intersperse.simps)
    apply(simp add: map_def )
    apply(rule pf(1))
    done
  done

(* 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
"itadd 0 n = n"|
"itadd (Suc m) n = itadd m (Suc n)"

lemma add_eq_itadd : "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply(unfold itadd.simps)
   apply(unfold add.simps)
   apply(rule refl)
  subgoal premises ps
    (*add m (Suc n) = Suc (add m n)*)
    (*apply(subst add_succ [where m="m" and n="(Suc n)"])*)
    apply(subst add_succ [symmetric])
    apply(rule ps(1))
    done
  done

(* 2.10 *)
datatype tree0 = Elf | Nd tree0 tree0

fun all_nodes :: "tree0 \<Rightarrow> nat"
  where 
"all_nodes Elf = 1"|
"all_nodes (Nd t s) = 1+(all_nodes t)+(all_nodes s)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0"
  where 
"explode 0 t = t"|
"explode (Suc n) t = explode n (Nd t t)"

value "all_nodes(explode 3 (Nd Elf Elf))"
value "(2::nat)^3"

lemma double : "a + a = (2::nat)*a"
  apply(induction a)
   apply(auto)
  done
  

lemma explode_form : "all_nodes( explode n t) = (((2::nat)^(n))-1)+((2::nat)^n)*(all_nodes t)"
  apply(induction n arbitrary: t)
   apply(simp)[1]
  apply (unfold explode.simps)
  subgoal premises ps  
    apply(subst ps(1))
    apply(subst all_nodes.simps)
    apply(subst  Power.monoid_mult_class.power_Suc2)
    apply(subst add.assoc)
    apply(subst double)
    apply(subst add_mult_distrib2)
    apply(auto)
    done
  done


  (* apply (subst all_nodes.simps [where s="t" ] )*)

(* 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int"
  where
"eval Var n = n"|
"eval (Const c) n = c"|
"eval (Add exp1 exp2) n = (eval exp1 n)+(eval exp2 n)"|
"eval (Mult exp1 exp2) n = (eval exp1 n)*(eval exp2 n)"


fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int"
  where
"evalp [] n = 0"|
"evalp (x#xs) n = x + n*evalp xs n"

fun add_long :: "int list \<Rightarrow> int list \<Rightarrow> int list"
  where 
"add_long [] ys = ys"|
"add_long xs [] = xs"|
"add_long (x#xs) (y#ys) = (x+y)#add_long xs ys"

lemma add_long_add : "evalp (add_long x y) n = (evalp x n) + (evalp y n)"
  apply(induction x y rule: add_long.induct)
    apply (unfold add_long.simps, unfold evalp.simps, simp)
  apply(simp)
  subgoal premises ps
    apply(subst ps)
    apply(simp add:algebra_simps)
    done
  done
    
  

value "add_long [1,2,3] [1,3,4,5,6]"

fun del_lead_zero :: "int list \<Rightarrow> int list"
where 
"del_lead_zero [] = []"|
"del_lead_zero (x#xs) = (if x=0 then (del_lead_zero xs) else (x#xs))"

fun del_trial_zero :: "int list \<Rightarrow> int list"
  where 
"del_trial_zero xs = rev(del_lead_zero(rev xs))"

fun mul_long :: "int list \<Rightarrow> int list \<Rightarrow> int list"
  where
"mul_long [] ys = []"|
"mul_long xs [] = []"|
"mul_long (x#xs) ys = add_long (map (\<lambda>t. x*t) ys) (mul_long xs (0#ys))"

lemma mul_long_mul: "evalp (mul_long xs ys) n = (evalp xs n)*(evalp ys n)"
  (*apply(induction xs ys rule: mul_long.induct)*)
  apply (induction xs arbitrary: ys)
    apply(unfold mul_long.simps, unfold evalp.simps, simp)
  subgoal premises ps
    apply (subst mul_long.simps)

value "mul_long [0,1] [1,31]"


fun coeffs :: "exp \<Rightarrow> int list"
  where
"coeffs (Const c) = [c]"|
"coeffs Var = [0,1]"|
"coeffs (Add x1 x2) = add_long (coeffs x1) (coeffs x2)"|
"coeffs (Mult x1 x2) = mul_long (coeffs x1) (coeffs x2)"

fun nth_power :: "exp \<Rightarrow> nat \<Rightarrow> exp"
  where
"nth_power x 0 = Const 1"|
"nth_power x (Suc n) = Mult x (nth_power x n)"

value "coeffs (nth_power (Add Var (Const 1)) 10)"


fun aux_gen :: "nat \<Rightarrow> nat list"
  where
  "aux_gen 0 = [0]"|
  "aux_gen (Suc n) = (Suc n)#(aux_gen n)"

fun gen :: "nat \<Rightarrow> nat list"
  where
  "gen n = rev (aux_gen n)"

value "gen 4"
value "zip [1::nat, 2] (gen 1)"

value "foldl (+) 0 [0::nat,1]"
value "foldl (\<lambda>x y. (Add x y)) (Const 0) [Var]"

definition decoeff_1 :: "int list \<Rightarrow> exp"
  where
  "decoeff_1 pol = 
    foldl (\<lambda>x y. (Add x y)) (Const 0) 
      (map (\<lambda> p. Mult (Const (fst p)) (nth_power Var (snd p))) 
        (zip pol (gen (length pol))))"

value "decoeff_1 (coeffs (nth_power (Add (Const 1) Var) 5))"

fun decoeff_2 :: "int list \<Rightarrow> exp"
  where
  "decoeff_2 [] = Const 0"|
  "decoeff_2 (x#xs) = (if x = 0 then Mult Var (decoeff_2 xs) 
      else Add (Const x) (Mult Var (decoeff_2 xs)))"

value "decoeff_2 (coeffs (nth_power (Add (Const 1) Var) 5))"

theorem equiv_of_repr : "evalp (coeffs e) x = eval e x"
  apply (induction e)
     apply (unfold coeffs.simps)[1]
     apply (unfold evalp.simps, unfold eval.simps)[1]
  apply( simp)
     apply (unfold coeffs.simps)[1]
    apply (unfold evalp.simps, unfold eval.simps)[1]
    apply(simp)
  subgoal premises ps
    apply (unfold eval.simps)
end