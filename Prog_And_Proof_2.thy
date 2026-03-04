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

value "explode 6 (Nd Elf Elf)"

end