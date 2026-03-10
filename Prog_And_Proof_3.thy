(*  Title:      Prog_And_Proof_3.thy
    Author:     AP
*)

section "Chapter 3"

theory Prog_And_Proof_3
  imports Main
begin

(* 3.1 *)
(* from 2.6 *)
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


(* new stuff *)
fun set_out_of_tree :: "'a tree \<Rightarrow> 'a set"
  where
  "set_out_of_tree Tip = {}"
| "set_out_of_tree (Node l a r) = {a} \<union> set_out_of_tree(l) \<union> set_out_of_tree(r)"  done

fun ls_tr :: "nat tree \<Rightarrow> nat tree \<Rightarrow> bool"
  where
  "ls_tr Tip y = True"
| "ls_tr y Tip = (if y = Tip then True else False)"
| "ls_tr (Node _ a1 _) (Node _ a2 _) =  (if a1 \<le> a2 then True else False)"

fun is_ord :: "nat tree \<Rightarrow> bool"
  where
  "is_ord Tip = True"
| "is_ord (Node l a r) = ((ls_tr l r) \<and> (is_ord l) \<and> (is_ord r))"

fun contains :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool"
  where
  "contains x Tip = False"|
  "contains x (Node l a r) = (if x = a then True else (contains x l)\<or>(contains x r))"

fun ins1 :: "nat \<Rightarrow> nat tree \<Rightarrow> nat tree"
  where 
  "ins1 n Tip = (Node Tip n  Tip)"
| "ins1 n (Node Tip a Tip) = (if n > a then (Node Tip a (Node Tip n Tip)) else (if n < a then (Node Tip n (Node Tip a Tip)) else (Node Tip a Tip)))"
| "ins1 n (Node l a r) = (if n < a then (Node (ins1 n l) a r) else (if n>a then (Node l a (ins1 n r)) else (Node l a r)))"

fun ins1_lst :: "nat list \<Rightarrow> nat tree"
  where 
  "ins1_lst [] = Tip"
| "ins1_lst (x#xs) = ins1 x (ins1_lst xs)"

value "ins1_lst [2,0,1]"
value "is_ord (ins1_lst [1,2,4,2,6,1,7,4,9])"

lemma preserve_ord: "is_ord x \<Longrightarrow> is_ord (ins1 n x)"



end