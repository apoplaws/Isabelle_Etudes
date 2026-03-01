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
  apply (induction m)
  apply (simp_all)
  apply (rule sym)
  apply (rule add_0)
  apply (unfold atomize_imp)
  apply (unfold atomize_all)
  apply (intro)



  (*apply(induction n)
  apply(simp_all)*)
  
   
end