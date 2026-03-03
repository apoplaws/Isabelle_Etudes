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
     
  
end