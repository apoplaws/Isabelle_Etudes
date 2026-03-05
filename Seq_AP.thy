(*  Title:      HOL/Examples/Seq.thy
    Author:     Makarius
*)

section \<open>Finite sequences\<close>

theory Seq_AP
  imports Main
begin

datatype 'a seq = Empty | Seq 'a "'a seq"

datatype ('a, 'b) coprod = L 'a| R 'b

datatype xing = Xing

type_synonym 'a possibly = "('a, xing) coprod"


fun conc :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq"
where
  "conc Empty ys = ys"
| "conc (Seq x xs) ys = Seq x (conc xs ys)"

fun reverse :: "'a seq \<Rightarrow> 'a seq"
where
  "reverse Empty = Empty"
| "reverse (Seq x xs) = conc (reverse xs) (Seq x Empty)"

fun make_seq :: "'a \<Rightarrow> 'a seq"
where
  "make_seq x = Seq x Empty"

fun head :: "'a seq \<Rightarrow> 'a possibly"
where
  "head Empty = R Xing"
| "head (Seq x xs) = L x"

fun tail :: "'a seq \<Rightarrow> 'a seq"
where
  "tail Empty = Empty"
| "tail (Seq _ xs) = xs"

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a seq \<Rightarrow> 'b seq"
where
  "map f Empty = Empty"
| "map f (Seq x xs) = Seq (f x) (map f xs)"

lemma conc_empty: "conc xs Empty = xs"
  by (induct xs) simp_all

lemma conc_assoc: "conc (conc xs ys) zs = conc xs (conc ys zs)"
  by (induct xs) simp_all

lemma reverse_conc: "reverse (conc xs ys) = conc (reverse ys) (reverse xs)"
  by (induct xs) (simp_all add: conc_empty conc_assoc)

lemma reverse_reverse: "reverse (reverse xs) = xs"
  by (induct xs) (simp_all add: reverse_conc)

end
