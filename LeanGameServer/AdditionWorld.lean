-- ADDITION WORLD --

--1(Theorem zero_add: For all natural numbers n, we have 0+n=n.)
/-
  induction n
  rw[add_zero]
  rfl
  rw[add_succ]
  rw[n_ih]
  rfl
-/

--2 (Theorem succ_add: For all natural numbers a,b, we have succ(a)+b=succ(a+b))
/-
  induction b with a
  rw[add_zero,add_zero]
  rfl
  rw[add_succ,n_ih,add_succ]
  rfl
-/

--3 (Theorem add_comm: On the set of natural numbers, addition is commutative. In other words, if a and b are arbitrary natural numbers, then a+b=b+a.)
/-
  induction b with a
  rw[add_zero,zero_add]
  rfl
  rw[add_succ,succ_add,n_ih]
  rfl
-/

--4 (Theorem add_assoc: On the set of natural numbers, addition is associative. In other words,
--if a,b and c are arbitrary natural numbers, we have (a+b)+c=a+(b+c).)
/-
  induction c with a b
  rw[add_zero,add_zero]
  rfl
  rw[add_succ,b,← add_succ,← add_succ]
  rfl
-/

--***5 (Theorem add_right_comm: If a,b and c are arbitrary natural numbers, we have (a+b)+c=(a+c)+b)
/-
  induction c with k hi
  rw[add_zero,add_zero]
  rfl
  rw[add_succ,add_succ,succ_add,hi]
  rfl
-/
