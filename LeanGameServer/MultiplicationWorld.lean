-- MULTIPLICATION WORLD --

--1 (Theorem mul_one: For any natural number m, we have m×1=m.)
/-
  rw[one_eq_succ_zero,mul_succ,mul_zero,zero_add]
  rfl
-/

--2 (Theorem zero_mul: For all natural numbers m, we have 0×m=0.)
/-
  induction m
  rw[mul_zero]
  rfl
  rw[mul_succ,n_ih,add_zero]
  rfl
-/

--**3 (Theorem succ_mul: For all natural numbers a and b, we have (succ a)×b=a×b+b.)
/-
  induction b with k hi
  rw[mul_zero,mul_zero,add_zero]
  rfl
  rw[mul_succ,hi,mul_succ,add_assoc,add_assoc,add_succ k a,add_succ a k]
  rw[add_comm k a]
  rfl
-/

--4 (Theorem mul_comm: Multiplication is commutative.)
/-
  induction b with k hi
  rw[mul_zero,zero_mul]
  rfl
  rw[mul_succ,succ_mul,hi]
  rfl
-/

--5 (Theorem one_mul: For any natural number m, we have 1×m=m.)
/-
  rw[mul_comm,mul_one]
  rfl
-/

--6 (Theorem two_mul: For any natural number m, we have 2×m=m+m.)
/-
  induction m with k hi
  rw[mul_zero,add_zero]
  rfl
  rw[mul_succ,add_succ,succ_add,← hi,succ_eq_add_one,succ_eq_add_one,add_assoc,← succ_eq_add_one,← two_eq_succ_one]
  rfl
-/

--7 (Theorem mul_add: Multiplication is distributive over addition on the left. In other words, for all natural numbers a, b and c, we have a(b+c)=ab+ac.)
/-
  induction c with k hi
  rw[add_zero,mul_zero,add_zero]
  rfl
  rw[add_succ,mul_succ,hi,mul_succ,add_assoc]
  rfl
-/

--8 (Theorem add_mul: Addition is distributive over multiplication. In other words, for all natural numbers a, b and c, we have (a+b)×c=ac+bc.)
/-
  rw[mul_comm,mul_add,mul_comm,mul_comm c b]
  rfl
-/

--9 (Theorem mul_assoc: Multiplication is associative. In other words, for all natural numbers a, b and c, we have (ab)c=a(bc).)
/-
  induction c with k hi
  rw[mul_zero,mul_zero,mul_zero]
  rfl
  rw[mul_succ,hi,mul_succ,mul_add]
  rfl
-/
