-- A --

--1 (Theorem add_right_cancel: a+n=b+n⟹a=b.)
/-
induction n with k hi
intro h
rw[add_zero,add_zero] at h
exact h
intro h2
rw[add_succ,add_succ] at h2
apply succ_inj at h2
apply hi at h2
exact h2
-/

--2 (Theorem add_left_cancel: n+a=n+b⟹a=b.)
/-
intro h
rw[add_comm,add_comm n b] at h
apply add_right_cancel at h
exact h
-/

--3 (Theorem add_left_eq_self: x+y=y⟹x=0.)
/-
intro h
nth_rewrite 2 [← zero_add y] at h
apply add_right_cancel at h
exact h
-/

--4 (Theorem add_right_eq_self: x+y=x⟹y=0.)
/-
intro h
nth_rewrite 2 [← add_zero x] at h
apply add_left_cancel at h
exact h
-/

--5 (Theorem add_right_eq_zero: If a+b=0 then a=0.)
/-
cases b with k
intro h1
rw[add_zero] at h1
exact h1
intro h2
rw[add_succ] at h2
symm at h2
cases zero_ne_succ (a + k) h2
-/

--6 (Theorem add_left_eq_zero: If a+b=0 then b=0.)
/-
cases a with k
intro h
rw[zero_add] at h
exact h
intro h
rw[succ_add] at h
symm at h
cases zero_ne_succ (k+b) h
-/
