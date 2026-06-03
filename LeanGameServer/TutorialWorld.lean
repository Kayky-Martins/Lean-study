-- TUTORIAL WORLD --

--3(Provar que 2 = succ(succ 0))
/-
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rfl
-/

--4(2 is the number after the number after 0)
/-
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]
  rfl
-/

--5(a+(b+0)+(c+0)=a+b+c)
/-
  rw[add_zero,add_zero]
  rfl
-/

--7 (Theorem succ_eq_add_one: For all natural numbers a, we have succ(a)=a+1)
/-
  rw[one_eq_succ_zero]
  rw[add_succ,add_zero]
  rfl
-/

--8 (2+2=4.)
/-
  rw[four_eq_succ_three]
  nth_rewrite 2 [two_eq_succ_one]
  rw[add_succ]
  rw[one_eq_succ_zero,add_succ,add_zero]
  rw[two_eq_succ_one]
  rw[three_eq_succ_two,two_eq_succ_one]
  rfl
-/
