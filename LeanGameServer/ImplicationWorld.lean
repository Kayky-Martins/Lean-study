-- IMPLICATION WORLD --

--2 (Assuming 0+x=(0+y)+2, we have x=y+2.)
/-
  rw[zero_add,zero_add] at h
  exact h
-/

--3 (If x=37 and we know that x=37⟹y=42 then we can deduce y=42.)
/-
  apply h2 at h1
  exact h1
-/

--**4 (If x+1=4 then x=3.)
/-
  rw[four_eq_succ_three] at h
  rw[← succ_eq_add_one] at h
  apply succ_inj at h
  exact h
-/

--**5 (If x+1=4 then x=3, agora manipulando x=3)
/-
  apply succ_inj
  rw[succ_eq_add_one,← four_eq_succ_three]
  exact h
-/

--6 (x=37⟹x=37.)
/-
  intro h
  apply h
-/

--**7 (x+1=y+1⟹x=y.)
/-
  intro h
  rw[← succ_eq_add_one x] at h
  rw[← succ_eq_add_one y] at h
  apply succ_inj at h
  exact h
-/

--**8 (If x=y and x!=y then we can deduce a contradiction.)
/-
  exact h2 h1
-/

--9 (Theorem zero_ne_one: 0!=1.)
/-
  intro h
  rw[one_eq_succ_zero] at h
  apply zero_ne_succ at h
  exact h
-/

--**10 (Theorem one_ne_zero: 1!=0.)
/-
  intro h
  symm at h
  apply zero_ne_one at h
  exact h
-/

--11 (2+2!=5.)
/-
  intro h
  rw [add_succ,add_succ,add_zero] at h
  apply succ_inj at h
  apply succ_inj at h
  apply succ_inj at h
  apply succ_inj at h
  apply zero_ne_succ at h
  exact h
-/
