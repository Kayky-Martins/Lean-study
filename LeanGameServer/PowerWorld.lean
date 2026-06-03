-- POWER WORLD --

--1 (Theorem zero_pow_zero: 0^0=1)
/-
  rw[pow_zero]
  rfl
-/

--2 (Theorem zero_pow_succ: For all numbers m, 0^succ(m)=0.)
/-
  rw[pow_succ,mul_zero]
  rfl
-/

--3 (Theorem pow_one: For all naturals a, a^1=a)
/-
  rw[one_eq_succ_zero,pow_succ,pow_zero,one_mul]
  rfl
-/

--4 (Theorem one_pow: For all naturals m, 1^m=1)
/-
  induction m with k hi
  rw[pow_zero]
  rfl
  rw[pow_succ,hi,mul_one]
  rfl
-/

--5 (Theorem pow_two: For all naturals a, a^2=axa)
/-
  rw[two_eq_succ_one,pow_succ,pow_one]
  rfl

-/

--6 (Theorem pow_add: For all naturals a, m, n, we have a^(m+n)=a^m a^n)
/-
  induction n with k hi
  rw[add_zero,pow_zero,mul_one]
  rfl
  rw[add_succ,pow_succ,hi,pow_succ,mul_assoc]
  rfl
-/

--**7 (Theorem mul_pow: For all naturals a, b, n, we have (ab)^n = a^n b^n .)
/-
  induction n with k hi
  rw[pow_zero,pow_zero,pow_zero,mul_one]
  rfl
  rw[pow_succ,hi,pow_succ,pow_succ]
  rw [← mul_assoc (a ^ k * b ^ k) a b]
  rw [mul_assoc (a ^ k) (b ^ k) a]
  rw [mul_comm (b ^ k) a]
  rw[← mul_assoc (a^k) a (b^k)]
  rw [← mul_assoc (a ^ k * a) (b ^ k) b]
  rfl
-/

--8 (Theorem pow_pow: For all naturals a, m, n, we have (a^m)^n=a^mn)
/-
  induction n with k hi
  rw[pow_zero,mul_zero,pow_zero]
  rfl
  rw[pow_succ,mul_succ,hi,pow_add]
  rfl
-/

--9 (Theorem add_sq: For all numbers a and b, we have (a+b) ^2=a^2 +b^2+2ab)
/-
  rw[two_eq_succ_one,pow_succ,pow_succ,pow_succ]
  rw[pow_one,pow_one,pow_one,succ_mul,one_mul]
  rw[← two_mul]
  rw[add_mul,mul_add,mul_add]
  rw[mul_comm b a,add_comm (a*b) (b*b)]
  rw [add_assoc (a * a) (a * b) (b * b + a * b)]
  rw [← add_assoc (a * b) (b * b) (a * b)]
  rw[add_comm (a*b) (b*b)]
  rw [← add_assoc (a * a) (b * b + a * b) (a * b)]--opa
  rw [← add_assoc (a * a) (b * b) (a * b)]
  rw [add_assoc (a * a + b * b) (a * b) (a * b)]
  rw [← two_mul (a * b)]
  rw [mul_assoc 2 a b]
  rfl
-/
