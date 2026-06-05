import MIL.Common

/- LEANFICATION_Reunião 4: Introdução à Prova por Táticas-/

/- Seção 1 : Comandos Básicos -/

/- 1.1: Tática "rlf" (reflexivity)
   Prova objetivos da forma X = X
-/

example (a b : ℕ) : 37*a + b = 37*a + b := by
 rfl

/- 1.2: Tática rw (rewrite)
  Se ha é uma prova que a = b, então rw [ha] muda o objetivo de a para b, equivalente a substituir
-/

example (a b : ℕ) (h : b = a + 3) : 3 * b = 3 * (a + 3) := by
 rw [h]

/- 1.3: Rewrite backwards (digita-se "\" + "l"),
  Podemos usar o rw de trás pra frente.
  Se temos uma hipótese ha a = b,
  e queremos provar que uma expressão de b equivale a uma em função de a, podemos usar
  rw [← ha] deixando a expressão em função de a
-/

example (a b : ℕ) (h : b = a + 3) : 3*b = 3*(a + 3) := by
 rw [← h]

/- 1.4: Nth rewrite
 Especifica qual a ocorrência de rw você deseja realizar
-/

example (a b : ℕ) (h : a = b) : 3*a + a = 3*a + b := by
 nth_rewrite 2 [h]
 rfl


/- 1.5: zero_add , add_comm , add_assoc
 zero_add: Prova de que 0 + a = a
 add_zero: Prova de que a + 0 = a
 add_comm: Comutação da adição : Prova de que a + b = b + a
 add_assoc: Associação da adição : Prova de que (a + b) + c = a + (b + c).
 -/

example (a : Nat) : 0 + a = a := by
  rw [zero_add]

example (a b : Nat) : a + b = b + a := by
  rw [add_comm]

example (a b c : Nat) : a + (b + c) = (a + b) + c := by
  rw [add_assoc]

/- Exercícios Seção 1-/
/- Obs: comutação e associação com multiplicação:
   mul_assoc : Prova de (a * b) * c = a * (b * c)
   mul_comm : Prova de a * b = b * a
   mul_add : Prova de a * (b + c) = a * b + a * c.
-/

example (a b c d : ℕ) (ha : a = b + c) : d * a =  d * c + d * b := by
 rw[ha,mul_add,add_comm]

example (a b c d e f : ℕ) (h1 : a * b = c * d) (h2 : e = f) : a * (b * e) = c * (d * f) := by
 rw[← mul_assoc,h1,h2,mul_assoc]

example (a b c : ℕ) : a * b + c * (a + b) = b * a + c * b + c * a := by
 rw[mul_comm,mul_add,add_comm (c*a) (c*b),← add_assoc]

example (p q r s t u : ℕ) (h1 : p * q = s) (h2 : p * r = t) (h3 : s + t = u) : p * (r + q) = u := by
 rw[mul_add,h2,h1,add_comm,h3]
/- Obs: Você pode usar rw em sua hipótese com "rw [...] at h"-/

/- Seção 2 : Táticas: induction, apply , exact , intro -/

/- 2.1: Tática Induction
 Se o objetivo menciona n, então com "induction n with d hd"
 tentamos provar o objetivo por indução em n, com a variável indutiva no caso sucessor sendo d,
 e a hipótese indutiva sendo hd
-/

example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
   rw [add_zero]
   /- Caso Base
   após escrever "0 + 0 = 0" como "0 = 0" o lean usa sozinho "rfl"
   outra maneira de resolver seria usando apenas "rfl", então o lean
   usaria sozinho "zero_add"
   -/
  | succ d dh =>
   /- Passo Indutivo
   O lean automaticamente escreve "succ d" como "d + 1",
   portanto, basta usar "zero_add"
   -/
    rw [zero_add]

example (m n : ℕ) : m + n = n + m := by
  induction n with
  | zero =>
    rw [add_zero]
    rw [zero_add]
  | succ d hd =>
    rw [Nat.add_succ]
    rw [hd]
    rw [Nat.succ_add]

/- 2.2: Tática Exact
Se o objetivo é um expressão P, então "exact h" vai completar
o objetivo se a hipótese h é uma prova de P
-/

example (a b : ℕ) (h1 : a + b = 37) : a + b = 37 := by
 exact h1

/- 2.3: Tática apply
Se "t : P → Q" é uma prova de  P⟹Q, e "h : P" é prova de P,
então "apply t at h" muda para uma prova de Q.  Modus Ponens
-/

example (a b : ℕ) (h1 : a = 36) (h2 : a = 36 → b = 63) : b = 63 := by
 apply h2 at h1
 exact h1

/- 2.4: Tática intro
Se o objetivo é uma implicação P → Q, então "intro h" introduz h como ua hipótese "h : P"
e o objetivo agora será provar Q. Basicamente, assume-se P para provar Q
-/

example (a : ℕ) : a = 369 -> a = 369 := by
 intro h
 exact h

/- Exercícios Seção 2 -/
/- Teoremas nescessários:
"mul_zero" e "zero_mul" : "a * 0 = 0" e "0 * a = 0"
"Nat.mul_succ" e "Nat.succ_mul" : "a * (b + 1) = a * b + a" e " (a + 1) * b = b * a + b"
"symm" tranforma "a = b" em "b = a"
"zero_ne_one" Prova que 0 = 1 é falso.
-/

example (a b : ℕ) (h : 0 + a = 0 + b + 2) : a = b + 2 := by
 rw[zero_add,zero_add] at h
 exact h

example (a b c d : ℕ) : (a + b = c) → (a + (b + d) = c + d) := by
 intro h
 rw[← add_assoc,h]

example (c d : ℕ) : c * d = d * c := by
 induction d with
 | zero =>
  rw[mul_zero,zero_mul]
 | succ d hd =>
  rw[mul_add,add_mul,mul_one,one_mul,mul_comm]

/- Resolva sem usar mul_comm-/

example : 1 ≠ 0 := by
 intro h
 contradiction
/- Pode-se supor por contradição que 1 = 0 com "intro h"-/

example (a n : ℕ) : a = 0 → a * n = 0 := by
 intro h
 rw[h,zero_mul]
/- Seção 3: Tática Cases e teoremas de adição -/

/- 3.1: Tática Cases:
 Se n é um número, então "cases n with d" irá separar o objetivo em dois,
 um com "n = 0" e outro com "n = succ d"
 Note que a tática cases é como a induction sem uma hipótese de indução
-/

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with
  | zero =>
    rw [add_zero]
    intro h
    exact h
  | succ d =>
    rw [Nat.add_succ]
    intro h
    contradiction

theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
 rw[add_comm]
 apply add_right_eq_zero

/- Exercícios Seção 3 -/

theorem questao_add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
 intro h
 rw[add_comm a n, add_comm b n] at h
  -- Agora h diz: n + a = n + b
  -- Usamos o teorema padrão de cancelamento à esquerda que já vem no Lean 4:
 exact Nat.add_left_cancel h



theorem questao_add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
 intro h
 rw[add_comm,add_comm n b] at h
 apply questao_add_right_cancel at h
 exact h

theorem questao_add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
 intro h
 nth_rewrite 2[← zero_add y] at h
 apply add_right_cancel at h
 exact h

--**
theorem quadrado_zero (n : ℕ) : n * n = 0 → n = 0 := by
 intro h
 cases n with
  | zero =>
    rw[mul_zero] at h
  | succ k =>
    contradiction
