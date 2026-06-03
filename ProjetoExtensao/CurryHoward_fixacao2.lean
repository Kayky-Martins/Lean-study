theorem trans_exemplo (P Q R : Prop) (f : P → Q) (g : Q → R) : P → R := by
  intro x
  let y := f x
  exact g y

-- EXERCÍCIO 1: A Identidade (O teorema mais simples possível)
-- Lógica: Se P é verdade, então P é verdade.
-- Curry-Howard: Uma função que recebe um P e devolve o próprio P (a função identidade).
theorem ex1 (P : Prop) : P → P := by
  intro PP
  exact PP

-- EXERCÍCIO 2: Troca de Argumentos (Comutatividade da Implicação)
-- Lógica: Se "P implica que Q implica R", então "Q implica que P implica R".
-- Curry-Howard: Uma função que recebe dois argumentos e apenas muda a ordem de entrada deles.
theorem ex2 (P Q R : Prop) (f : P → Q → R) : Q → P → R :=
  fun (pq:Q) (pp:P)=> f pp pq

-- EXERCÍCIO 3: Introdução da Conjunção (O conectivo "E")
-- Lógica: Se temos P e temos Q, então temos "P e Q".
-- Curry-Howard: Construir um par ordenado (tupla) contendo uma prova de P e uma de Q.
-- Dica: Use a tática `constructor` para quebrar o objetivo `P ∧ Q` em dois sub-objetivos.
theorem ex3 (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
  ⟨p,q⟩

-- EXERCÍCIO 4: Eliminação da Conjunção (Projeção)
-- Lógica: Se sabemos que "P e Q" é verdade, então P é verdade.
-- Curry-Howard: Extrair o primeiro elemento de um par ordenado.
-- Dica: Se `h : P ∧ Q`, você pode extrair as partes usando `let hp := h.left` ou `let hp := h.1`.
theorem ex4 (P Q : Prop) (h : P ∧ Q) : P :=
  h.left

-- EXERCÍCIO 5: Introdução da Disjunção (O conectivo "OU")
-- Lógica: Se P é verdade, então "P ou Q" é verdade (independente de quem seja Q).
-- Curry-Howard: Injetar um valor em um tipo de união pela esquerda.
-- Dica: Use a tática `left` para dizer ao Lean que você vai provar o lado esquerdo do `∨`.
theorem ex5 (P Q : Prop) (p : P) : P ∨ Q :=
  Or.inl p
