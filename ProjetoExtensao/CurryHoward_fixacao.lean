-- Aula02.lean: Exercícios de Fixação (Tipos Compostos e Limites)
variable {α β χ η : Type}

---
-- EXERCÍCIO 1: Distribuição do Produto sobre a Soma
-- Dica: Você recebe um par onde o primeiro elemento é um 'α'
-- e o segundo é uma escolha entre 'β ⊕ χ'. Devolva uma escolha entre dois pares.
example (p : α × (β ⊕ χ)) : (α × β) ⊕ (α × χ) :=
  p.2.elim
    (fun b =>Sum.inl (p.1,b))
    (fun c =>Sum.inr (p.1,c))

-- EXERCÍCIO 2: O Tipo Unitário Trivial
-- Dica: Qualquer tipo pode gerar uma função para 'Unit'. Basta ignorar
-- o argumento de entrada e usar o construtor canônico do Módulo 4.
example (f : α → β) : α × Unit → β × Unit :=
  fun p => (f (p.1),())


---
-- EXERCÍCIO 3: Eliminação de Soma com Alvos Diferentes
-- Dica: Você tem duas opções de entrada (sum). Se vier da esquerda,
-- aplique 'f' e injete na esquerda do resultado. Se vier da direita,
-- aplique 'g' e injete na direita do resultado.
example (f : α → χ) (g : β → η) (sum : α ⊕ β) : χ ⊕ η :=
  sum.elim
    (fun a => Sum.inl (f a))
    (fun b => Sum.inr (g b))

---
-- EXERCÍCIO 4: Contradição interna (Explosão)
-- Dica: Uma das opções da sua soma da esquerda te dá uma função 'α → Empty'.
-- Se você combinar isso com o par da direita (que te dá um 'α'), você gera um 'Empty'.
example (sum : (α → Empty) ⊕ β) (p : α × χ) : β ⊕ η :=
  sum.elim
    (fun a => (a p.1).elim)
    (fun b => Sum.inl b)

---
-- EXERCÍCIO 5: Alta Ordem com Produto e Empty (O Desafio Final)
-- Dica: Olhe para as portarias e escopos. A meta pede uma função.
-- O argumento 'h' espera receber um par. Cuidado com os parênteses!
example (h : (α × β) → Empty) : α → β → Empty :=
  fun a => fun b => h ((a,b))

-----------------------------------------------------------------------------------------------------------
variable {p q r s : Prop}

---
-- EXERCÍCIO 6: Transitividade da Implicação (Modus Ponens em Cadeia)
-- Hipóteses: 'p' implica 'q', e 'q' implica 'r'.
-- Meta: Se eu te der um 'p', você consegue me entregar um 'r'?
-- Dica: Abra a portaria para receber o 'p' e vá aplicando as funções.
theorem transatividade (hpq : p → q) (hqr : q → r) : p → r :=
  fun pp => hqr (hpq pp)

---
-- EXERCÍCIO 7: Identidade e Acúmulo de Hipóteses
-- Hipóteses: Uma função que espera 'p' e 'q' para entregar 'r', e outra que leva 'p' a 'q'.
-- Meta: Uma função que recebe 'p' e entrega 'r'.
-- Dica: Ao abrir a portaria com 'fun hp =>', você terá 'hp : p'. Como você
-- consegue gerar o 'q' que a primeira hipótese também pede?
theorem deducao_complexa (hpqr : p → (q → r)) (hpq : p → q) : p → r :=
  fun pp => hpqr pp (hpq pp)

---
-- EXERCÍCIO 8: Comutatividade Completa do AND
-- Hipótese: Você recebe um pacote 'h : p ∧ q'.
-- Meta: Você precisa devolver um pacote invertido 'q ∧ p'.
-- Dica: Desmonte 'h' usando as projeções (.left e .right) e monte o novo par
-- usando And.intro ou a notação de construtor anônimo ⟨..., ...⟩.
theorem trocar_ordem (h : p ∧ q) : q ∧ p :=
  ⟨h.right,h.left⟩


---
-- EXERCÍCIO 9: Implicação com Múltiplos Argumentos empacotados
-- Hipóteses: Uma implicação 'hpqr' que espera 'p' e 'q' (em cadeia) para entregar 'r',
--            e um pacote 'hpq' contendo as provas de 'p ∧ q' juntas.
-- Meta: Entregar uma prova de 'r'.
-- Dica: Você não precisa abrir portarias com 'fun' porque a meta é apenas 'r'.
-- Seu objetivo é extrair as peças de dentro de 'hpq' para alimentar a função 'hpqr'.
theorem and_elim_to_impl (hpqr : p → q → r) (hpq : p ∧ q) : r :=
  hpqr (hpq.left) (hpq.right)

---
-- EXERCÍCIO 10: Distribuição do AND sobre o OR
-- Hipótese: Você tem um pacote contendo 'p' E uma escolha entre 'q ∨ r'.
-- Meta: Você precisa entregar uma escolha entre (p ∧ q) OU (p ∧ r).
-- Dica: Use as projeções .left e .right. Como o lado direito (.right) é um OR,
-- você precisará usar o .elim nele para abrir os dois caminhos.
theorem and_distrib_or (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) :=
  h.right.elim
    (fun pq => Or.inl ⟨h.left, pq⟩)
    (fun pr => Or.inr ⟨h.left,pr⟩)

---
-- EXERCÍCIO 11: Combinação de Implicações em Disjunção
-- Hipóteses: Uma implicação que leva 'p' a 'r', outra que leva 'q' a 'r',
--            e uma escolha inicial 'p ∨ q'.
-- Meta: Entregar uma prova de 'r'.
-- Dica: Faça a eliminação de 'h'. Em cada ramo, use a função correspondente
-- (hpqr ou hqrr) para transformar a hipótese local no 'r' que você precisa.
theorem or_elim_impl (hpqr : p → r) (hqrr : q → r) (h : p ∨ q) : r :=
  h.elim
    (fun pp => hpqr pp)
    (fun pq => hqrr pq)

---
-- EXERCÍCIO 12: Modus Tollens (A Regra do Contrapositivo)
-- Hipóteses: 'hpq' diz que 'p → q', e 'hnq' é uma prova de '¬q' (ou seja, 'q → False').
-- Meta: Provar '¬p' (que o Lean enxerga como 'p → False').
-- Dica: Como a meta final é uma implicação ('p → False'), comece abrindo a portaria
-- com 'fun hp =>'. Seu objetivo interno passará a ser gerar um 'False'.
-- Use as funções do inventário em cadeia para chegar no absurdo!
theorem modus_tollens (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun pp => hnq (hpq pp)
---
-- EXERCÍCIO 13: O Silogismo Disjuntivo
-- Hipóteses: Você sabe que vale 'p ∨ q' (uma escolha) e tem uma prova 'hnp : ¬p'.
-- Meta: Entregar uma prova de 'q'.
-- Dica: Faça a eliminação por casos da disjunção 'h'.
-- No caso da direita, você ganha 'hq : q' (meta resolvida!).
-- No caso da esquerda, você ganha 'hp : p'. Mas você tem 'hnp : ¬p' no inventário global!
-- Use a função 'absurd' nesse ramo para explodir a contradição e fechar a meta.
theorem silogismo_disjuntivo (h : p ∨ q) (hnp : ¬p) : q :=
  h.elim
    (fun pp => absurd pp hnp)
    (fun pq => pq)
