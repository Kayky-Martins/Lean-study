set_option linter.unusedVariables false

variable {α β χ : Type}

-- Lean também funciona como uma linguagem de programação.
section Tipos

  -- Aqui, temos a função adição, onde Nat é um número natural
  -- de precisão arbitrária.
  def add (x y : Nat) : Nat :=
    x + y

  -- Int é o tipo de números inteiros de precisão arbitrária.
  -- Esse exemplo mostra o controle de flow mais simples possível,
  -- if-then-else.
  def pos (x : Int) : Bool :=
    if x > 0
      then true
      else false

  -- Essa é a função valor absoluto de um inteiro.
  -- Como esse número é necessariamente não-negativo,
  -- o valor de retorno é Nat.
  def abs (x : Int) : Nat :=
    Int.toNat
      (if x > 0
        then x
        else -x)

  -- Podemos evaluar nossas funções com a palavra-chave eval:
  #eval abs (-1 * (add 1 3))

  -- Também podemos criar funções polimórficas, ou seja, que atuam
  -- sobre vários tipos. A seguinte função é válida para qualquer tipo α.
  def identity (a : α) : α := a
  #eval identity true --exemplo de uso da identity( pode ser qualquer coisa no lugar de true)

  -- O tipo α → β (digite \a \r \b) representa o tipo de funções
  -- cujo parâmetro é de tipo α e cujo valor de retorno é de tipo β.
  -- Criamos elementos desse tipo com a notação de função anônima:
  -- se y é de tipo γ, então (fun x => y) é de tipo χ → γ
  -- e a variável x interna à função é de tipo χ.
  def compose (f : α → β) (g : β → χ) : α → χ :=
    fun n => g (f n)

  -- O tipo α × β (digite \a \x \b) representa o produto cartesiano de α e β.
  -- Em linguagens como Python, equivale ao tipo tupla.
  -- Você pode criar tuplas a partir de seus elementos básicos com a notação
  -- (a, b), e você pode acessar os elementos constituentes de uma n-tupla
  -- a partir de índices numéricos: t.1, t.2, ... t.n
  def prod_swap (e : α × β) : β × α :=
    (e.2, e.1)
    -- Alternativamente, comente a linha acima e descomente a linha abaixo:
    -- Prod.mk e.2 e.1

  example (f : α → χ) : α × β → χ :=
    fun pair => f pair.1

  -- O tipo α ⊕ β (digite \a \o+ \b) representa a união disjunta de α e β,
  -- também conhecido como tipo soma.
  -- Um elemento desse tipo é, necessariamente, ou do caso α ou do caso β.
  -- Ele possui dois construtores canônicos: Sum.inl e Sum.inr.
  -- Se m é de tipo μ, então (Sum.inl m) é de tipo μ ⊕ η,
  -- enquanto (Sum.inr m) é de tipo η ⊕ μ (η arbitrário).
  -- Podemos "eliminar" tipos soma da seguinte maneira: se s é de tipo α ⊕ β,
  -- f é de tipo α → χ e g é de tipo β → χ, então a expressão (s.elim f g)
  -- é de tipo χ. Internamente, a função elim determina a qual caso o elemento
  -- s pertence e aplica a função f ou g respectiva.
  def sum_swap (sum : α ⊕ β) : β ⊕ α :=
    sum.elim
      (fun a => Sum.inr a)
      (fun b => Sum.inl b)

  -- O tipo Empty é um tipo especial: é um tipo que não possui nenhum valor
  -- associado. Ele é geralmente utilizado para representar situações onde a
  -- computação é impossível (por exemplo, loops infinito) e para marcar
  -- caminhos de código inalcancáveis.
  -- A função Empty.elim transforma qualquer occorência do tipo Empty em
  -- qualquer outro tipo (isso é válido pois o tipo Empty é impossível de ser
  -- encontrado na prática).
  def anything (a : α) (na: α → Empty) : χ :=
    (na a).elim

  -- Uma notação mais curta para funções anônimas simples involve o uso de
  -- parênteses e · (digite \.), que representa o parâmetro da função.
  def double_empty_fun (a : α) : (α → Empty) → Empty :=
    (· a)
    -- Essa notação é equivalente a:
    -- fun fe => fe a

  -- Por fim, o tipo Unit é o tipo canônico com um único elemento.
  -- Equivale ao tipo `void` em C, e seu elemento canônico é a tupla vazia.
  def anything_and_unit (a : α) : α × Unit :=
    (a, ())
end Tipos

section Exercicios_Tipos
  -- Nesses exercícios, quero apenas que vocês façam as funções compilarem.

  example (f : α → β) (g : α → χ) : α → β × χ :=
    fun n => (f n,g n)

  example (f : α → χ) (g : β → χ) : α ⊕ β → χ :=
    fun soma => soma.elim
      (fun a => f a)
      (fun b => g b)

  example (sum1 : α ⊕ χ) (sum2 : β ⊕ χ) : (α × β) ⊕ χ :=
    sum1.elim
      (fun a =>
        sum2.elim
          (fun b => Sum.inl (a,b))
          (fun x2 => Sum.inr x2)
      )
      (fun x1 => Sum.inr x1)

  example (tn: ((α → Empty) → Empty) → Empty) : α → Empty :=
    fun a => tn (fun fe => fe a)--reflita

  example (sum : (α → Empty) ⊕ β) : α → β :=
    fun a => sum.elim
      (fun f => (f a).elim)
      (fun b => b)

end Exercicios_Tipos

variable {p q r : Prop}

-- Vamos, agora, voltar a discutir o uso de Lean como provador de teoremas,
  -- nos restringindo a lógica proposicional.
section Propo

  -- Na última reunião, utilizamos táticas para provar proposições.
  -- Hoje, nós não utilizaremos táticas, realizando apenas provas diretas -
  -- também conhecidas como "proof term".

  -- O exemplo mais simples é a prova trivial:
  theorem triv (hp : p) : p :=
    hp
  -- Como já temos uma prova hp da nossa hipótese p, hp é prova de p.
  -- Porém, para manipularmos os operadores usuais da lógica proposicional
  -- sem uso de táticas, precisamos de novas estratégias.

  -- Usando proof terms, podemos manipular implicações da mesma forma que
  -- manipulamos funções:
  theorem concat (hpq : p → q) (hrp : r → p) : r → q :=
    fun hr => hpq (hrp hr)

  -- Se hp é prova de p e hq é prova de q, então (And.intro hp hq) produz
  -- uma prova de p ∧ q. Dada uma prova (h : p ∧ q), a função h.left extrai
  -- uma prova de p e a função h.right extrai uma prova de q.
  example (hpq : p ∧ q) (hr: r) : r ∧ p :=
    And.intro hr (hpq.left)

  -- Alternativamente, podemos usar a notação de construtor anônimo,
  -- usando os símbolos ⟨ e ⟩ (digite \< e \>).
  theorem and_intro (hp : p) (hq : q) : p ∧ q :=
    ⟨hp, hq⟩

  -- Dada uma prova (hp : p), a expressão (Or.inl hp) constrói uma prova
  -- de p ∨ q enquanto (Or.inr) constrói uma prova de q ∨ p (q arbitrário).
  --
  -- A eliminação de disjunções é mais complicada: dado (h : p ∨ q),
  -- (hpr : p → r) e (hqr : q → r), então (h.elim hpr hqr) é uma prova de r.
  theorem or_swap (h : p ∨ q) : q ∨ p :=
    h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

  -- Em Lean, a negação é definida como a implicação em falsidade.
  -- Ou seja, ¬p = p → False.
  --
  -- A expressão "show p from h" não altera nada na semântica de execução
  -- do programa, apenas deixa claro que h é uma prova da proposição p.
  theorem impl_to_nand (h : p → q) : ¬(p ∧ ¬q) :=
    fun ha => show False from ha.right (h ha.left)

  -- A função absurd produz uma prova de qualquer proposição a partir de duas
  -- hipóteses contraditórias.
  theorem explosion (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp
end Propo

section Exercicios_Propo
  -- Lembrem-se: não utilizem a palavra chave `by` na resoluação!
  example (hpr : p → r) (hqr : q → r) : p ∨ q → r :=
    fun a=> a.elim
      (fun pp=> hpr pp)
      (fun pq=>hqr pq)

  example (ho : ¬p ∨ q) : p → q :=
    fun pp => ho.elim
      (fun pnp=> absurd pp pnp)
      (fun pq=>pq)

  example (hpq : p → q) (hpr : p → r) : p → q ∧ r :=
    fun pp=> ⟨hpq pp,hpr pp⟩


  example (htn: ¬¬¬p) : ¬p :=
    fun pp=> htn (fun (hnp : ¬p) => absurd pp hnp)

  example (hpq : p → q) : ¬q → ¬p :=
    fun pnq=>fun pp=> absurd (hpq pp) pnq


end Exercicios_Propo
