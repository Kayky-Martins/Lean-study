import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

section Conjunction

/- O objetivo desta seção é apresentar o uso da conjução através
 de táticas novas, até o momento vimos somente por proof terms-/

/- tática constructor: a tatica constructor permite mostrar conjuncoes
separando objetivos da forma A ∧ B em A e B, no geral ele pega um tipo indutivo
e deconstroi ele partes -/

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

/- Ao passar o curso sobre o nome da tatica vc pode ler a documentancao dela
nesta parte temos que constructor <;> linarith pega cada ojetivo e aplica linarith-/

example {x y z : ℝ} (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ y ∧ x ≤ z := by
  constructor <;> linarith

/- Note que os exemplos acima são para cada eu quero demonstrar um objetivo que é
conjução -/

/- Caso eu queira USAR uma conjucao eu devo usar rcases ou rintro -/

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁ -- contrapose faz exatamente o que uma demosntracao por contraposicao faz
  exact le_antisymm h₀ h₁

/- Ao encontrar uma tatica que vc nao conhece vc pode fazer
#check le_antisymm
para descobrir o que ela faz exatamente

Ao longo do projeto, valhe a pena se familiarizar com apply? exact? loogle e mathlibsearch
-/

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

/- De forma muito similar podemos usar as ideias acima para lidar com ∃ -/

example {f : ℝ → ℝ} (h : ∃ x, f x = 3) : ∃ y : ℝ, f y ^ 2 = 9 := by
  obtain ⟨x, heq⟩ := h -- resgatamos o x e o que ele faz
  use x -- para tentar terminar um objetivo com ∃ podemos usar use
  rw [heq]; norm_num

example {f : ℝ → ℝ} (h : ∃ x, f x = 3) : ∃ y : ℝ, f y ^ 2 = 9 := by
  obtain ⟨x, heq⟩ := h -- resgatamos o x e o que ele faz
  exact ⟨x, by rw[heq]; norm_num⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5/2
  constructor <;> norm_num

-- Problemas

-- use qualquer metodo de lidar com ∧ que vc preferir

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h₀, h₁⟩
  constructor
  · exact h₀
  intro h
  exact h₁ (dvd_antisymm h₀ h)


-- utilize as seguintes definicoes

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable {f g : ℝ → ℝ}

-- tente usar leansearch para encontrar as taticas de desigualdades necessarias

theorem fnUb_add {a b : ℝ} (ubf : FnUb f a) (ubg : FnUb g b) : FnUb (fun x ↦f x + g x) (a + b) := by
  intro x
  have hf : f x ≤ a := ubf x
  have hg : g x ≤ b := ubg x
  linarith

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, h_a⟩
  rcases ubg with ⟨b, h_b⟩
  use (a+b)
  intro x
  have hf : f x ≤ a := h_a x
  have hg : g x ≤ b := h_b x
  linarith

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- Tarefa

end Conjunction

--aprenda a usar calc e faca os seguintes exercicios

section Calc

theorem ex1 (a b c : ℕ) : a + (b + c) = c + (a + b) := by
  sorry

theorem ex2 (a b c : ℕ) : (a * b) * c = b * (c * a) := by
  sorry

theorem ex3 (a b c : ℕ) : (a + b) * c = c * a + c * b := by
  sorry

theorem ex4 (a b c : ℕ) : (a + b) + c = c + (b + a) := by
  sorry

end Calc
