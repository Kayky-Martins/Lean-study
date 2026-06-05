-- Encontro Lean4
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option linter.style.longLine false

-- Linarith
-- Tem o propósito de resolver dilemas lineares, exemplos:
example (a b : ℝ) : a + 2*b = a + b + b := by
  linarith
example (a b c d e : ℝ) (h : a > b) (h2 : b > c) (h3 : c > d) (h4 : d > e) : a > e := by
  linarith

-- Ring
-- Resolve problemas que envolvem anéis (muito útil com os reais)
-- (problemas com associatividade, comutatividade, etc.), exemplo:
-- Ela trata de anéis unitários comutativos, ou seja, possuem elemento neutro
-- para multiplicação e também são comutativos nela
example (a b : ℝ) : a * b + b + a = b * a + a + b := by
  ring

-- VARIÁVEIS (variable)
-- Servem de forma análoga a matemática, podemos ter algo como:
-- x | x ∈ ℝ
-- E isso nos ajudará na organização

-- SEÇÕES (section/end)
-- São partes do código onde podemos definir variáveis específicas
-- caso não queiramos que essas variáveis estejam em outras partes
-- Ex:

section
variable (a : ℝ)
#check a -- Exibe o tipo da variável "a"

example (h : a > 0) : a + a > a := by
  linarith

example : a + a + a = 3 * a := by
  ring
example {b : ℝ} : 3 * (a + b) = 3*a + 3*b := by
  ring
end
-- #check a -- não existe fora da section

-- Exercício: Como ficariam as provas sabendo dessas táticas?
theorem real_sum_comm {a b : ℝ} : a + b = b + a := by
  ring

theorem real_sum_assoc {a b c : ℝ} : (a + b) + c = a + (b + c) := by
  ring

theorem real_mul_comm {a b : ℝ} : a * b = b * a := by
  ring

theorem real_mul_assoc {a b c : ℝ} : a * b * c = a * (b * c) := by
  ring

theorem sum_squared {a b : ℝ} : (a + b) * (a + b) = a*a + 2 * a * b + b * b := by
  ring

theorem sum_mul_dif {a b : ℝ} : (a + b) * (a - b) = a*a - b*b := by
  ring

example {x y z : ℝ} (h1 : x < y) (h2 : y = z + 2) : x < z + 2 := by
  linarith

example {x y z w : ℝ} (h1 : z = x * x + y * x) (h2 : w = x * x + y * x) (h3 : x + z < y + w) : x < y := by
  linarith

example {x y z : ℝ} (h1 : z = (x + 1) * (x + 1)) (h2 : x * x + 2 * x < y) : z - 1 < y := by
  rw[h1,sum_squared]
  linarith

example {x y z w : ℝ} (h1 : z = x + y) (h2 : w = x - y) (h3 : x * x = y * y) : w * z = 0 := by
  rw[h2,h1,mul_comm,sum_mul_dif,h3]
  ring
-- NAMEPSACE
-- São partes do código que podem ser definidos conceitos
-- importantes, que podem ser reutilizados posteriormente

namespace Geometria

def Ponto : Type := ℝ × ℝ

def DistanciaAoQuadrado (p1 p2 : Ponto) : ℝ :=
  let (x1, y1) := p1
  let (x2, y2) := p2
  (x1-x2)*(x1-x2) + (y1-y2)*(y1-y2)

end Geometria

-- Uma outra forma de definir ponto e distância:
namespace Geometria_2

structure Ponto where
  x : ℝ
  y : ℝ

def DistanciaAoQuadrado (p1 p2 : Ponto) : ℝ :=
  let dx := p2.x - p1.x
  let dy := p2.y - p1.y
  dx * dx + dy * dy

def SomaDoisPontos (p1 p2 : Ponto) : Ponto :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

-- Exercício:
-- defina produto por escalar
def ProdutoPorEscalar (p : Ponto) (r : ℝ) : Ponto :=
  {x:=r*p.x, y:=r*p.y}

-- defina projeção no eixo X e no eixo Y (no plano cartesiano convencional)
def ProjecaoEixoX (p : Ponto) : Ponto:=
  {x:= p.x,y:=0}

def ProjecaoEixoY (p : Ponto) : Ponto:=
    {x:= 0,y:=p.y}

-- defina ProdutoEscalar entre dois pontos que retorna um ℝ
def ProdutoEscalar (p1 p2 : Ponto) : ℝ:=
  p1.x * p2.x + p1.y*p2.y

-- def NomeDaDefinição (parâmetros) : Tipo :=
--  desenvolvimento

end Geometria_2

-- Para usar o que criou dentro de um namespace, basta
-- explicitar o nome do namespace e acessar o que quer
#check Geometria_2.Ponto

-- Pense como seria para criar um namespace para o R³ e como seria definir suas operações
-- como Produto Escalar, Produto p/Escalar, Produto Vetorial, etc.
