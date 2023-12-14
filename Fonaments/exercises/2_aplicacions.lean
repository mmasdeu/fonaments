import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Init.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Verbose.Catalan.All


open Function Finset Dvd Rat
open scoped BigOperators

variable {X Y : Type}

def Injectiva (f : X → Y) := ∀ x y, (f x = f y) → x = y
def Exhaustiva (f: X → Y) := ∀ y, ∃ x, f x = y


Exemple "Si g ∘ f és injectiva aleshores f també ho és."
Conclusió: Injectiva (g ∘ f) → Injectiva f
Prova:
  sorry
QED

-- Exercici 45b
Exemple "Si g ∘ f és injectiva, g no té per què ser-ho."
Conclusió: ∃ (f g : ℕ → ℕ), (Injectiva (g ∘ f) ∧ ¬ Injectiva g)
Prova:
  sorry
QED


Exemple "Si g ∘ f és exhaustiva aleshores g també ho és."
Conclusió: Exhaustiva (g ∘ f) → Exhaustiva g
Prova:
  sorry
QED

Exemple "Si g ∘ f és exhaustiva aleshores f no té per què ser-ho."
Conclusió: ∃ (f g : ℕ → ℕ), (Exhaustiva (g ∘ f) ∧ (¬ Exhaustiva f))
Demostració:
{
  sorry
}
QED


def Fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => Fib n + Fib (n+1)

Exemple "Fibonacci"
  Conclusió: ∀ n, 1 + ∑ i in range n, Fib i = Fib (n+1)
Demostració:
  sorry
QED

def Collatz : ℕ → ℕ := λ n ↦ if (Even n) then n / 2  else 3 * n + 1

Exemple "Collatz no és injectiva"
  Conclusió: ¬ (Injectiva Collatz)
Demostració:
  sorry
QED

Exemple "Collatz és exhaustiva'"
  Conclusió: Exhaustiva Collatz
Demostració:
  sorry
QED

