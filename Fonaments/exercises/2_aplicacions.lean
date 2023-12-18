import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Init.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Verbose.Catalan.Help


open Function Finset Dvd Rat
open scoped BigOperators

variable {X Y : Type}

def Injectiva (f : X → Y) := ∀ x y, (f x = f y) → x = y
def Exhaustiva (f: X → Y) := ∀ y, ∃ x, f x = y


Exemple "La composició de funcions injectives és injectiva"
Dades: (f : X → Y) (g : Y → Z)
Hipòtesis: (hf: Injectiva f) (hg: Injectiva g)
Conclusió: Injectiva (g ∘ f)
Prova:
  sorry
QED

Exemple "La composició de funcions exhaustives és exhaustiva"
Dades: (f : X → Y) (g : Y → Z)
Hipòtesis: (hf: Exhaustiva f) (hg: Exhaustiva g)
Conclusió: Exhaustiva (g ∘ f)
Prova:
  sorry
QED

Exemple "Si g ∘ f és injectiva aleshores f també ho és."
Dades: (f : X → Y) (g : Y → Z)
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
Dades: (f : X → Y) (g : Y → Z)
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

def Fib : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => Fib n + Fib (n+1)

/-
Per aquest exercici us poden ser útils els següents teoremes:
* range_succ : range (n + 1) = insert n (range n)
* sum_insert (h : a ∉ s) : ∑ x in insert a s, f x = f a + ∑ x in s, f x
* not_mem_range_self : n ∉ range n

-/
Exemple "Exercici del parcial sobre Fibonacci"
  Conclusió: ∀ n, 1 + ∑ i in range n, Fib i = Fib (n+1)
Demostració:
  sorry
QED

