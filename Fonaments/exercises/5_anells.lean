import Mathlib.Tactic
import Verbose.Catalan.Help

/-
En aquest exercici us pot ser útil el teorema
* mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c
-/
Exemple "En un domini, primer implica irreductible"
  Dades: (A : Type) [CommRing A] [IsDomain A] (p : A)
  Hipòtesis: (hp : p ≠ 0) (h : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
  Conclusió: ∀ (a b : A), p = a * b → (∃ x, a * x = 1) ∨ (∃ x, b * x = 1)
Prova:
  sorry
QED

