import Mathlib.Tactic
import Verbose.Catalan.All

Exemple "En un domini, primer implica irreductible"
  Dades: (A : Type) [CommRing A] [IsDomain A] (p : A)
  Hipòtesis: (hp : p ≠ 0) (h : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
  Conclusió: ∀ (a b : A), p = a * b → (∃ x, a * x = 1) ∨ (∃ x, b * x = 1)
Prova:
  sorry
QED

