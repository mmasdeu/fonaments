import Mathlib.Tactic
import Verbose.Catalan.All


Exemple "Exercici del Parcial 2024"
  Conclusió: ∀ n, ∃ m, ∀ k, ( (k > n) → 2*k > n + m )
Demostració:
  sorry
QED

/-
Per aquest exercici és útil la tàctica "nlinarith", que intenta demostrar desigualtats
-/
Exemple "Exercici 24 de la llista"
  Conclusió: ∀ (n : ℕ), ∃ m, ∀ k, (∃ t s, (t < k) ∧ (t < n) ∧ (t > s)) → ((m > n) ∧ (m < k * n))
Demostració:
  sorry
QED

/-
Per aquest exercici els següents lemes que LEAN ja sap poden us ser útils:

* Nat.mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k
* tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c
* Nat.eq_one_of_mul_eq_one_right {m n : ℕ} (H : m * n = 1) : m = 1
-/
Exemple "Exercici 21 de la llista"
  Conclusió: ∀ n, ∃ m, ∀ k, ((∃ u, (n+1 = k * u)) ∧ (∃ v, (m = k*v))) → k = 1
Demostració:
  sorry
QED

