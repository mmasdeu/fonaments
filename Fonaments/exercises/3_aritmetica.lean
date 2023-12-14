import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Init.Function
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Verbose.Catalan.All

open Function Finset Dvd Rat
open scoped BigOperators


Exemple "La suma dels primers n naturals"
  Conclusió: ∀ n,  ∑ k in range (n + 1), (k : ℝ) = n * (n + 1) / 2
Demostració:
  sorry
QED

Exemple "La suma dels primers n quadrats"
  Conclusió: ∀ n,  ∑ k in range (n + 1), (k^2 : ℝ) = n * (n + 1) * (2*n + 1) / 6
Demostració:
  sorry
QED


Lema even_of_even_sq "Si m^2 és parell, aleshores m és parell"
Dades: (m : ℕ)
Hipòtesis: (h : 2 ∣ m^2)
Conclusió: 2 ∣ m
Demostració:
  exact Prime.dvd_of_dvd_pow (Nat.prime_iff.mp Nat.prime_two) h -- LEAN ja ho sap
QED

Exemple "L'arrel quadrada de 2 és irracional"
  Dades: (m n : ℕ)
  Hipòtesis: (mn_coprimers : m.gcd n = 1)
  Conclusió:  m^2 ≠ 2 * n^2
Demostració:
  sorry
QED

