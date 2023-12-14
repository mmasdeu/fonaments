import Mathlib.Tactic
import Verbose.Catalan.All

variable {G : Type} [Group G]

def es_subgrup (X : Set G) : Prop := X.Nonempty ∧
(∀ x y, x ∈ X → y ∈ X → x * y⁻¹ ∈ X)


Lema subgroup.one_mem "1 pertany a tot subgrup"

Dades: {X : Set G}
Hipòtesis: (h : es_subgrup X)
Conclusió: (1 : G) ∈ X

Demostració:
  sorry
QED

Lema subgroup.inv_mem' "Els inversos hi pertanyen"

Dades: {X : Set G} {g : G}
Hipòtesis: (h : es_subgrup X) (hg: g ∈ X)
Conclusió: g⁻¹ ∈ X

Demostració:
  sorry
QED

Lema subgroup.inv_mem "Els inversos hi pertanyen 2"

Dades: {X : Set G}
Hipòtesis: (h : es_subgrup X)
Conclusió: ∀ g, g ∈ X ↔ g⁻¹ ∈ X

Demostració:
  sorry
QED

Lema subgroup.mul_mem "Els subgrups són tancats pel producte"

Dades: {X : Set G} {x y : G}
Hipòtesis: (h : es_subgrup X) (hx : x ∈ X) (hy : y ∈ X)
Conclusió: x * y ∈ X

Demostració:
  sorry
QED


/-
CENTRALITZADOR I NORMALITZADOR
-/

@[reducible] def centralitzador  (A : Set G) := {g : G | ∀ a, a ∈ A → g*a*g⁻¹ = a }

def es_normal {G : Type} [Group G] (N H : Set G) := N ⊆ H ∧ ∀ g n, g ∈ H → n ∈ N → g⁻¹ * n * g ∈ N

@[reducible] def normalitzador  (A : Set G) := {g : G | ∀ a, a ∈ A ↔ g*a*g⁻¹ ∈ A }

variable (A : Set G)

/-
Observeu que no cal assumir que A és no buit en el següent resultat!
-/
Exemple "El normalitzador és un subgrup"
Dades: (A : Set G)
Conclusió: es_subgrup (normalitzador A)
Demostració:
  sorry
QED

/-
Observeu que no cal assumir que A és no buit en el següent resultat!
-/
Exemple "El centralitzador és un subgrup"
Dades: (A : Set G)
Conclusió: es_subgrup (centralitzador A)
Demostració:
  sorry
QED

Exemple "El centralitzador és normal en el normalitzador"
Dades: (A : Set G)
Conclusió: es_normal (centralitzador A) (normalitzador A)
Demostració:
  sorry
QED

Exercici "Tot subgrup és normal en el seu normalitzador"
Dades: (H : Set G)
Hipòtesis: (hHG : es_subgrup H)
Conclusió: es_normal H (normalitzador H)
Demostració:
  sorry
QED

Exemple "El normalitzador és subgrup més gran on H és normal"
Dades: (H K : Set G)
Hipòtesis: (hKG : es_subgrup K) (hHK : es_normal H K)
Conclusió: K ⊆ normalitzador H
Demostració:
  sorry
QED

