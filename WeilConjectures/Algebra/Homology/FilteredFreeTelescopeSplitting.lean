/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! The degreewise split exact sequence of an exhaustive split filtration. -/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Identity minus successor on the direct sum of the filtration stages. -/
noncomputable def filteredTelescopeMap {A : Type u} [CommRing A]
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (step : ∀ n, F n ⟶ F (n + 1)) : (∐ F) ⟶ ∐ F :=
  Sigma.desc fun n ↦ Sigma.ι F n - step n ≫ Sigma.ι F (n + 1)

/-- Augmentation from the direct sum, induced by the inclusions in the union. -/
noncomputable def filteredTelescopeAugmentation {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) : (∐ F) ⟶ P :=
  Sigma.desc ι

/-- Compatibility makes the telescope maps a short complex. -/
theorem filteredTelescope_comp_zero {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n) :
    filteredTelescopeMap F step ≫ filteredTelescopeAugmentation P F ι = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [filteredTelescopeMap, filteredTelescopeAugmentation, Preadditive.sub_comp,
    Category.assoc, hcompat]

/-- The explicitly constructed telescope sequence is split exact in each degree.
Source: Stacks Project, Tags 09KL--09KM, admissible telescope sequence.
(blueprint: lem-pc-filtered-free-telescope-splitting)

Proof: write S = direct sum of F n, a = identity minus successor, and b for the
augmentation induced by the compatible inclusions. These are precisely the maps
in the statement; they commute with differentials because their summand maps do.
Compatibility gives b a = 0. Work in an arbitrary degree k, identifying S.X k
with the direct sum of (F n).X k by preservation of coproducts by evaluation.
Every vector has finite support. The zeroth coordinate of a(x) is x_0; once the
coordinates before n vanish, its nth coordinate is x_n. Induction therefore
proves that a is injective. Exhaustion proves that b is surjective.
For exactness at S, take z with b(z) = 0 and choose N containing its finite support.
For i <= N let t(i,N) be the composite of the transition maps, with t(N,N) = id.
The relations e_i(x) - e_(i+1)(step_i(x)) = a(e_i(x)) show, by a finite
sum, that z is congruent modulo image(a) to e_N(sum_i t(i,N)(z_i)).
The image of this last coefficient under ι_N is b(z) = 0. Since ι_N is monic,
the coefficient is zero. Thus kernel(b) = image(a), in every degree.

Choose the given degree-k retractions r_i of step_i. For i < j define r(j,i)
by composing r_(j-1), ..., r_i, and put r(i,i) = id. Define a linear map
l : S.X k -> S.X k on the jth summand by giving its ith coordinate as
-r(j,i) for i < j, and zero for i >= j. This has finite support on every
summand and hence defines a map out of the direct sum. In l a on summand n,
the coordinates below n cancel using step_n followed by r_n = id; coordinate
n is id and coordinates above n vanish. Hence l a = id.
Let p = id - a l. It kills image(a). By the kernel calculation and surjectivity
of b, it factors uniquely as s b for a linear s : P.X k -> S.X k.
Equivalently s(x) = p(z) for any lift b(z) = x; differences of lifts lie in
image(a), which p kills, so this formula is independent of the lift and linear.
Then b s = id by surjectivity, and a l + s b = id by definition of p.
These three identities give the required ShortComplex.Splitting. The retractions
need not commute with differentials: the splitting is only degreewise. No
K-projectivity, zero initial stage or boundedness assumption is used here.

For its downstream use, the coproduct S is K-projective whenever the stages are:
restrict a map to an acyclic complex to each summand, choose a null homotopy,
and assemble the components by degreewise coproducts. The split exact sequence
gives a distinguished triangle S -> S -> P -> S[1] in the homotopy category.
K-projectivity is left orthogonality to acyclic complexes, stable under shifts
and extensions; the exact Hom sequence then makes P K-projective. These final
two arguments are separate checked proofs in the assembly, not hypotheses or
conclusions of this construction lemma. Zero rings and zero filtrations are included. -/
theorem filteredTelescope_degreewise_splitting {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k)) :
    ∀ k : ℤ, Nonempty
      (((ShortComplex.mk (filteredTelescopeMap F step)
        (filteredTelescopeAugmentation P F ι)
        (filteredTelescope_comp_zero P F ι step hcompat)).map
          (HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) k)).Splitting) := by
  sorry

end CochainComplex
