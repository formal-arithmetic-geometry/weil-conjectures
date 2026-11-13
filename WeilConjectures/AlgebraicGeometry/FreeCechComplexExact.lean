/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible
import WeilConjectures.AlgebraicGeometry.FreeCechComplexDecomposition

/-!
# Exactness of the free Čech complex on the small étale site

## References

* Stacks Project, Tag 03F5.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The chain complex `K_• = 𝒪_{𝒰,•}` of presheaves of `𝒪`-modules of the family
`𝒰 = {f i : U i ⟶ U₀}` of `X_ét` is exact in positive degrees, evaluated at every object `W`.
Here `K_•` is the alternating face map complex of the Čech nerve of the family
`i ↦ Over.mk (f i)` in `Over U₀`, sent to presheaves of `𝒪`-modules by
`V ↦ PresheafOfModules.free 𝒪 (yoneda V)`. (Stacks, Tag 03F5) -/
theorem freeCechComplex_exact (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) (p : ℕ) :
    (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O)))).ExactAt (p + 1) := by
  classical
  apply (freeCechComplex_exact_iff_fibres X ι U₀ U f O W p).2
  intro φ
  let S := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
  have h := Algebra.powerSetComplex_contractible (O.obj (op W)) S
  by_cases hS : Nonempty S
  · exact (h.2.2.2.1 hS).1 p
  · have : IsEmpty S := not_nonempty_iff.mp hS
    have : Subsingleton (Algebra.powerSetComplexObject (O.obj (op W)) S (p + 1)) :=
      h.2.2.1 inferInstance (p + 1)
    exact Subsingleton.elim _ _

end AlgebraicGeometry
