/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DistTriang
public import WeilConjectures.TraceFormula.TransverseBoundary.OneDivisor

/-!
# Local constancy along the boundary divisor

Let `C` be a transverse corner over an algebraically closed field `k`
(`AlgebraicGeometry.Scheme.TransverseCorner`), `ℓ` a prime invertible in `k`, `Λ` a finite
commutative `ℓ`-primary ring and `E` a bounded complex of `Λ`-modules on `Z - (X ∪ Y)` with
finite locally constant cohomology whose monodromy factors through a finite `ℓ`-group. Then
`M = Rj_* i_! E` restricted to `Y - z` has finite locally constant cohomology sheaves: its
stalks are the continuous cohomology of the tame inertia representation of `E` along `Y`, and
the specialization maps between them are isomorphisms (blueprint
`det-tf-transverse-tame-local-constancy`).

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.isFiniteLocallyConstantSheaf_homology_boundaryComplex`:
  the cohomology sheaves of `M|_{Y - z}` are finite locally constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : (ℓ : k) ≠ 0) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)

include hℓ hΛ in
/-- Blueprint `det-tf-transverse-tame-local-constancy`, after the reduction to one divisor: for
`j_W : Z - (X ∪ Y) ⟶ W = Z - X`, the restriction of `R j_{W*} E` to the regular divisor
`Y - z ⊆ W` has finite locally constant cohomology sheaves (tameness along `Y` and Abhyankar's
lemma, Stacks Tag 0EYG). -/
theorem hasFiniteLocallyConstantHomology_puncturedYι_jW
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) :
    HasFiniteLocallyConstantHomology C.puncturedY
      ((L((C.puncturedYι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((C.jW)_*[ModuleCat.{u + 1} Λ])).obj E)) := by
  sorry

include hℓ hΛ in
/-- Blueprint `det-tf-transverse-tame-local-constancy`: Local constancy along the boundary
divisor. The restriction of `M = Rj_* i_! E` to the punctured divisor `Y - z` has finite locally
constant cohomology sheaves. On `W = Z - X`, which contains `Y - z`, `M` is `R j_{W*} E`
(`AlgebraicGeometry.Scheme.TransverseCorner.leftDerivedUpperStarPuncturedYBoundaryComplexIso`),
and only the regular divisor `Y` remains
(`AlgebraicGeometry.Scheme.TransverseCorner.hasFiniteLocallyConstantHomology_puncturedYι_jW`). -/
theorem isFiniteLocallyConstantSheaf_homology_boundaryComplex
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) (n : ℤ) :
    IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((L((C.puncturedY.ι ≫ C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E))) := by
  obtain ⟨a, -, ha, -⟩ := hE.1
  exact (C.hasFiniteLocallyConstantHomology_puncturedYι_jW hℓ Λ hΛ E hE).of_iso
    (C.leftDerivedUpperStarPuncturedYBoundaryComplexIso Λ E a).symm n

end AlgebraicGeometry.Scheme.TransverseCorner
