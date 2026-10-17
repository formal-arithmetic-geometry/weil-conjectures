/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension

import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# The affine Artin vanishing bound

Let `K` be a field with `cd_tor(K) ≤ c` and `X` an affine `K`-scheme of finite type. Then
`cd_tor(X) ≤ dim X + c` (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`,
blueprint `thm-sc-affine-torsion-cd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Blueprint `thm-sc-affine-torsion-cd`: The affine torsion cohomological dimension bound.

Let `K` be a field with `cd_tor(K) ≤ c`, and let `X` be an affine `K`-scheme of finite type
(structure morphism `a`) of dimension at most `d`. Then `cd_tor(X) ≤ d + c`:
`Hᵠ(X_ét, F) = 0` for every torsion abelian étale sheaf `F` on `X` and every `q > d + c`.

The proof is by induction on `d`, over all ground fields at once; it reduces to algebraically
closed `K` (`lem-sc-cd-ground-field`) and, by Noether normalisation, to affine space, where the
Leray spectral sequence of `𝔸ᵈ ⟶ ℙ¹ × 𝔸ᵈ⁻¹ ⟶ 𝔸ᵈ⁻¹` and a computation of the stalks of the
higher direct images (`lem-sc-one-variable-field-cd`, `lem-sc-cd-affine-limit`) conclude. -/
theorem hasTorsionCohomologicalDimensionLE_of_isAffine {K : Type u} [Field K] {c d : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [IsAffine X]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) := by
  let : X.Over (Spec (.of K)) := ⟨a⟩
  have hK' : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c := by
    intro F hF q hq
    have : Subsingleton ((Sheaf.functorH _ q).obj F) := hK F hF q hq
    obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso (Spec (.of K)) q
    exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton
  have : LocallyOfFiniteType (X ↘ Spec (.of K)) := ‹LocallyOfFiniteType a›
  have hX' := hasTorsionEtaleCohomologicalDimensionLE_of_isAffine_of_dimension_le
    K c d hK' X hX
  intro F hF q hq
  have hz := hX' F hF q hq
  have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} X q).obj F) := hz
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  exact (e.app F).addCommGroupIsoToAddEquiv.injective.subsingleton

end AlgebraicGeometry.Scheme
