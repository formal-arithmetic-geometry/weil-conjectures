/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The affine-adjoining step of single-complex source-open induction

Source: Stacks Project, Tag 0DJ9, induction step.
(blueprint: lem-pc-single-complex-open-affine-union).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Gluing the comparison after adjoining one affine open.

Source: Stacks Project, Tag 0DJ9, induction step, applied inside `U ⊔ V`.
(blueprint: lem-pc-single-complex-open-affine-union).

Proof: Set W = U union V. Its compactness follows from compactness of U and
of the affine V. Restrict the cartesian square and both coefficients to W and
its inverse image. Derived pullback preserves quasi-coherent cohomology.
The inverse images of U and V in W cover W, and their intersection is compact
because X is quasi-separated over affine S. The restricted morphism W -> S
is qcqs. Since g is a morphism between affine schemes, its base change g' is
affine, so the three inverse-image opens in X' are also quasi-compact.
Use relative Mayer--Vietoris on this two-open cover for both coefficients.
Apply Lg* to the original direct-image triangle and compare it to the new-base
triangle. Naturality of the adjunction units and counits and the derived
composition comparisons gives a morphism of distinguished triangles whose
components are the comparison on W, the direct sum of those on U and V, and
the comparison on their intersection. The identifications with the ambient
open comparisons are the canonical nested-open identifications. The last two
components are invertible by the three hypotheses, so the first is invertible
by the two-out-of-three theorem for morphisms of distinguished triangles.
This proves the claim. Empty opens and redundant covers obey the same triangle
argument; neither the stalk condition nor a global comparison is assumed. -/
theorem singleComplexOpenComparison_affine_union
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVaff : IsAffineOpen V)
    (hU : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U))
    (hV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ V))
    (hUV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊓ V))) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊔ V)) := by sorry

end AlgebraicGeometry
