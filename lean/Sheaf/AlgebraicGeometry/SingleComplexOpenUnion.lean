/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.RelativeMayerVietoris

/-! # Source-open union gluing for the single-complex comparison

Source: Stacks Project, Tag 0DJ9, induction step.
(blueprint: lem-pc-single-complex-open-union).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Mayer--Vietoris on a union, expressed in the ambient scheme's open coordinates.
Source: Stacks Project, Tag 0DJ9, induction step.
(blueprint: lem-pc-single-complex-open-union).

Proof: Put W = U union V. Inside W take the inverse images of U and V; they cover W,
are quasi-compact, and their intersection identifies with U intersection V. Since
X is quasi-separated over the affine S, the quasi-compact open immersion W → X
is quasi-compact, and W → S is qcqs. Base change identifies W' with X' times_X W.
Restrict K and K' and transport phi by the pullback composition comparisons.
Open restriction preserves quasi-coherent cohomology. Apply relativeMayerVietoris
to the resulting square with source W. Its three comparison hypotheses are the
ambient comparisons on U, V and their intersection: the identifications follow
from associativity of fibre products and coherence of derived pullback composition
and its direct-image mates. The conclusion is the ambient comparison on W by the
same naturality. Empty opens cause no exception; a redundant member of the cover
also gives the same comparison. -/
theorem singleComplexOpenComparison_union
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
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U))
    (hV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ V))
    (hUV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊓ V))) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊔ V)) := by sorry

end AlgebraicGeometry
