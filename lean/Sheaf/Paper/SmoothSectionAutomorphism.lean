/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NoetherianEtaleSectionSpecialization

/-! # Action of a smooth ambient automorphism on the section dualizing line -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.NoetherianSectionSpecialization

/-- An ambient automorphism fixing a smooth section acts trivially on its dualizing line.
Source: sk-prop-sp-purity-bc, finite orientation factor, and sk-thm-dnc, centred etale
coordinates and the affine-space normalization.
(blueprint: lem-sp-smooth-section-automorphism).
Proof: after shifting by -2d, smooth duality makes the section dualizing complex a locally
constant free rank-one sheaf. Its automorphism is a scalar, detected on geometric stalks.
Choose centred etale coordinates at each geometric section point. The section dualizing
line is the local fundamental-class line with trace-normalized generator. The given
ambient isomorphism identifies the local pairs with degree one, so functoriality of the
local fundamental class sends this generator to itself. This statement follows on an
etale coordinate neighbourhood by the affine-space trace normalization and transitivity
of compact-support traces; the etale inverse-image/counit comparison carries the local
class to the class of the same section point. The inverse ambient isomorphism gives the
inverse comparison, so no multiplicity other than one occurs. Thus the scalar is one at
every geometric stalk. Faithfulness in degree zero and conservativity of geometric stalks
prove equality. Reintroducing the shift and the identity inverse-image compositor yields
the displayed equation for the actual counit-defined sectionMap. Invertibility of N is
used for smooth duality. Rank zero is the etale identity-counit equation; the empty base
and zero ring yield equality in the zero categories. No deformation comparison or
specialization-base-change theorem is used in this argument. -/
theorem sectionMap_automorphism
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y) [SmoothOfRelativeDimension d f]
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (s : Y ⟶ X) [IsClosedImmersion s] (hs : s ≫ f = 𝟙 Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (a : X ≅ X)
    (sq : IsPullback a.hom f f (𝟙 Y)) (hsect : s ≫ a.hom = (𝟙 Y) ≫ s) :
    sectionMap A f f (𝟙 Y) a.hom sq s s hsect =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app
        (sectionInvariant A f s) := by
  sorry

end AlgebraicGeometry.Etale.NoetherianSectionSpecialization
