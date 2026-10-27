/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensorDefs

/-! # Tensor compatibility of the scalar/open restriction comparison

Source: Stacks Project, sites-modules.tex, Tags 03EL and 0E8J;
sites-cohomology.tex, Tags 06YY and 07A4.
(blueprint: lem-coef-etale-open-scalar-restriction-tensor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The fixed scalar/restriction mate respects the normalized binary tensor comparisons.
Source: the restriction/tensor portion of the proof of
`lem-coef-etale-open-mixed-tensor-scalar`; Stacks Tags 03EL, 0E8J, 06YY and 07A4.

Proof: ordinary restriction of coefficients commutes sectionwise with the direct
image from the open slice site. The identity comparison is monoidal for the lax
coefficient and direct-image tensorators: both composites act on local tensors
by the same balancing map. Conjugating under scalar and geometric adjunctions
therefore makes the ordinary scalar/restriction comparison monoidal for the
canonical oplax structures. The inverse of this comparison is r-zero of the
fixed open comparison data, since both are the left-adjoint comparison for the
same sectionwise identity.

Apply this ordinary equation to each bidegree of two flat K-flat resolutions.
Restriction is exact and preserves flat objects and integer-indexed colimits,
so these resolutions can also compute the derived restriction tensorators.
Ordinary scalar extension takes these resolving complexes to flat K-flat
complexes over the new ring. The scalar representative maps and localization
tensorators on these models are invertible. The scalar-adjunction definition
of r transposes to the localized ordinary scalar unit, so its representative
normalization is exactly the degreewise ordinary scalar/restriction comparison.
The defining normalization of t identifies its inverse with the localized
ordinary oplax tensorator. Substitute these normalizations into the totalized
ordinary monoidality equation and cancel the representative isomorphisms.
This yields the displayed equation on resolving representatives. Naturality
in each argument and the existence of such representatives yield it for all
unbounded K and M. Each map preserves bidegrees, so the signed totalization
introduces no extra sign. Nothing requires a flat coefficient map, a nonempty
open, or a nonzero coefficient ring.
(blueprint: lem-coef-etale-open-scalar-restriction-tensor). -/
theorem etaleOpenScalarRestrictionTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K M : DerivedCategoryModule A X) :
    (scalarExtension φ U).map
        (openExactRestrictionTensor (ModuleCat.{u + 1} A) j K M).hom ≫
      (openScalarRestriction φ j).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj M) ≫
      (derivedRestriction (A := B) j).map (etaleHomTensorComparison X φ K M).inv =
    (etaleHomTensorComparison U φ
        ((derivedRestriction (A := A) j).obj K)
        ((derivedRestriction (A := A) j).obj M)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} B) U).map
        ((openScalarRestriction φ j).hom.app K)).app
          ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) U).obj
        ((derivedRestriction (A := B) j).obj ((scalarExtension φ X).obj K))).map
          ((openScalarRestriction φ j).hom.app M) ≫
      (openExactRestrictionTensor (ModuleCat.{u + 1} B) j
        ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj M)).hom := by sorry

end AlgebraicGeometry.Etale
