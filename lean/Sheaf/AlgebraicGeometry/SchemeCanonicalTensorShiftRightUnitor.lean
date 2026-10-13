/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift

/-! # The canonical tensor shift and the right unitor

Source: Stacks Project, Tag 06YH, total tensor localization and the Koszul unitor identity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-right-unitor).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- On a K-flat representative the canonical first-variable tensor shift commutes with
 the right unitor in degree one.
Source: Stacks Project, Tag 06YH, derived tensor localization;
WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift,
CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom;
WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor,
DerivedCategory.rightUnitor_commShift (the same representative argument,
with an arbitrary K-flat first factor and independent universes).
(blueprint: lem-sc-scheme-canonical-tensor-shift-right-unitor).

Proof. Let U be the unit complex, concentrated in degree zero. For a K-flat P,
the tensor localization comparison Q(P) tensor Q(U) to Q(P tensor U) is invertible.
The derived right unitor at Q(P) is this comparison followed by the localization
of the complex right unitor, with the localization unit identification inserted.
This is the right-unit identity of the lax monoidal localization functor.
The defining shift square for the localized two-variable tensor comparison,
specialized to P and U, relates the derived first-variable shift to the complex
Koszul shift. In each summand of the total tensor complex with U, its second degree
is zero, so the Koszul sign for translation of the first variable is one.
Thus the complex right unitor commutes with that shift. Apply localization to
this equality and substitute the right-unit identity into the comparison square.
Naturality of the right unitor cancels the shift comparison for the inclusion of
K-flat complexes; naturality in the second variable absorbs the unit identification.
Cancel the invertible tensor localization comparison and localization shift maps.
The resulting equation is exactly the displayed square, with the usual shift of
the identity functor. All comparisons restrict to the unique morphism on zero
objects, so this also covers P zero and the empty scheme. -/
theorem schemeCanonicalTensorShift_rightUnitor (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    letI := schemeCanonicalTensorShift Y
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      let K := DerivedCategory.Q.obj P
      let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
      ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
          (τ.app K)⟦(1 : ℤ)⟧' =
        τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
          (1 : ℤ)).hom.app K := by sorry

end AlgebraicGeometry
