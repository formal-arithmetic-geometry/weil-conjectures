/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
/-! # Composition of inverse images and coefficient units

Source: Stacks Project, Section 01F7, functoriality of pullback.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {X Y Z : Scheme.{u}}

/-- The coefficient morphism induced by the module pullback unit.
Source: Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def coefficientUnit (f : Y ⟶ X) (M : X.Modules) :=
  coeff f ((pullbackPushforwardAdjunction f).unit.app M)

/-- The inverse-image composition comparison, determined by the adjunctions.
Source: Mathlib `Adjunction.leftAdjointCompIso`; Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def invImageComp (g : Z ⟶ Y) (f : Y ⟶ X) :
    invImage f ⋙ invImage g ≅ invImage (g ≫ f) :=
  Adjunction.leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (g ≫ f).base)
    (Iso.refl _)

/-- Inverse images along equal morphisms identify.
Source: equality transport; Stacks Project, Section 01F7.
(blueprint: lem-pc-coefficient-unit-composition) -/
noncomputable def invImageCongr {f g : Y ⟶ X} (h : f = g) :
    invImage f ≅ invImage g := eqToIso (congrArg invImage h)

/-- Coefficient units compose under the canonical comparisons.
Source: Stacks Project, Section 01F7, functoriality of pullback.
(blueprint: lem-pc-coefficient-unit-composition)

Proof: Postcompose both sides with the forgotten inverse of pullbackComp g f.
This is an isomorphism, so it suffices to prove the resulting equality. Apply
the composite abelian inverse-image/direct-image adjunction to both morphisms.
The adjunct of the left hand side is the composite of the two module units,
after forgetting to abelian sheaves. The adjunct of the right hand side is
the unit for the composite followed by the inverse of the module pullback
composition comparison. These agree by pullbackUnit_comp_app on every open.
The abelian composition comparison is the unique left-adjoint comparison,
so its adjunct is precisely the composite abelian unit. Injectivity of the
adjunction hom equivalence proves the equality. This works for all morphisms,
including identities, empty schemes and zero modules.
-/
@[reassoc]
theorem coefficientUnit_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) :
    (invImage g).map (coefficientUnit f M) ≫
        coefficientUnit g ((pullback f).obj M) ≫
        (SheafOfModules.toSheaf Z.ringCatSheaf).map ((pullbackComp g f).hom.app M) =
      (invImageComp g f).hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≫
        coefficientUnit (g ≫ f) M := by sorry

end AlgebraicGeometry.Scheme.Modules
