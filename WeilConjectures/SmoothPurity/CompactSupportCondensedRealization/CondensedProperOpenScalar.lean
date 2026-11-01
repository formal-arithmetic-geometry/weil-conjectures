/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore

/-! # Coefficient compatibility for a constituent of compact-support refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local instance] fieldSheafAbelian
attribute [local instance] fieldSheafGrothendieck
attribute [local instance] fieldSheafBigColimits
attribute [local instance] fieldSheafCoequalizers
attribute [local instance] fieldSheafMonoidalPreadditive
attribute [local instance] fieldModuleAbelian
attribute [local instance] fieldModuleGrothendieck
attribute [local instance] fieldModuleKInjectiveResolutions
attribute [local instance] fieldModuleDerivedCategory
attribute [local instance] fieldModuleColimits
attribute [local instance] fieldModuleBigColimits
attribute [local instance] fieldSheafFlatResolution
attribute [local instance] fieldModuleFlatResolution
attribute [local instance] fieldModuleCountableCoproducts
attribute [local instance] fieldModuleIntegerColimits
attribute [local instance] fieldModuleIntegerExactColimits
attribute [local instance] fieldTensorColimits
attribute [local instance] fieldTensorColimitsRight
attribute [local instance] fieldGradedTensor
attribute [local instance] fieldGradedFour
attribute [local instance] fieldGradedLeft
attribute [local instance] fieldGradedRight
attribute [local instance] fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible] condensedScalar condensedPushScalar condensedOpenScalar
  CondensedRing.lowerStar CondensedRing.upperStar CondensedRing.openImmersionLowerShriek
  fieldPushComp fieldProperOpen

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] [FlatCoefficientMap a]

/-- Pasting coefficient compatibility of the normalized proper/open lift.

Source: the proper/open coefficient mate argument of compact-support realization
Steps 15--16 (blueprint: lem-pur-condensed-proper-open-scalar).

Proof: compare the normalized lift after scalar extension with the normalized
lift for the scalar-extended bounded constructible object. Precompose the former
with the inverse open scalar comparison for `d.i` and transpose under the open
adjunction with coefficients `Λ'`. The open scalar mate equation carries the
original open unit to the new open unit. The proper scalar mate equation carries
the original proper counit to the new proper counit. Restriction of coefficients
commutes with the pullback composition comparison associated to `r.i_hom`.
Consequently the transpose, followed by `fieldProperOpenRestriction Λ' r`, is
the new open unit. Uniqueness of the normalized lift at
`⟨(condensedScalar a X).obj K.obj, hK⟩` identifies it with the chosen new lift.
Cancel the inverse open comparison. This proves that the three morphisms inside
the proper direct image in the displayed left side equal the open comparison
for `d.i` followed by the new normalized lift. Apply the proper direct image to
that equality, precompose with the proper scalar mate for `d.g`, and postcompose
with the specified target pushforward compositor. Functoriality separates the
two factors inside that image. The first resulting factor is the component of
`condensedProjection a d`; the second is the component of `fieldRefinement Λ' r`
at the scalar-extended object, by their definitions. Associativity gives the
claimed equality. No invertibility of a proper scalar comparison is assumed. -/
theorem fieldProperOpen_scalar_pasting {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedPushScalar a d.g).app
          ((CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj) ≫
        (CondensedRing.lowerStar Λ' d.g).rightDerivedFunctor.map
          ((condensedScalar a d.Z).map (fieldProperOpen Λ r K) ≫
            (condensedPushScalar a r.hom).app
              ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
            (CondensedRing.lowerStar Λ' r.hom).rightDerivedFunctor.map
              ((condensedOpenScalar a c.i).hom.app K.obj)) ≫
        ((fieldPushComp Λ' r.hom d.g).hom ≫
          eqToHom (congrArg (fieldDerivedLowerStar Λ') r.hom_g)).app
            ((CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory.obj
              ((condensedScalar a X).obj K.obj)) =
      (condensedProjection a d).app K.obj ≫
        (fieldRefinement Λ' r).app ⟨(condensedScalar a X).obj K.obj, hK⟩ := by sorry

end WeilConjectures.CompactSupportCondensedRealization
