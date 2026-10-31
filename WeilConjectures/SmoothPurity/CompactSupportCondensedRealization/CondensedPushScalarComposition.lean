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

/-- The proper coefficient square pasted with a compactification refinement.

Source: the proper-image mate pasting of compact-support realization Steps 15--16
(blueprint: lem-pur-condensed-push-scalar-composition).

Proof: the refinement component is the proper direct image of its normalized
open lift, followed by the pushforward compositor transported along `r.hom_g`.
The projection component is the proper scalar mate followed by the proper image
of the open scalar comparison. Expand these two component formulas and apply
functoriality of scalar extension. The proper scalar mate respects composition
of direct images: on the restriction side, both underived pastes are the same
section map, with the same coefficient action by coefficient naturality. Derive
this identity using the canonical right-derived comparisons; exact coefficient
restriction preserves K-injective complexes because its scalar-extension left
adjoint is exact. Uniqueness identifies these comparisons with the right-adjoint
mates of the pullback compositors, namely `fieldPushComp`. Taking scalar mates
therefore gives the proper coefficient compositor square. Transport it along
`r.hom_g` by equality induction. Substitute it into the expanded refinement
component. Naturality of `condensedPushScalar a d.g` moves the scalar image of
the normalized lift past that mate. Naturality of the target compositor in the
open scalar comparison moves that comparison before the compositor. Finally
combine the three maps inside the final proper direct image by functoriality.
This gives exactly the displayed paste. No scalar-extended constructibility
hypothesis or coefficient compatibility of the normalized lift is used here. -/
theorem condensedPushScalar_refinement_factorization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (condensedScalar a Y).map ((fieldRefinement Λ r).app K) ≫
        (condensedProjection a c).app K.obj =
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
              ((condensedScalar a X).obj K.obj)) := by sorry

end WeilConjectures.CompactSupportCondensedRealization
