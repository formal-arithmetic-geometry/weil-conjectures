/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedProperOpenScalar
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedPushScalarComposition
import WeilConjectures.CategoryTheory.SmoothPurity.UnitNormalizedLiftComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Combinatorics.Quiver.ReflQuiver
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste

/-! # Condensed compact-support refinement coherence

The constructions and their existing proved coherence laws are publicly imported
from the core module. The composition proof keeps the original normalized maps.
(blueprint: def-pur-condensed-compact-support-projection). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem fieldProperOpen_spec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
        fieldProperOpenRestriction Λ r K.obj =
      (fieldOpenAdjunction Λ c.i).unit.app K.obj :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose_spec

private meta def exactRefinementInstanceCongr : Tactic := fun stx =>
    withMainContext do
    let h := stx[1]
    let proof ← elabTerm h none
    let target ← instantiateMVars (← getMainTarget)
    let proofType ← instantiateMVars (← inferType proof)
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    let he ← instanceCongrHEq cache #[] 200 proofType target
    let e ← mkAppM ``eq_of_heq #[he]
    (← getMainGoal).assign (← mkAppM ``Eq.mp #[e, proof])

/-- Coefficient extension commutes with the original refinement map itself.
Source: blueprint proof Steps 15--16; proper/open coefficient mate pasting
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Coefficient restriction
commutes with the original open unit and the proper counit, so both transposes are
the same section-normalized restriction map. Uniqueness in the open Hom bijection
and the proper compositor identify the original maps. This applies verbatim to the
finite-valued closure coefficient and requires no new choice of comparison arrow. -/
theorem condensedProjection_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X))
    (hK : boundedConstructible (condensedRingObj Λ' X) ((condensedScalar a X).obj K.obj)) :
    (condensedScalar a Y).map ((fieldRefinement Λ r).app K) ≫
        (condensedProjection a c).app K.obj =
      (condensedProjection a d).app K.obj ≫
        (fieldRefinement Λ' r).app ⟨(condensedScalar a X).obj K.obj, hK⟩ := by
  have hproper := condensedPushScalar_refinement_factorization a r K
  have hopen := fieldProperOpen_scalar_pasting a r K hK
  let pasted := (condensedPushScalar a d.g).app
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
          ((condensedScalar a X).obj K.obj))
  calc
    _ = pasted := by exact_refinement_instance_congr hproper
    _ = _ := by exact_refinement_instance_congr hopen

attribute [local irreducible] fieldProperOpen fieldOpenAdjunction
  fieldProperOpenRestrictionNat
attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

section RefinementCompositionProof

attribute [local irreducible] fieldDerivedUpperStar fieldDerivedLowerStar
  fieldDerivedOpenShriek
  fieldDerivedPullComp fieldDerivedAdjunction
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek

attribute [local irreducible] conjugateEquiv conjugateIsoEquiv mateEquiv

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] fieldPushComp

attribute [local irreducible] counitRestrictionNat

end RefinementCompositionProof

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

end WeilConjectures.CompactSupportCondensedRealization

  fieldSheafGrothendieck
  fieldSheafBigColimits
  fieldSheafCoequalizers
  fieldSheafMonoidalPreadditive
  fieldModuleGrothendieck
  fieldModuleKInjectiveResolutions
  fieldModuleColimits
  fieldModuleBigColimits
  fieldSheafFlatResolution
  fieldModuleFlatResolution

attribute [instance 2000] fieldModuleCountableCoproducts fieldModuleIntegerColimits
  fieldModuleIntegerExactColimits fieldExtendScalarsKFlat

attribute [instance 2000] fieldSheafAbelian fieldModuleAbelian fieldModuleDerivedCategory
