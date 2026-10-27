/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnitScalarRawData
import Sheaf.AlgebraicGeometry.SheafHDerivedNaturality
import all Mathlib.Logic.Small.Defs

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  Etale.sheafHToDerived Etale.sheafHDerivedEquiv
  Etale.rawRestrictedCohomologyComparison coherentEtaleRestrictionIso
  unitStructureCoefficientIso Etale.cohomology Etale.upperStar
  RingedSpace.moduleCohomology CoherentEtale.Coeff tensorPullback tensorPullbackObj
  CategoryTheory.derivedExtEvaluation unitLocalizedCoefficientIso unitCoherentRawClass
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem equiv_comp_apply {A B D E : AddCommGrpCat.{u + 1}}
    (r : A ⟶ B) [IsIso r] (e : D ≃+ B) (k : D ≅ E) (z : A) :
    ((asIso r).addCommGroupIsoToAddEquiv.trans
      (e.symm.trans k.addCommGroupIsoToAddEquiv)) z = k.hom (e.symm (r z)) := by
  rfl

/-- The raw evaluation is the explicit restriction map after the inverse Ext comparison.
Source: Stacks Project Tags 03Q8, 03FD and 01FT.
(blueprint: new-unit-coherent-raw-evaluation-formula-aux). -/
theorem unit_coherent_raw_evaluation_formula {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (U : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op U)) :
    affineRealizationRawEvaluation f G q U z =
      Sheaf.H.map (coherentEtaleRestrictionIso (pullback.snd U.hom f) G).hom q
        ((Etale.sheafHDerivedEquiv
          ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
            (liftedCoherentEtaleSheaf G)) q).symm
          (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) U z)) := by
  let _ := Etale.isIso_rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) U
  unfold affineRealizationRawEvaluation affineRealizationRawEquiv
  exact equiv_comp_apply _ _ _ _




end
end AlgebraicGeometry.Scheme.Modules
