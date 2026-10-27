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

/-- Evaluation commutes with a coefficient morphism after cancelling the Ext comparison.
Source: Stacks Project Tags 03FD and 01FT.
(blueprint: new-unit-coherent-raw-evaluation-formula-map-aux). -/
theorem unit_evaluation_map_symm {Y : Scheme.{u}}
    {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (k : A ⟶ B) (q : ℕ)
    (t : (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A))) :
    Etale.sheafHToDerived B q
        (Sheaf.H.map k q ((Etale.sheafHDerivedEquiv A q).symm t)) =
      (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map k)) t := by
  let e := Etale.sheafHDerivedEquiv A q
  have hfun : (e : Sheaf.H A q → _) = Etale.sheafHToDerived A q := by
    unfold e Etale.sheafHDerivedEquiv
    rfl
  have he : Etale.sheafHToDerived A q (e.symm t) = t :=
    (congrFun hfun (e.symm t)).symm.trans (e.apply_symm_apply t)
  exact (Etale.sheafHToDerived_map k q (e.symm t)).trans
    (congrArg (fun y => (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map k)) y) he)



end
end AlgebraicGeometry.Scheme.Modules
