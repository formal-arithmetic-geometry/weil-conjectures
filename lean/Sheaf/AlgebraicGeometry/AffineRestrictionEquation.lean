/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
public import Sheaf.AlgebraicGeometry.AffinePullbackCoefficientMap

/-! # Evaluation equation for the affine restriction -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  moduleAbelianCohomologyLarge coherentEtaleMap
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  etaleTensorSectionsRestriction
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The affine restriction is the map of its prescribed tensor adjunction.
Source: Stacks Project, Tags 03Q8 and 01FD.
(blueprint: lem-weil-pbc-affine-restriction-equation).
Proof: unfold the affine restriction and the chart arrow to identify the same
generic tensor-composition restriction. Apply its coefficient-map equation,
rewrite the constructed affine coefficient map by its defining equation, and
pass these equalities through the tensor adjunction and module cohomology map.
Evaluate the resulting equality of morphisms at the given class. -/
theorem affineRealizationRestriction_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V)
    (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) :
    affineRealizationRestriction f G q h x =
      moduleCohomologyFMap (affineRealizationChartMap f h)
        ((Classical.choose
          (exists_tensorPullbackAdjunction (affineRealizationChartMap f h))).homEquiv
          _ _ (affineRealizationCoefficientMap f G h)) q x := by
  have hres : affineRealizationRestriction f G q h =
      tensorCompositeCohomologyRestriction (affineRealizationChartMap f h)
        (pullback.snd V.hom f) (pullback.snd V'.hom f)
        (affineRealizationChartMap_w f h) G q := by
    unfold affineRealizationRestriction affineRealizationChartMap
    rfl
  have hc := congrArg (fun ψ ↦ moduleCohomologyFMap (affineRealizationChartMap f h)
    ((Classical.choose
      (exists_tensorPullbackAdjunction (affineRealizationChartMap f h))).homEquiv _ _ ψ) q)
    (affineRealizationCoefficientMap_eq f G h)
  exact ConcreteCategory.congr_hom
    (hres.trans ((tensorCompositeCohomologyRestriction_eq_coefficient
      (affineRealizationChartMap f h)
      (pullback.snd V.hom f) (pullback.snd V'.hom f)
      (affineRealizationChartMap_w f h) G q).trans hc.symm)) x

end
end AlgebraicGeometry.Scheme.Modules
