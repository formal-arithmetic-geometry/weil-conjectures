/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.SheafHDerivedPullback
import Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionComposition
import Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormulaAux
import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization

/-! # Derived restriction and the structural etale pullback

Source: Stacks Project, Tags 03Q8, 03FD, 01FT and 03DR.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] tensorPullback tensorPullbackObj tensorSectionsComp
  tensorSectionsUnit qcoherentPullbackSection
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  coherentEtaleRestrictionIso affineRealizationRawEvaluation affineRealizationRawEquiv
  Etale.rawRestrictedCohomologyComparison Etale.rawAffineComplexPullback
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Functor.rightDerived CategoryTheory.Functor.rightDerivedFunctor
  Etale.cohomologyMap CategoryTheory.Sheaf.H.map CategoryTheory.Adjunction.homEquiv
  Etale.upperStar Etale.cohomology
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- Raw evaluation intertwines chart restriction with structural etale pullback,
before the normalized comparison with ordinary module cohomology.
The section formula pins down the coefficient map. No affine, compactness,
quasi-compactness or separatedness assumption is used.
Source: Stacks Project, Tag 03Q8 (lemma-higher-direct-images), Tag 03FD
(lemma-cohomology-modules-abelian-agree), Tag 01FT
(section-cohomology-sheaves), and Tag 03DR (section-quasi-coherent-sheaves).
Agent expansion of the presentation-and-coefficient square in the parent proof.
(blueprint: lem-weil-pbc-affine-raw-evaluation-pullback).

Proof: The naturality equation of rawRestrictedClassNormalization identifies the
raw comparison of the restricted class with normalizationCohomologyRestriction
of its comparison. Expand the latter as derived chart pullback followed by the
inverse-image composition coefficient map. The fixed Ext-to-derived comparison
evaluates the represented class at the integer generator. Derived adjunction-unit
naturality, compatibility with shifts, and derivedSectionPullback_single_unit
identify pullback of that evaluation with evaluation of cohomologyMap: the
constant-sheaf generator pulls back to the generator. Coefficient naturality
identifies the derived single coefficient map with Sheaf.H.map. Transport on
each chart by coherentEtaleRestrictionIso. Its etale section formula is inverse
tensor-section composition. Naturality of the tensor adjunction unit,
associativity of unit-normalized tensorSectionsComp, and b.w cancel the
intermediate comparisons. The resulting coefficient map on sections is exactly
qcoherentPullbackSection for psi. The hypothesis htheta identifies theta with
this map by extensionality; etale inverse image is localization restriction.
Compose these squares and cancel the inverse fixed evaluation equivalences.
This proves the equation without using any coherent-to-ordinary comparison.
The same unit and composition equations apply to empty charts, zero modules,
and q=0. -/
theorem affineRealizationRawEvaluation_pullback {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (V V' : S.Etale) (h : V' ⟶ V)
    (θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')))
    (hθ : let b := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h
      let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
          affineRealizationCoefficient f G V' :=
        (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
          eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
      ∀ (U : (Limits.pullback V.hom f : Scheme.{u}).Etale)
        (s : (etaleTensorSectionsSheaf (affineRealizationCoefficient f G V)).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection b.left _ _ ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b.left).obj U)
            (pullback.fst U.hom b.left) pullback.condition s))
    (q : ℕ)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    affineRealizationRawEvaluation f G q V'
      ((Etale.abelianHigherDirectImageRawPresheaf f q
        (liftedCoherentEtaleSheaf G)).map h.op z) =
      Sheaf.H.map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).homEquiv
          _ _ |>.symm θ) q
        (Etale.cohomologyMap
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left
          (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q
          (affineRealizationRawEvaluation f G q V z)) := by
  let F := liftedCoherentEtaleSheaf G
  let b := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h
  let A := (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F
  let A' := (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V'.hom f)).obj F
  let e := coherentEtaleRestrictionIso (pullback.snd V.hom f) G
  let e' := coherentEtaleRestrictionIso (pullback.snd V'.hom f) G
  let c := (Etale.upperStarComp AddCommGrpCat.{u + 1} b.left
    (pullback.snd V.hom f) (pullback.snd V'.hom f) b.w.symm).inv.app F
  let a := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b.left).homEquiv
    _ _).symm θ
  let r := (Etale.sheafHDerivedEquiv A q).symm
    (Etale.rawRestrictedCohomologyComparison f q F V z)
  have hcoeff :=
    coherentEtaleRestrictionIso_composition f G V V' h θ hθ
  have hnorm := Etale.rawRestrictedClassNormalization f q F
  obtain ⟨k, hk⟩ := hnorm.1
  have hnmap := k.hom.naturality h.op
  rw [hk V', hk V, hnorm.2.1 V V' h] at hnmap
  have hn := ConcreteCategory.congr_hom hnmap z
  have hp := (congrArg (Etale.sheafHDerivedEquiv A' q).symm hn).trans
    (Etale.sheafHDerivedEquiv_symm_restriction f q F V V' h _)
  rw [unit_coherent_raw_evaluation_formula, unit_coherent_raw_evaluation_formula]
  refine (congrArg (Sheaf.H.map e'.hom q) hp).trans ?_
  calc
    _ = Sheaf.H.map (c ≫ e'.hom) q (Etale.cohomologyMap b.left A q r) :=
      (Sheaf.H.map_comp_apply c e'.hom _).symm
    _ = Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} b.left).map e.hom ≫ a)
        q (Etale.cohomologyMap b.left A q r) := congrArg (fun t ↦
          Sheaf.H.map t q (Etale.cohomologyMap b.left A q r)) hcoeff.symm
    _ = _ := (Sheaf.H.map_comp_apply _ a _).trans
      (congrArg (Sheaf.H.map a q) (Etale.cohomologyMap_map b.left q e.hom r).symm)


end
end AlgebraicGeometry.Scheme.Modules
