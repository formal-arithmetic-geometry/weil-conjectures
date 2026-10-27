/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.UnitScalarRawData
import Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormula
public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso
public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization
import Sheaf.AlgebraicGeometry.SheafHDerivedNaturality
public import Sheaf.AlgebraicGeometry.UnitLocalizedScalarConjugation

/-! # Raw evaluation after the canonical unit coefficient identification -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  Etale.rawRestrictedCohomologyComparison Etale.abelianHigherDirectImageClass
  affineRealizationRawEvaluation affineRealizationClass affineRealizationRawEquiv
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  coherentEtaleRestrictionIso unitLocalizedCoefficientIso unitStructureCoefficientIso
  coherentEtaleMap CoherentEtale.Coeff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat


/-- Canonical classes commute with the explicit unit coefficient identification.
Source: Stacks Project, Tag 03Q8.
(blueprint: new-unit-scalar-raw-evaluation).
Proof: specialize coefficient naturality of the canonical raw class map to the
inverse of the explicit unit isomorphism. Evaluation and its inverse cancel in
affineRealizationClass_rawEvaluation. -/
theorem unitCoherentRawClass_class {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (U : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q X.etaleAdditiveSheaf).obj (op U)) :
    (Etale.normalizationHigherCoefficient f q (unitStructureCoefficientIso X).inv).hom.app
        (op U) (Etale.abelianHigherDirectImageClass f q X.etaleAdditiveSheaf U z) =
      affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) q U
        (affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) q U
          (unitCoherentRawClass f q U z)) := by
  have hr := affineRealizationClass_rawEvaluation f
    (SheafOfModules.unit X.ringCatSheaf) q U (unitCoherentRawClass f q U z)
  apply Eq.trans ?_ hr.symm
  have h := ((Etale.rawRestrictedClassNormalization f q X.etaleAdditiveSheaf).2.2.2.2.2
    _ (unitStructureCoefficientIso X).inv).2.2.1
  exact (congrArg (fun k ↦ k.app (op U) z) h).symm







/-- A scalar relation in restricted structural cohomology becomes multiplication
on the canonical coherent Ext classes, after the explicit coefficient identification.
Source: Stacks Project, Tags 03Q8, 03P2, 0096 and 0097.
(blueprint: new-unit-scalar-raw-evaluation).
Proof: write j for the projection of the chart to X and r for the pullback of a.
The normalized coherent restriction isomorphism composed with j inverse image of
the inverse unit coefficient isomorphism identifies structural functions with the
coherent pulled-back unit. On an etale test object T, the first map is the inverse
of the tensor-unit structure map for T→X and the second is the inverse tensor
composition map. Both are linear over Γ(T,O_T). Hence the prescribed scalar μ
conjugates to coherentEtaleMap of multiplication by r: pullback of multiplication
by r is multiplication by its image in Γ(T,O_T), by adjunction unit naturality.
The section-normalized restriction isomorphism and the coefficient maps are
natural, so these section identities give an equality of sheaf morphisms.
Apply derived cohomology. Coefficient naturality of raw comparison carries the
hypothesized equality through j inverse image of the inverse unit isomorphism.
Coefficient naturality of sheafHToDerived and its bijectivity carry the resulting
equality back to Ext; compose with coherent restriction. This is precisely the
forward map in affineRealizationRawEquiv. Empty charts and zero scalars require
no exception: every map and equality above remains defined. -/
theorem unitCoherentRawClass_scalar {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (a : Γ(U.left, ⊤))
    (μ : (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
      X.etaleAdditiveSheaf ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
        X.etaleAdditiveSheaf)
    (hμ : ∀ (T : (Limits.pullback U.hom f).Etale)
      (x : ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
        X.etaleAdditiveSheaf).obj.obj (op T)),
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
        (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app
          (op T)) (μ.hom.app (op T) x) =
        ULift.up (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a) *
          (@id Γ(T.left, ⊤) ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
            (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app
              (op T)) x).down)))
    (z z' : (Etale.abelianHigherDirectImageRawPresheaf f 1 X.etaleAdditiveSheaf).obj (op U))
    (hz : Etale.rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
      (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom f) (1 : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ))
          (Etale.rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z)) :
    affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) 1 U
        (unitCoherentRawClass f 1 U z') =
      Sheaf.H.map (coherentEtaleMap _ _
        ((affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) U).smulHom
          ((pullback.fst U.hom f).appTop a))) 1
        (affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) 1 U
          (unitCoherentRawClass f 1 U z)) := by
  let _ : (affineRealizationCoefficient f
      (SheafOfModules.unit X.ringCatSheaf) U).IsQuasicoherent :=
    isQuasicoherent_tensorPullback (pullback.snd U.hom f)
      (SheafOfModules.unit X.ringCatSheaf)
  let j := pullback.snd U.hom f
  let K := liftedCoherentEtaleSheaf (affineRealizationCoefficient f
    (SheafOfModules.unit X.ringCatSheaf) U)
  let C := Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom f) (1 : ℤ)
  let Q := CochainComplex.singleFunctor
    (Sheaf (Limits.pullback U.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      DerivedCategory.Q ⋙ C
  let e := unitLocalizedCoefficientIso j
  let m := coherentEtaleMap _ _
    ((affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) U).smulHom
      ((pullback.fst U.hom f).appTop a))
  have hm : μ ≫ e.hom = e.hom ≫ m := by
    change μ ≫ (unitLocalizedCoefficientIso (pullback.snd U.hom f)).hom =
      (unitLocalizedCoefficientIso (pullback.snd U.hom f)).hom ≫ _
    apply unitLocalizedCoefficientIso_scalar (pullback.snd U.hom f)
      ((pullback.fst U.hom f).appTop a) μ
    intro T x
    have h := hμ T x
    have hs : (T.hom ≫ pullback.fst U.hom f).appTop a =
        T.hom.appTop ((pullback.fst U.hom f).appTop a) := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [hs] at h
    exact h
  apply (Etale.sheafHToDerived_bijective K 1).1
  rw [Etale.sheafHToDerived_map, unitCoherentRawClass_evaluation,
    unitCoherentRawClass_evaluation, hz]
  have h := congrArg Q.map hm
  simp only [Q.map_comp] at h
  exact ConcreteCategory.congr_hom h
    (Etale.rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z)

end
end AlgebraicGeometry.Scheme.Modules
