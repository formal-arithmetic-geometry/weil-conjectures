/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeDefs
import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantExchangeEncoding
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-! # Invertibility of the proper compactification factor

A component of the compactification product-projection argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Fix the intrinsic pro-etale localization, which uses the standard derived category.
attribute [local instance 50000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleAmbientRingedExchange
  proEtaleRingDerivedAdjunction proEtaleRingModuleDirectImage Functor.mapDerivedCategory

set_option maxRecDepth 4000 in
-- Compare exact realization and restriction without expanding their site models.
private theorem originRestriction (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    Nonempty (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A ⋙
      proEtaleDerivedModuleRestriction X A ≅
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory) := by
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X A
  exact ⟨(Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ Functor.rightUnitor _)⟩

private def productSquare {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) (T : Over S) :
    ChosenCartesianSquare (prod.fst : U ⨯ T ⟶ U).left
      (prod.map f (𝟙 T)).left f.left (prod.fst : V ⨯ T ⟶ V).left :=
  { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).toCommSq
    isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).isoPullback
    hom_fst := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_fst
    hom_snd := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_snd }

set_option maxRecDepth 4000 in
-- The identity-square encoding compares the two direct-image presentations.
private theorem directImageOrigin (A : Type u) [CommRing A]
    {X B : Scheme.{u}} (j : X ⟶ B) [QuasiCompact j] [QuasiSeparated j]
    (M : proEtaleDerivedCategory X A)
    (Lp : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (eMfixed : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj Lp.obj ≅
        (proEtaleDerivedModuleRestriction X A).obj M) :
    Nonempty ((proEtaleDerivedModuleRestriction B A).obj
      ((proEtaleConstantRingPushforward A j).rightDerivedFunctor.obj M) ≅
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) B).mapDerivedCategory.obj
            ((AlgebraicGeometry.Etale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).rightDerivedFunctorPlus.obj Lp).obj) := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let N := (proEtaleConstantRingPushforward A j).rightDerivedFunctor.obj M
  let Lnext := (AlgebraicGeometry.Etale.lowerStar C j).rightDerivedFunctorPlus.obj Lp
  let ps := IsPullback.id_horiz j
  let sqI : ChosenCartesianSquare (𝟙 X) j j (𝟙 B) :=
    { toCommSq := ps.toCommSq
      isoPullback := ps.isoPullback
      hom_fst := ps.isoPullback_hom_fst
      hom_snd := ps.isoPullback_hom_snd }
  obtain ⟨eI⟩ := proEtaleConstantExchange_encoding A sqI
    ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq (𝟙 X) j A)).trans
      ((congr_arg_heq
        (fun q : X ⟶ B ↦ proEtaleConstantRingComparison q A) sqI.w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
          j (𝟙 B) A)).symm)) M
  let eN : (proEtaleDerivedModuleRestriction B A).obj N ≅
      (ProEtale.comparisonUpperStar C B).mapDerivedCategory.obj Lnext.obj :=
    (proEtaleDerivedModuleRestriction B A).mapIso
        ((proEtaleStalkDerivedIdentityPullback A B).app N).symm ≪≫
      Arrow.leftFunc.mapIso eI ≪≫
      (ProEtale.leftDerivedUpperStarId C B).app _ ≪≫
      ((ProEtale.lowerStar C j).rightDerivedFunctor.mapIso eMfixed).symm ≪≫
      ((ProEtale.rightDerivedLowerStarComparisonIso' j C).app Lp).symm
  exact ⟨eN⟩

set_option maxRecDepth 4000 in
-- Transport the two predicates through the fixed-scalar comparison origin.
private theorem boundedClassicalOfOrigin (A : Type u) [CommRing A] (B : Scheme.{u})
    (N : proEtaleDerivedCategory B A)
    (Lnext : DerivedCategory.Plus
      (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (eN : (proEtaleDerivedModuleRestriction B A).obj N ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) B).mapDerivedCategory.obj Lnext.obj) :
    (∃ n : ℤ, DerivedCategory.IsGE N n) ∧ ProEtale.IsClassicalModuleComplex N := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hNb : ∃ n : ℤ, DerivedCategory.IsGE N n := by
    obtain ⟨n, hn⟩ := Lnext.property
    have hfixed : DerivedCategory.IsGE
        ((ProEtale.comparisonUpperStar C B).mapDerivedCategory.obj Lnext.obj) n := by
      have := hn
      exact (ProEtale.comparisonUpperStar C B).isGE_mapDerivedCategory_obj Lnext.obj n
    refine ⟨n, (proEtaleDerivedModuleRestriction_isGE_iff B A N n).mp ?_⟩
    have := hfixed
    exact DerivedCategory.TStructure.t.isGE_of_iso eN.symm n
  have hNc : ProEtale.IsClassicalModuleComplex N := by
    let : TopologicalSpace (ULift.{u + 1, u} A) := ⊥
    let : DiscreteTopology (ULift.{u + 1, u} A) := ⟨rfl⟩
    have hu := (ProEtale.boundedBelowComparison B (ULift.{u + 1, u} A)).1
    have hc := (ProEtale.classicalDerivedEquivalence B (ULift.{u + 1, u} A)
      (fun K ↦ by let := hu; infer_instance)).1 Lnext
    have hfixed := (proEtaleFixedClassical_iso_iff B (ULift.{u + 1, u} A)
      ((ProEtale.comparisonUpperStar C B).mapDerivedCategoryPlusCompatibility.app
        Lnext)).mp hc
    exact (proEtaleDerivedModuleRestriction_classical_iff B A N).mpr
      ((proEtaleFixedClassical_iso_iff B (ULift.{u + 1, u} A) eN).mpr hfixed)
  exact ⟨hNb, hNc⟩

private theorem torsionOfExponent (A : Type u) [CommRing A]
    (B : Scheme.{u}) (N : proEtaleDerivedCategory B A) (l : ℕ) (_hl : l.Prime)
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0) :
    ∀ q : ℤ, ((SheafOfModules.toSheaf _).obj
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules B (proEtaleConstantRing B A)) q).obj N)).IsTorsion := by
  obtain ⟨r, hr, hA⟩ := _hA
  have hpos : 0 < l ^ r := pow_pos _hl.pos r
  have hAu : ((l ^ r : ℕ) : ULift.{u + 1, u} A) = 0 := by
    apply (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).injective
    simpa only [map_natCast, map_zero] using hA
  intro q U s
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, ?_⟩
  intro V f hf
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨l ^ r, hpos, ?_⟩
  let H := (DerivedCategory.homologyFunctor
    (proEtaleRingModules B (proEtaleConstantRing B A)) q).obj N
  change (l ^ r) • (show ((proEtaleModuleRestriction B A).obj H).obj.obj
    (Opposite.op V) from _) = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1, u} A), hAu, zero_smul]

set_option maxRecDepth 4000 in
-- Keep the origin elimination independent of the final product-square exchange.
private theorem directImageBoundedClassical (A : Type u) [CommRing A] [Finite A]
    {X B : Scheme.{u}} (j : X ⟶ B) [QuasiCompact j] [QuasiSeparated j]
    (M : proEtaleDerivedCategory X A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).essImage M) :
    (∃ n : ℤ, DerivedCategory.IsGE
      ((proEtaleConstantRingPushforward A j).rightDerivedFunctor.obj M) n) ∧
      ProEtale.IsClassicalModuleComplex
        ((proEtaleConstantRingPushforward A j).rightDerivedFunctor.obj M) := by
  classical
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let N := (proEtaleConstantRingPushforward A j).rightDerivedFunctor.obj M
  obtain ⟨L, ⟨eM⟩⟩ := _hM
  have hLb : ∃ n : ℤ, DerivedCategory.IsGE L.obj n := by
    obtain ⟨a, b, hab, hv⟩ := L.property.2
    exact ⟨a, (DerivedCategory.isGE_iff L.obj a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  let Lp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology C) := ⟨L.obj, hLb⟩
  let Lnext := (AlgebraicGeometry.Etale.lowerStar C j).rightDerivedFunctorPlus.obj Lp
  let eMfixed := ((Classical.choice (originRestriction X A)).app L.obj).symm ≪≫
    (proEtaleDerivedModuleRestriction X A).mapIso eM
  obtain ⟨eN⟩ := directImageOrigin A j M Lp eMfixed
  obtain ⟨hNb, hNc⟩ := boundedClassicalOfOrigin A B N Lnext eN
  exact ⟨hNb, hNc⟩

set_option maxRecDepth 4000 in
-- Compare only the canonical specialization wrappers.
private theorem productExchange_eq (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S) :
    compactificationProductExchange A f T = classicalProEtaleExchange A (productSquare f T) := by
  rfl

set_option maxRecDepth 4000 in
-- The origin comparison involves the intrinsic derived-category instances.
/-- Invertibility of the proper exchange at the actual open direct image.

Source: latest blueprint det-tf-ibc-pasting.proof.md, steps 2 and 6; the existing
classical proper-base-change theorem applied to the canonical product square.
(blueprint: compactification-product-exchange-proper-isIso).

Proof: unpack the given etale origin L of M and record its lower bound. Let Lnext
be its etale direct image along j in D+. Constant exchange encoding for the square
with vertical maps j and horizontal identity maps, followed by the two normalized
identity pullbacks, identifies scalar restriction of N = Rj_* M with fixed-scalar
direct image of the restricted M. The intrinsic realization/restriction comparison
and the canonical qcqs direct-image comparison identify this with comparison(Lnext).
Exact comparison preserves the lower bound and constant restriction reflects it.
The classical derived equivalence makes comparison(Lnext) classical; transport
across the preceding isomorphism and restriction proves N classical. Every section
of every homology sheaf is killed by the positive integer l^r: after restriction
it is a module over ULift A. Thus its underlying additive sheaf is locally torsion.
Classical proper base change on the actual product square at N now gives exactly
the required intrinsic ambient exchange isomorphism. No completion is used. -/
theorem compactificationProductExchange_proper_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (j : X ⟶ B) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    IsIso ((compactificationProductExchange A p T).app
      ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M)) := by
  have h := directImageBoundedClassical A j.left M _hM
  rw [productExchange_eq]
  exact (isIso_classicalProEtaleExchange_of_isProper A (productSquare p T)
    ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M)
    h.1 h.2 (torsionOfExponent A B.left _ l _hl _hA)).2.2.2.2

end AlgebraicGeometry.Scheme
