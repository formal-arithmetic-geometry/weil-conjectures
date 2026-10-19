/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.LfpTensorSingle
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Sheaf.Paper.IntegralLfpConstantModelComparison
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Field.ULift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
/-!
# Tensor of integral constructible sheaves in degree zero

Source: blueprint main-20261015, sk-lem-integral-models-operations,
parent proof steps 4--7 (blueprint: lem-sfb-integral-models-sheaf-tensor).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.upperStar AlgebraicGeometry.ProEtale.CondensedRing.upperStar

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj CondensedRing

private theorem constantModel_iff_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) :
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M ↔
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) M := by
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := coefficientMap φ X
  have hp := integralLfpConstantModelComparison ℓ (ULift.{u} E.val) X
    ((Mod.comap ψ).obj M)
  refine (constantModel_comap_iff φ X M).symm.trans (hp.symm.trans ?_)
  constructor
  · intro h
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
        Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)
  · exact _root_.constructible_comap ψ


namespace CondensedRing

attribute [-instance] monoidalCategory_cochainComplex monoidalCategoryStruct_cochainComplex in
private theorem constructible_tensor_single_noetherian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X) G) :
    boundedConstructible (condensedRingObj Λ X)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) := by
  classical
  let R := condensedRingObj Λ X
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨S, hS⟩ := common_lfp_stratification hF hG
  let H (a : Fin S.n) := upperStar Λ (S.immersion a)
  have lfp (a : Fin S.n)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : IsLocallyFinitelyPresented
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) ((H a).obj M) := by
    unfold H CondensedRing.upperStar
    dsimp only [Functor.comp_obj]
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)).symm
      (localFinitePresentation_comap
        (asIso (condensedPullbackHom Λ (S.immersion a))).inv hM)
  let ec (a : Fin S.n) := leftDerivedUpperStarIsoMapDerivedCategory Λ (S.immersion a)
  let es (a : Fin S.n) := (H a).mapDerivedCategorySingleFunctor 0
  let et (a : Fin S.n) := ((leftDerivedUpperStarTensorIso Λ (S.immersion a)).app
    ((DerivedCategory.singleFunctor _ 0).obj F)).app
      ((DerivedCategory.singleFunctor _ 0).obj G)
  have he (a : Fin S.n) : Nonempty ((H a).mapDerivedCategory.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H a).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H a).obj G)) :=
    ⟨(ec a).symm.app K ≪≫ et a ≪≫ tensorIso (C := DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
      (condensedRingObj Λ (S.domain a))))
      ((ec a).app ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫ (es a).app F)
      ((ec a).app ((DerivedCategory.singleFunctor _ 0).obj G) ≪≫ (es a).app G)⟩
  let e (a : Fin S.n) := Classical.choice (he a)
  have hlocal (a : Fin S.n) :
      TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.noetherianSpace
  have hom_lfp (a : Fin S.n) (n : ℤ) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
        ((H a).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_iso
      ((H a).mapDerivedCategoryHomologyFunctorIso n |>.app K).symm
    apply localFinitePresentation_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso (e a)).symm
    exact (lfp_tensor_single Λ (S.domain a) ((H a).obj F) ((H a).obj G)
      (lfp a F (hS a).1) (lfp a G (hS a).2)).2 n
  have detect
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hM : ∀ a : Fin S.n, IsZero ((H a).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply Mod.hom_ext
    apply abDetectMaps S.immersion
    · intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨a, S.range_immersion a |>.symm ▸ ha⟩
    · intro a
      let e' := (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)
      have hm := hM a
      unfold H CondensedRing.upperStar at hm
      dsimp only [Functor.comp_obj] at hm
      have hz := (Mod.forget _).map_isZero (hm.of_iso e'.symm)
      change IsZero ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj M.X) at hz
      simpa using hz.eq_of_src
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map (𝟙 M.X)) 0
  have hupper : K.IsLE (0 : ℤ) := DerivedCategory.isLE_tensor
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G) 0 0
  have hK : boundedConstructible R K := by
    apply (mem_boundedConstructible_iff R K).2
    constructor
    · refine ⟨-1, 0, fun n hn ↦ ?_⟩
      rcases hn with hn | hn
      · apply detect
        intro a
        have hb := (lfp_tensor_single Λ (S.domain a) ((H a).obj F) ((H a).obj G)
          (lfp a F (hS a).1) (lfp a G (hS a).2)).1
        have hz := (DerivedCategory.isGE_iff _ (-1)).1 hb n hn
        exact hz.of_iso
          (((H a).mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
            (DerivedCategory.homologyFunctor _ n).mapIso (e a))
      · exact (DerivedCategory.isLE_iff K 0).1 hupper n hn
    · intro n
      refine ⟨S, fun a ↦ ?_⟩
      apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
      apply localFinitePresentation_of_iso
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _)
      simpa only [H, upperStar, Functor.comp_obj] using hom_lfp a n
  exact hK

attribute [-instance] monoidalCategory_cochainComplex monoidalCategoryStruct_cochainComplex in
/-- The derived tensor of two integral constructible sheaves is bounded constructible.
Source: blueprint main-20261015, integral-models-operations proof, tensor paragraph,
parent proof steps 4--7 (blueprint: lem-sfb-integral-models-sheaf-tensor).

Proof: transport coefficients along the integral coefficient isomorphism and use
integralLfpConstantModelComparison to identify constant-model constructibility with
the existing stratified local finite presentation predicate. Take a common finite
stratification of the two sheaves. On every stratum, Cartesian inverse image is
exact and monoidal, so it carries their degree-zero tensor to the tensor of their
restrictions. The existing lfp_tensor_single theorem gives lower bound -1 and
locally finitely presented cohomology on each stratum. Exact inverse image commutes
with homology. The jointly surjective finite family of stratum immersions detects
zero sheaves, so the lower bound holds globally. General right t-exactness gives
upper bound 0. The common stratification witnesses constructibility of each
cohomology sheaf; transport back through the integral coefficient comparison gives
finite constant scalar models. Empty strata, zero modules, and identity restrictions
are covered by the same comparisons and zero detection. -/
theorem integralModels_sheaf_tensor (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) [IsNoetherian X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))
    (hF : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X F)
    (hG : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X G) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
      (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  classical
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have hTensor : derivedTensor Λ X =
      MonoidalCategory.curriedTensor (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))) := rfl
  rw [hTensor]
  have hF' := (constantModel_iff_constructible ℓ E X F).mp hF
  have hG' := (constantModel_iff_constructible ℓ E X G).mp hG
  have hK := constructible_tensor_single_noetherian Λ X F G hF' hG'
  exact ⟨hK.1, fun n ↦ (constantModel_iff_constructible ℓ E X _).mpr (hK.2 n)⟩

end CondensedRing

end AlgebraicGeometry.ProEtale
