/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Sheaf.Paper.CompletedConstructibleReductionControl
import Sheaf.Paper.LevelwiseAdicTruncations
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import Sheaf.Paper.NormalizedEtaleOriginWitnesses
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.PbcActualStrictPullback

/-! # Constructible preservation with the original adic coefficient datum

The coefficient ring has the same universe as the module sheaves, with no lift or
replacement of the datum. Source: Stacks 09C7 and 09C2; blueprint preservation proposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem intrinsicComplete_of_iso
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : PbcCompletedDerived T d} (e : K ≅ L)
    (hK : PbcIsIntrinsicallyComplete T d K) : PbcIsIntrinsicallyComplete T d L := by
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison T d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

private theorem actualPush_intrinsicComplete
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived S d) (hK : PbcIsIntrinsicallyComplete S d K) :
    PbcIsIntrinsicallyComplete T d ((pbcActualDerivedPush f d).obj K) := by
  let P : ObjectProperty (PbcCompletedDerived S d) := PbcIsIntrinsicallyComplete S d
  let Q : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let a := Adjunction.ofIsRightAdjoint P.ι
  let b := Adjunction.ofIsRightAdjoint Q.ι
  have : IsIso ((pbcActualCompletionUnit d S).app K) :=
    a.isIso_unit_app_iff_mem_essImage.mpr ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩
  have he := (pbcActualDirectCompletionIso_exists f d).exists.choose_spec K
  change (pbcActualCompletionUnit d T).app ((pbcActualDerivedPush f d).obj K) ≫
    (pbcActualDirectCompletionIso f d).hom.app K = _ at he
  have : IsIso ((pbcActualCompletionUnit d T).app
      ((pbcActualDerivedPush f d).obj K) ≫
        (pbcActualDirectCompletionIso f d).hom.app K) := by
    rw [he]
    infer_instance
  have : IsIso ((pbcActualCompletionUnit d T).app
      ((pbcActualDerivedPush f d).obj K)) :=
    IsIso.of_isIso_comp_right _ ((pbcActualDirectCompletionIso f d).hom.app K)
  have : IsIso (b.unit.app ((pbcActualDerivedPush f d).obj K)) := by
    change IsIso ((pbcActualCompletionUnit d T).app ((pbcActualDerivedPush f d).obj K))
    infer_instance
  obtain ⟨L, ⟨e⟩⟩ := b.mem_essImage_of_unit_isIso ((pbcActualDerivedPush f d).obj K)
  exact intrinsicComplete_of_iso T d e L.property

private theorem datumPush_eq_actualPush
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    d.push f = pbcActualDerivedPush f d := by
  have hm : proEtaleRingModuleDirectImage f (d.completedRing T) (d.completedRing S)
      (d.integralRingIso f) = completedModuleDirectImage f d := by
    unfold proEtaleRingModuleDirectImage completedModuleDirectImage
    unfold proEtaleRingDirectImageMap completedCoefficientDirectImageMap
    rw [cbcDatumCoefficient_eq]
    rfl
  cases hm
  rfl

private theorem datumPush_intrinsicComplete
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived S d) (hK : PbcIsIntrinsicallyComplete S d K) :
    PbcIsIntrinsicallyComplete T d ((d.push f).obj K) := by
  rw [datumPush_eq_actualPush]
  exact actualPush_intrinsicComplete f d K hK

private theorem datumPull_intrinsicComplete
    {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    PbcIsIntrinsicallyComplete S d ((d.completedPull f).obj K) := by
  let L : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d) := ⟨K, hK⟩
  let e := (pbcActualCompletedPullback_tower d f).exists.choose
  exact intrinsicComplete_of_iso S d
    ((e.app L).symm ≪≫ (cbcDatumActualStrictTransport d f).app K)
    (pbcActualCompletedPull_isComplete f d K)


private theorem boundedBelow_of_exact_faithful
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (K : DerivedCategory C)
    (hK : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := hK
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  intro i hi
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.isGE_iff _ a).1 ha i hi)

private theorem compatibleOrigins_of_levelwise
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d)
    (M : ∀ n : ℕ, ProEtale.PbcWitnessAmbient T d n)
    (hM : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
      ((ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj
        (M n)))
    (W : ∀ n : ℕ, EtaleOriginWitness T (ProEtale.PbcQuotient d n)
      ⟨(ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj
        (M n), hM n⟩)
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (M n) ≅
      (pbcCompletedReduction T d n).obj K) : PbcHasCompatibleEtaleOrigins T d K := by
  classical
  let theta (n : ℕ) : (ProEtale.pbcWitnessReduction T d n).obj (M (n + 1)) ≅ M n :=
    (pbcDerivedFunctionRealization T d n).preimageIso
      ((pbcFunctionReduction T d n).symm.app (M (n + 1)) ≪≫
        (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
          (e (n + 1)) ≪≫
        pbcReductionNormalization (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K ≪≫ (e n).symm)
  have lift (n : ℕ) :
      ∃ beta : (ProEtale.pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj ≅
          (W n).L.obj,
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T).mapDerivedCategory.map beta.hom ≫
            (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d n)
              (M n) (hM n) (W n)).hom =
          (ProEtale.pbcComparisonReduction T
            (ProEtale.pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
              (W (n + 1)).L.obj ≫
            (ProEtale.pbcWitnessReduction T d n).map
              (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d (n + 1))
                (M (n + 1)) (hM (n + 1)) (W (n + 1))).hom ≫ (theta n).hom := by
    let C := (ProEtale.pbcWitnessEtaleReduction T d n).obj (W (n + 1)).L.obj
    let F := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T).mapDerivedCategory
    let a : F.obj C ≅ M n :=
      (ProEtale.pbcComparisonReduction T
        (ProEtale.pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).symm.app
          (W (n + 1)).L.obj ≪≫
        (ProEtale.pbcWitnessReduction T d n).mapIso
          (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d (n + 1))
            (M (n + 1)) (hM (n + 1)) (W (n + 1))) ≪≫ theta n
    have hC : DerivedCategory.TStructure.t.plus C := by
      apply boundedBelow_of_exact_faithful (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T)
      apply boundedBelow_of_exact_faithful
        (ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n))
      exact DerivedCategory.TStructure.t.plus.prop_of_iso
        ((ProEtale.finiteCoefficientRealization T
          (ProEtale.PbcQuotient d n)).mapDerivedCategory.mapIso a).symm (hM n)
    let b : F.obj C ≅ F.obj (W n).L.obj :=
      a ≪≫ (ProEtale.pbcFixedOriginAlpha T (ProEtale.PbcQuotient d n)
        (M n) (hM n) (W n)).symm
    obtain ⟨f, hf⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C (W n).L.obj
        (W n).L.property).2 b.hom
    obtain ⟨g, hg⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map (W n).L.obj C hC).2 b.inv
    change F.map f = b.hom at hf
    change F.map g = b.inv at hg
    have hfg : f ≫ g = 𝟙 C :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map C C hC).1 (by
        change F.map (f ≫ g) = F.map (𝟙 C)
        simp only [Functor.map_comp, hf, hg, Iso.hom_inv_id]
        exact (F.map_id _).symm)
    have hgf : g ≫ f = 𝟙 (W n).L.obj :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (W n).L.property).1 (by
        change F.map (g ≫ f) = F.map (𝟙 (W n).L.obj)
        simp only [Functor.map_comp, hf, hg, Iso.inv_hom_id]
        exact (F.map_id _).symm)
    refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
    change F.map f ≫ _ = _
    rw [hf]
    simp [b, a, Category.assoc]
  choose beta hbeta using lift
  refine ⟨⟨M, hM, W, theta, beta, hbeta⟩, e, ?_⟩
  intro n
  have ht := Functor.map_preimage
    (pbcDerivedFunctionRealization T d n)
    (((pbcFunctionReduction T d n).symm.app (M (n + 1)) ≪≫
        (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).mapIso
          (e (n + 1)) ≪≫
        pbcReductionNormalization (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K ≪≫ (e n).symm).hom)
  change (pbcDerivedFunctionRealization T d n).map (theta n).hom ≫ _ = _
  rw [show (pbcDerivedFunctionRealization T d n).map (theta n).hom = _ from ht]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

private def fixedRestrictId (T : Scheme.{u}) (P : Type (u + 1)) [CommRing P] :
    Sheaf.restrictScalars (ProEt.topology T) (RingHom.id P) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId P) ≪≫ F.obj.rightUnitor))
    (by intro F G f; ext U x; rfl)

private def functionRealizationComparison
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ) :
    pbcFunctionRealization T d n ≅
      ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n) ⋙
        SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison T (ProEtale.PbcQuotient d n)).hom := by
  let P := ProEtale.PbcQuotient d n
  let e := AdicCoefficients.finiteRingComparison T P
  let a := pbcAssociatedRestriction_exists T P P
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (Opposite.op n)))
    (ProEtale.finiteCoefficientRingSheaf T P)
    (pbcFunctionScalars T d n) (ProEtale.finiteCoefficientScalarMap T P)
    (RingHom.id P) e.hom (by
      simp [pbcFunctionScalars, P, e]
      rfl)
  exact (Functor.isoWhiskerRight (fixedRestrictId T P).symm
    (pbcFunctionRealization T d n)) ≪≫ a.exists.choose

private theorem levelwiseOrigin
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (n : ℕ)
    (h : IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin T d M n) :
    ∃ (K : ProEtale.PbcWitnessAmbient T d n)
      (hK : DerivedCategory.TStructure.t.plus
        ((ProEtale.finiteCoefficientRealization T
          (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj K)),
      Nonempty (EtaleOriginWitness T (ProEtale.PbcQuotient d n)
        ⟨(ProEtale.finiteCoefficientRealization T
          (ProEtale.PbcQuotient d n)).mapDerivedCategory.obj K, hK⟩) ∧
      Nonempty ((pbcDerivedFunctionRealization T d n).obj K ≅ M.level n) := by
  obtain ⟨C, ⟨L, ⟨_, a, b, hab, hbound⟩, ⟨eL⟩⟩, ⟨eC⟩⟩ := h
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) T
  let R := ProEtale.finiteCoefficientRealization T (ProEtale.PbcQuotient d n)
  let G := ProEtale.finiteCoefficientComparison T (ProEtale.PbcQuotient d n)
  let K := F.mapDerivedCategory.obj L
  have hLp : DerivedCategory.TStructure.t.plus L := by
    refine ⟨a, (DerivedCategory.isGE_iff L a).2 ?_⟩
    intro q hq
    exact hbound q (Or.inl hq)
  have hGp : DerivedCategory.TStructure.t.plus (G.mapDerivedCategory.obj L) := by
    obtain ⟨c, hc⟩ := hLp
    let := hc
    exact ⟨c, G.isGE_mapDerivedCategory_obj L c⟩
  let e : R.mapDerivedCategory.obj K ≅ G.mapDerivedCategory.obj L :=
    (Functor.mapDerivedCategoryCompIso F R).symm.app L
  have hK : DerivedCategory.TStructure.t.plus (R.mapDerivedCategory.obj K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso e.symm hGp
  let W : EtaleOriginWitness T (ProEtale.PbcQuotient d n)
      ⟨R.mapDerivedCategory.obj K, hK⟩ :=
    ⟨⟨L, hLp⟩, DerivedCategory.Plus.ι.preimageIso e.symm⟩
  refine ⟨K, hK, ⟨W⟩, ⟨?_⟩⟩
  let Q := SheafOfModules.restrictScalars
    (AdicCoefficients.finiteRingComparison T (ProEtale.PbcQuotient d n)).hom
  let U := SheafOfModules.toSheaf
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (Opposite.op n)))
  have : PreservesFiniteLimits (Q ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf
      (ProEtale.finiteCoefficientRingSheaf T (ProEtale.PbcQuotient d n))))
  have : PreservesFiniteColimits (Q ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf
      (ProEtale.finiteCoefficientRingSheaf T (ProEtale.PbcQuotient d n))))
  have : PreservesFiniteLimits Q := preservesFiniteLimits_of_reflects_of_preserves Q U
  have : PreservesFiniteColimits Q := preservesFiniteColimits_of_reflects_of_preserves Q U
  exact (Functor.mapDerivedCategoryNatIso (functionRealizationComparison T d n)).app K ≪≫
    (Functor.mapDerivedCategoryCompIso R Q).app K ≪≫
    Q.mapDerivedCategory.mapIso (e ≪≫ eL) ≪≫ Q.mapDerivedCategoryFactors.app C ≪≫ eC

private theorem boundedConstructible_of_reductionControl
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (hc : PbcIsIntrinsicallyComplete T d K)
    (h : PbcConstructibleReductionControl T d K) :
    PbcIsBoundedConstructibleComplete T d K := by
  obtain ⟨a, b, hab, hconstructible, hbounded⟩ := h
  classical
  have hlocal := normalizedConstructibleTower_local_effectivity T d
    (pbcReductionAdicTower T d K) hconstructible a b hab hbounded
  have hlevels (n : ℕ) := levelwiseOrigin T d
    (pbcReductionAdicTower T d K) n (hlocal.1 n)
  choose M hM hW he using hlevels
  let W := fun n ↦ Classical.choice (hW n)
  let e := fun n ↦ Classical.choice (he n)
  refine ⟨hc, ?_, compatibleOrigins_of_levelwise T d K M hM W e⟩
  refine ⟨pbcReductionAdicTower T d K, fun _ ↦ Iso.refl _, ?_, ?_⟩
  · exact hlocal.2
  · intro b a hab
    dsimp only [pbcReductionAdicTower, Iso.refl_hom]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    unfold adicTowerSemilinearTransition
    change (pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app _ ≫
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
        (pbcReductionNormalizationHom (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) K) = _
    exact ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).homEquiv
      ((pbcCompletedReduction T d b).obj K) ((pbcCompletedReduction T d a).obj K))
        |>.apply_symm_apply (pbcReductionTransition (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) K)

/-- The four completed-coefficient operations preserve the full constructible complete
condition for the original adic datum, independently of a finite-extension presentation.
Source: Stacks 09C7 and 09C2; blueprint main-20261015,
prop-weil-pbc-preservation-constructible.proof.md
(blueprint: lem-weil-pbc-actual-coefficient-constructible-preservation).

Proof: uniform local models of the input tower have a single term window [d0,d1].
The uniform perfect-quotient bound gives resolutions in [-r,0] for every quotient.
Flat constant-to-completed comparison sheafifies these resolutions. Their tensor with
each local model vanishes outside [d0-r,d1]. On each stratum use its supplied covering;
then the retained etale origins and geometric stalk conservativity give this same
bound globally. The strata are not claimed to form a pro-etale covering.
Apply amplification_of_isProper to the annihilator N and the geometric fibre bound.
Its finite-level amplification gives constructibility and [a,b+2e] for proper direct
images and [a,b] for pullbacks, where [a,b]=[d0-r,d1]. Direct image commutes with the
specified derived inverse limit and preserves intrinsic completeness. Its perfect
projection mate identifies its canonical reductions with the finite direct images,
including quotient actions: lift quotient scalars locally to the completed coefficient
ring and use annihilation to see independence of the lifts. Completed-pullback reduction
gives intrinsic completeness and canonical quotient-linear reduction isomorphisms for
the two pullbacks. Apply these statements first to K and then to its direct image.
The fourth object is handled by the same proper direct-image argument for f'.
For each output, normalized constructible local effectivity gives bounded etale
origins. Exact realization and its scalar-restriction comparison put each origin in
the specified fixed-coefficient presentation. The normalized etale-origin theorem
lifts the canonical normalization maps
uniquely and preserves their unit and quotient cocycle; exact inverse image detects
boundedness before its bounded-below full faithfulness is used. Finally normalized
constructible local effectivity supplies the common local models for each output's
canonical tower. Intrinsic completeness, these models, and the compatible origins
are exactly the three defining clauses of the conclusion. Zero inputs, empty schemes,
and a zero finite quotient are covered by the same support containments. -/
theorem AdicCoefficientDatum.constructible_preservation
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (hDimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (hDimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnn : (N : A ⧸ d.ideal) = 0)
    (hNX : IsUnit (N : Γ(X, ⊤))) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hNX' : IsUnit (N : Γ(X', ⊤))) (hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : d.derived X) (hK : PbcIsBoundedConstructibleComplete X d K) :
    PbcIsBoundedConstructibleComplete Y d ((d.push f).obj K) ∧
      PbcIsBoundedConstructibleComplete Y' d
        ((d.completedPull g).obj ((d.push f).obj K)) ∧
      PbcIsBoundedConstructibleComplete X' d ((d.completedPull g').obj K) ∧
      PbcIsBoundedConstructibleComplete Y' d
        ((d.push f').obj ((d.completedPull g').obj K)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := d.constructible_reduction_control sq
    hDimX hDimY hDimX' hDimY' N hN hAnn hNX hNY hNX' hNY' e hFibres K hK
  have hc₁ := datumPush_intrinsicComplete f d K hK.1
  have hc₂ := datumPull_intrinsicComplete g d _ hc₁
  have hc₃ := datumPull_intrinsicComplete g' d K hK.1
  have hc₄ := datumPush_intrinsicComplete f' d _ hc₃
  exact ⟨boundedConstructible_of_reductionControl Y d _ hc₁ h₁,
    boundedConstructible_of_reductionControl Y' d _ hc₂ h₂,
    boundedConstructible_of_reductionControl X' d _ hc₃ h₃,
    boundedConstructible_of_reductionControl Y' d _ hc₄ h₄⟩

end AlgebraicGeometry.Scheme
