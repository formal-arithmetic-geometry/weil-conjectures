/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Compactification.OnePoint.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.OrdinaryChart.OrdinaryChartAdjunctionObjects
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-!
# Finite coefficient comparison for smooth exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md, det-sp-reduction-exceptional;
proof: sk-lem-sp-reduction-exceptional.proof.md, Existence, uniqueness, naturality;
Locality; Charts (blueprint: det-sp-reduction-exceptional).

This statement retains the canonical compact-support mate and its normalized chart formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem reductionCtf_good (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (M : proEtaleDerivedCategory T A) :
    spFiniteConstructibleTor T A M ↔
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj M)} ∧
        (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
          ((DerivedCategory.homologyFunctor _ i).obj M)) ∧
        HasFiniteProEtaleTorAmplitude T A M := by
  constructor
  · rintro ⟨⟨a, b, hab, hz⟩, hc, ht⟩
    refine ⟨?_, hc, ht⟩
    apply Set.Finite.subset (Set.finite_Icc a b)
    intro i hi
    constructor <;> by_contra! hn
    · exact hi (hz i (.inl hn))
    · exact hi (hz i (.inr hn))
  · rintro ⟨hb, hc, ht⟩
    obtain ⟨a, ha⟩ := hb.bddBelow
    obtain ⟨b, hb⟩ := hb.bddAbove
    refine ⟨⟨min a b, b, min_le_right _ _, ?_⟩, hc, ht⟩
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi

private theorem reductionCtf_iso {T : Scheme.{u}} {A : Type u}
    [CommRing A] [Finite A] {K L : proEtaleDerivedCategory T A}
    (e : K ≅ L) (h : spFiniteConstructibleTor T A K) :
    spFiniteConstructibleTor T A L := by
  obtain ⟨hb, hc, a, b, ht⟩ := (reductionCtf_good T A K).mp h
  apply (reductionCtf_good T A L).mpr
  refine ⟨hb.subset (fun i hi hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)),
    ?_, a, b, ht.1, ?_⟩
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e))
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))
  · intro N P hN f hf hP M i hi
    obtain ⟨q⟩ := hN
    exact ht.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem reductionMate_existsUnique
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {LA : C ⥤ D} {GA : D ⥤ C} {LB : E ⥤ F} {GB : F ⥤ E}
    (a : LA ⊣ GA) (b : LB ⊣ GB) (S : C ⥤ E) (T : D ⥤ F)
    (β : LA ⋙ T ≅ S ⋙ LB) :
    ∃! c : GA ⋙ S ⟶ T ⋙ GB,
      ∀ K, LB.map (c.app K) ≫ b.counit.app (T.obj K) =
        β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) := by
  let c := (mateEquiv a b (TwoSquare.mk S LA LB T β.inv)).natTrans
  have hc (K : D) : LB.map (c.app K) ≫ b.counit.app (T.obj K) =
      β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) :=
    mateEquiv_counit a b (TwoSquare.mk S LA LB T β.inv) K
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  ext K
  apply (b.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using (hc' K).trans (hc K).symm

-- The following three arguments retain the realized counit and canonical chart map.
-- Their field-dependent input is only that ell is invertible on the base.

private theorem finiteExceptionalRealization
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (_hf : j ≫ p = f)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj)) :
    ∃ (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
      (adj : reductionCtfCompactSupport A j p hF ⊣ G),
      Nonempty (ReductionExceptionalRealization A j p hF G adj) := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (Z ↘ Spec (.of k))
  have : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := by
    obtain ⟨n, hn⟩ := hA
    have hz : ((ℓ ^ n : ℕ) : ULift.{u + 1} A) = 0 := by
      apply ULift.ext
      change ((ℓ ^ n : ℕ) : A) = 0
      simpa only [nsmul_eq_mul, mul_one] using hn 1
    have hne : (ℓ : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hchar
    have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
    exact ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, hz, by
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have : HasInvertibleExponent (ULift.{u + 1} A) Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  exact realizationFromData A j p hF
    (ordinaryCtfData A k (Y ↘ Spec (.of k)) j p)

private theorem finiteExceptionalChart
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hb : ∀ K : spFiniteConstructibleTorCategory Y A,
      IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj))
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCompactSupport B j p).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
            (hb K) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) :
    ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c := by
  classical
  have _ := hf
  have _ := hA
  have _ := hB
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  let F := RA.origin ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y
  let H := reductionCtfScalar φ Y hSY ⋙ RB.origin
  have hF (K) : _root_.DerivedCategory.TStructure.t.plus (F.obj K) := by
    have hM : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) Y (RA.origin.obj K) :=
      ⟨(AdjunctionTransfer.boundedConstructible_iff _ Y _).2
        (RA.origin_ctf K).1, (RA.origin_ctf K).2⟩
    obtain ⟨a, b, hTor⟩ := hM.2
    refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr (fun q hq ↦ ?_)⟩
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (Sheaf.restrictScalars Y.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ))
    exact ((_root_.DerivedCategory.isGE_iff _ a).1
      (hTor (Etale.scalarCoefficientSheaf (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y)).1
        q hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.scalarTensorIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).app
          (RA.origin.obj K)))
  have hH (K) : _root_.DerivedCategory.TStructure.t.plus (H.obj K) :=
    (RB.origin_ctf ((reductionCtfScalar φ Y hSY).obj K)).1.1.1
  let Fp := ObjectProperty.lift _ F hF
  let Hp := ObjectProperty.lift _ H hH
  let S := DerivedCategory.Plus.ι ⋙ reductionSite B Y
  have : S.Full := site_plus_full B Y
  have : S.Faithful := site_plus_faithful B Y
  let e : Fp ⋙ S ≅ Hp ⋙ S :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft RA.origin (reductionSiteScalarIso φ Y).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight RA.originIso (scalarExtensionFunctor φ Y) ≪≫
      (Functor.isoWhiskerLeft (reductionCtfScalar φ Y hSY) RB.originIso).symm
  let op := Functor.fullyFaithfulCancelRight S e
  let o : F ≅ H := Functor.isoWhiskerRight op DerivedCategory.Plus.ι
  have ho (K : spFiniteConstructibleTorCategory Y A) :
      (reductionSite B Y).map (o.hom.app K) ≫
          RB.originIso.hom.app ((reductionCtfScalar φ Y hSY).obj K) =
        (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj K) ≫
          (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app K) := by
    change S.map (op.hom.app K) ≫ _ = _
    dsimp only [op]
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    simp only [ObjectProperty.ι, reductionCtfScalar, ObjectProperty.lift, Functor.comp_obj,
      inducedFunctor_obj, Functor.comp_map, inducedFunctor_map, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, e]
    exact Category.id_comp _
  refine ⟨o, ho, ?_⟩
  intro n hnA hnB
  have hunit : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h : (ℓ : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k
      (Fact.out : ℓ.Prime) hchar
    have hu := (isUnit_iff_ne_zero.mpr (pow_ne_zero n h)).map
      (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      hu.map (Y ↘ Spec (.of k)).appTop.hom
  refine ⟨hunit, ?_⟩
  intro MA MB tA DA tB DB hX hY U hU i hi e hee hse hlfe hqce he K
  let KB := (reductionCtfScalar φ Y hSY).obj K
  let L := RA.origin.obj K
  let LB := RB.origin.obj KB
  let m := reductionExceptionalComponent φ X Y hSX hSY GA GB c K
  obtain ⟨q, hq⟩ := (site_map_bijective B X
    ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj
      (RA.right.obj L)) (RB.right.obj LB) (RB.right_plus KB)).2
    ((reductionSiteScalarIso φ X).inv.app (RA.right.obj L) ≫
      (scalarExtensionFunctor φ X).map (RA.rightIso.inv.app K) ≫
      m ≫ RB.rightIso.hom.app KB)
  have cq := reductionExceptional_counit_descent φ j p hFA hFB GA GB adjA adjB RA RB
    K KB (𝟙 _) (o.hom.app K)
    (by
      change _ = _ ≫ _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact ho K)
    m (hb K) (by
      change _ = _ ≫ _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact hc K)
    q hq
  let cf : Compactification (j ≫ p) :=
    ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
  let rA := (reductionEtaleChartRightIso (ULift.{u + 1, u} A) MA (j ≫ p) i d e he cf
    RA.right RA.adjunction (ℓ ^ n) hnA tA DA hunit).app L
  let rB := (reductionEtaleChartRightIso (ULift.{u + 1, u} B) MB (j ≫ p) i d e he cf
    RB.right RB.adjunction (ℓ ^ n) hnB tB DB hunit).app LB
  let v := (reductionEtaleChartScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ)
    (ℓ ^ n) hnA hnB hunit d e L).hom ≫
      (Etale.affineTraceRight (ULift.{u + 1, u} B) (ℓ ^ n) hnB Y d ⋙
        Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) e).map (o.hom.app K)
  have chart := reductionExceptional_ordinary_chart
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) hnA hnB (j ≫ p) i d e he cf MA MB
    tA DA tB DB hunit RA.right RB.right RA.adjunction RB.adjunction
    L (RA.origin_ctf K) LB (o.hom.app K) q cq
  have h := transfer_chart
    (reductionSite A X) (reductionSite A U) (reductionSite B X) (reductionSite B U)
    (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X)
    (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) U)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ U)
    (Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i)
    (Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) i)
    (proEtaleConstantRingDerivedPullback A i) (proEtaleConstantRingDerivedPullback B i)
    (reductionSiteScalarIso φ X) (reductionSiteScalarIso φ U)
    (reductionSitePullbackIso A i) (reductionSitePullbackIso B i)
    (directImageScalarPullbackIso φ i)
    (Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) i)
    (RA.rightIso.app K) (RB.rightIso.app KB) m q rA rB v hq
    (reductionSite_scalar_pullback φ i (RA.right.obj L)) chart
  simpa only [reductionIntrinsicChartIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Functor.comp_obj, ObjectProperty.ι_obj,
    scalarExtensionFunctor, scalarExtension, directImageScalarExtension,
    Category.assoc, cf, rA, rB, v, L, LB, KB, m] using h

private theorem finiteExceptionalConservative
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hchart : ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c) :
    ∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)  := by
  classical
  intro K
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨r, hr⟩ := hA
  obtain ⟨s, hs⟩ := hB
  let n := r + s
  have hnA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : A) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ r : ℕ) : A) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hr 1
    rw [hz, zero_mul]
  have hnB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0 := by
    apply ULift.ext
    change ((ℓ ^ (r + s) : ℕ) : B) = 0
    rw [pow_add, Nat.cast_mul]
    have hz : ((ℓ ^ s : ℕ) : B) = 0 := by
      simpa only [nsmul_eq_mul, mul_one] using hs 1
    rw [hz, mul_zero]
  obtain ⟨o, ho, hchart⟩ := hchart
  obtain ⟨hY, hchart⟩ := hchart n hnA hnB
  obtain ⟨MA⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} A)
  obtain ⟨MB⟩ := Etale.nonempty_etaleCompactSupportNormalization (ULift.{u + 1, u} B)
  obtain ⟨tA, DA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} A) hnA
  obtain ⟨tB, DB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ULift.{u + 1, u} B) hnB
  obtain ⟨m, U, V, hUV, e₀, e, hcover, _, _, _, _, he⟩ :=
    SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover
      (k := k) f d
  have hlocal (a : Fin m) :
      IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom) := by
    have ha := he a
    have : IsNoetherian (U a).toScheme := ha.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have : IsSeparated (e a) := ha.2.2.2.2.2.1
    have : AlgebraicGeometry.Etale (e a) := ha.2.2.2.2.2.2.1
    have : LocallyOfFinitePresentation (e a) := ha.2.2.2.2.2.2.2.1
    have : QuasiCompact (e a) := ha.2.2.2.2.2.2.2.2.1
    let v := e a ≫ (affineTraceAffineSpaceIso Y d).inv
    have : IsSeparated v := inferInstance
    have : AlgebraicGeometry.Etale v := inferInstance
    have : LocallyOfFiniteType v := inferInstance
    have : QuasiCompact v := inferInstance
    have hv : (U a).ι ≫ (j ≫ p) = v ≫ affineTraceProjection Y d := by
      rw [hf, ha.2.2.2.2.2.2.2.2.2.2.1]
      dsimp [v]
      have hp : affineTraceToAffineSpace Y d ≫
          (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = affineTraceProjection Y d :=
        AffineSpace.homOfVector_over _ _
      rw [← hp]
      simp [Category.assoc, affineTraceAffineSpaceIso]
    have h := hchart MA MB tA DA tB DB inferInstance inferInstance
      (U a).toScheme (U a).ι v hv K
    have : IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj ≫
        (proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom) := by
      change IsIso ((directImageScalarPullbackIso φ (U a).ι).inv.app
        (GA.obj K).obj ≫ (proEtaleConstantRingDerivedPullback B (U a).ι).map
          (reductionExceptionalComponent φ X Y hSX hSY GA GB c K) ≫ _)
      rw [h]
      infer_instance
    have := IsIso.of_isIso_comp_left
      ((directImageScalarPullbackIso φ (U a).ι).inv.app (GA.obj K).obj)
      ((proEtaleConstantRingDerivedPullback B (U a).ι).map (c.app K).hom ≫
        (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
          (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom)
    exact IsIso.of_isIso_comp_right _
      (reductionIntrinsicChartIso B j p hFB GB adjB RB MB (U a).ι d v hv
        (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom
  let E := sfIntrinsicDerivedEquivalence X B
  let g := E.inverse.map (c.app K).hom
  have hfixed (a : Fin m) : IsIso ((sfFixedDerivedPullback B (U a).ι).map g) := by
    have hi : IsIso ((proEtaleConstantRingDerivedPullback B (U a).ι).map
        (E.functor.map g)) := by
      have := hlocal a
      exact (NatIso.isIso_map_iff
        (Functor.isoWhiskerRight E.counitIso
          (proEtaleConstantRingDerivedPullback B (U a).ι)) (c.app K).hom).mpr
          (by simpa only [Functor.comp_map, Functor.id_map] using hlocal a)
    have hi' : IsIso ((sfIntrinsicDerivedEquivalence (U a).toScheme B).functor.map
        ((sfFixedDerivedPullback B (U a).ι).map g)) :=
      (NatIso.isIso_map_iff (reductionRealizationPullbackIso B (U a).ι) g).mp hi
    exact isIso_of_reflects_iso _ (sfIntrinsicDerivedEquivalence (U a).toScheme B).functor
  have hg : IsIso g := by
    obtain ⟨C, v, δ, ht⟩ := Pretriangulated.distinguished_cocone_triangle g
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ ht).mp
    apply isZero_of_forall_isZero_mapDerivedCategory_upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U hcover
    intro a
    have := hfixed a
    apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((sfFixedDerivedPullback B (U a).ι).map_distinguished _ ht)).mpr
    exact hfixed a
  have : IsIso (c.app K).hom := isIso_of_reflects_iso _ E.inverse
  exact (ObjectProperty.isIso_hom_iff (c.app K)).mp inferInstance

/-- Exceptional inverse image of a smooth morphism commutes with extension of finite coefficients.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/`
`sk-lem-sp-reduction-exceptional.md`, det-sp-reduction-exceptional; standing
finite-or-algebraically-closed field convention (blueprint: det-sp-reduction-exceptional).

Proof (deferred to stage 3; the node's six steps, from
`sk-lem-sp-reduction-exceptional.proof.md`):

1. (Existence, uniqueness, naturality.) Put $T=(-)_B$, $F_R=Rf_{!,R}$, $G_R=f_R^!$. Scalar
preservation and the restricted adjunction make $\tau_K=T(\epsilon_{A,K})b(G_AK)^{-1}$ well
typed. Define $c_K$ as its unique $B$-transpose. This is the required counit equation.
Naturality of $b,\epsilon_A$ gives $T(u)\tau_K=\tau_LF_BTG_A(u)$; injectivity and naturality of
transposition prove naturality of $c$.
Uses: det-sp-scalar-extension-functor, sk-prop-sf-rf-shriek-preservation,
det-sp-reduction-direct-image, def-weil-pbc-adjunction-mate.

2. (Locality and Charts.) Take the admissible affine coordinate cover $j:U\hookrightarrow X$,
$g=fj=p_de$. Its schemes and maps meet the finite-ring chart hypotheses. The chart-domain
theorem supplies etale origins, finite-Tor site equivalences and preservation by compact
support, pullback, Tate tensor, shifts and scalar extension.
Uses: lem-sp-smooth-admissible-coordinate-cover, lem-sp-etale-ctf-chart-domain.

3. (Charts: Kummer, diagonal, splitting and iterated integration.) The projective-line
splitting theorem preserves the unit, Kummer and diagonal classes and trace. The actual
projective-line counit has its scalar equation; the ordered affine-space counit theorem gives
$\epsilon_{d,B}F_{d,B}(a_d)\beta_d=T\epsilon_{d,A}$, including $d=0$, for the specified
compactification.
Uses: lem-sp-finite-p1-coefficient-splitting, lem-sp-p1-counit-scalar,
lem-sp-affine-counit-scalar.

4. (Charts: summation and composition with affine integration.) The etale-sum theorem gives the
counit scalar equation and graph-normalized coefficient square for $e$. Paste its inverse
coefficient square with that of $p_d$ using mate-pasting (2) and the composite counit.
Compact-support scalar composition and refinement identify the left square with $\beta_g$;
the ordered right normal form identifies its mate with canonical $a_g$. Thus
$\epsilon_{g,B}F_{g,B}(a_g)\beta_g=T\epsilon_{g,A}$.
Uses: lem-sp-finite-etale-sum-coefficient-counit, lem-weil-pbc-mate-pasting,
def-weil-pbc-composite-adjunction, lem-pur-etale-compact-scalar-coherence,
lem-amb-etale-compact-comparisons, lem-sp-finite-affine-right-scalar-normal-form.

5. (Charts: counit transport and canonical reassociation.) Transfer the chart adjunction
counit-preservingly through $\nu^*$: its counit is $\nu^*(\epsilon^{et})c_R^{-1}$. Substitute
the finite site/coefficient square in Step 4. It gives
$\epsilon_{g,B}F_{g,B}(\rho_K)=T(\epsilon_{g,A})b_g^{-1}$. The right-normal-form site equation
and chart reassociation identify the transported $a_g$ with $\rho_K$. Uniqueness of the
transpose gives $c_g(K)=\rho_K$.
Uses: det-sp-et-proet-adjunction-transfer, lem-sp-finite-ctf-site-coefficient-square,
lem-sp-finite-affine-right-scalar-normal-form,
lem-sp-reduction-exceptional-chart-scalar-reassociation, def-weil-pbc-adjunction-mate.

6. (Locality and Charts conclusion.) Open locality gives $c_g=j_B^*c_f\circ a_j$ under the
counit-preserving chart identification. Step 5 therefore gives exactly the asserted canonical
chart map for every restriction of $c_f$. It is invertible, so covering-family conservativity
makes $c_f$ invertible. This includes the empty scheme and its empty cover.
Uses: lem-sp-finite-exceptional-coefficient-open-locality, lem-cbc-proetale-stalk-conservative.
-/
theorem reductionExceptional_coefficient_extension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
      (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
      (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
        spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)),
      ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
        (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
        (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
        (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB),
        ∃ (RA : ReductionExceptionalRealization A j p hFA GA adjA)
          (RB : ReductionExceptionalRealization B j p hFB GB adjB),
        ∃ hb : ∀ K : spFiniteConstructibleTorCategory Y A,
          IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj),
        ∃! c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB,
          (∀ K : spFiniteConstructibleTorCategory Y A,
            (reductionCompactSupport B j p).map (c.app K).hom ≫
                (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
              @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
                  (hb K) ≫
                (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
          (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)) ∧
          ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB
            RA RB c := by
  classical
  have hF (R : Type u) [CommRing R] [Finite R]
      (hR : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0)
      (M : spFiniteConstructibleTorCategory X R) :
      spFiniteConstructibleTor Y R ((reductionCompactSupport R j p).obj M.obj) := by
    obtain ⟨hb, hc, ht⟩ := (reductionCtf_good X R M.obj).mp M.property
    have h := (reductionDirectImage_finiteCoefficients_isIso ℓ k hk hchar f j p hf hR hR
      (RingHom.id R) M.obj hb hc ht).2
    exact reductionCtf_iso ((scalarExtensionFunctor_identity Y).app _)
      ((reductionCtf_good Y R _).mpr ⟨h.1, h.2.1, h.2.2.1⟩)
  let hFA := hF A hA
  let hFB := hF B hB
  have hS (T : Scheme.{u}) (M : spFiniteConstructibleTorCategory T A) :
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M.obj) := by
    obtain ⟨hb, hc, a, b, ht⟩ := (reductionCtf_good T A M.obj).mp M.property
    obtain ⟨hb', hc', ht'⟩ := scalarExtensionFunctor_preserves_constructible_tor
      ℓ hA hB φ T M.obj hb hc a b ht
    exact (reductionCtf_good T B _).mpr ⟨hb', hc', a, b, ht'⟩
  obtain ⟨GA, adjA, ⟨RA⟩⟩ :=
    finiteExceptionalRealization ℓ k hchar f j p hf A hA hFA
  obtain ⟨GB, adjB, ⟨RB⟩⟩ :=
    finiteExceptionalRealization ℓ k hchar f j p hf B hB hFB
  have hcomp (M : spFiniteConstructibleTorCategory X A) :
      IsIso ((reductionDirectImageComparison φ j p).app M.obj) := by
    have hM := (reductionCtf_good X A M.obj).mp M.property
    exact (reductionDirectImage_finiteCoefficients_isIso ℓ k hk hchar f j p hf hA hB φ M.obj
      hM.1 hM.2.1 hM.2.2).1
  let beta : reductionCtfCompactSupport A j p hFA ⋙ reductionCtfScalar φ Y (hS Y) ≅
      reductionCtfScalar φ X (hS X) ⋙ reductionCtfCompactSupport B j p hFB :=
    NatIso.ofComponents
      (fun M ↦ by
        have := hcomp M
        exact (spFiniteConstructibleTor Y B).fullyFaithfulι.preimageIso
          (asIso ((reductionDirectImageComparison φ j p).app M.obj)))
      (by
        intro M N g
        apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison φ j p).naturality g.hom)
  obtain ⟨c, hc, hu⟩ := reductionMate_existsUnique adjA adjB
    (reductionCtfScalar φ X (hS X)) (reductionCtfScalar φ Y (hS Y)) beta
  have hc' (K : spFiniteConstructibleTorCategory Y A) :
      (reductionCompactSupport B j p).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y (hS Y)).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
          (hcomp (GA.obj K)) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom := by
    exact congrArg (fun v ↦ v.hom) (hc K)
  have hchart := finiteExceptionalChart ℓ k hchar f d j p hf hA hB φ
    hFA hFB (hS X) (hS Y) GA GB adjA adjB RA RB c (fun K ↦ hcomp (GA.obj K)) hc'
  refine ⟨hFA, hFB, hS X, hS Y, GA, GB, adjA, adjB, RA, RB,
    (fun K ↦ hcomp (GA.obj K)), c, ⟨hc', ?_, hchart⟩, ?_⟩
  · exact finiteExceptionalConservative ℓ k f d j p hf hA hB φ
      hFA hFB (hS X) (hS Y) GA GB adjA adjB RA RB c hchart
  · intro c' hc'
    apply hu c'
    intro K
    apply ObjectProperty.hom_ext
    exact hc'.1 K

end AlgebraicGeometry.ProEtale
