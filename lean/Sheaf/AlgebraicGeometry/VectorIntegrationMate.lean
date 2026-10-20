/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.CompactProjectionExchange
public import Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # The normalized vector integration mate

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, Steps 5--7.
This isolates the ordinary unbounded adjunction argument from coefficient descent,
bounded coefficient realization and the arithmetic choice of an annihilator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.setOption false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
attribute [local instance 20000] Etale.sheafBraidedCategory


private instance symmetry_component_isIso
    (A : Type w) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((derivedTensorSymmetry A X).hom.app K).app L) :=
  (((derivedTensorSymmetry A X).app K).app L).isIso_hom

/-- The adjunct of another right adjoint's counit is the canonical comparison. -/
private theorem adjunct_counit_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D) :
    IsIso (a.homEquiv (H.obj K) K (b.counit.app K)) := by
  have he : a.homEquiv (H.obj K) K (b.counit.app K) =
      (b.rightAdjointUniq a).hom.app K := by
    apply (a.homEquiv _ _).symm.injective
    simpa only [Equiv.symm_apply_apply] using
      (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app b a K).symm
  rw [he]
  infer_instance

/-- A counit transported through a specified source isomorphism has invertible adjunct. -/
private theorem normalized_adjunct_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D)
    {X : C} (e : X ≅ H.obj K) (c : F.obj X ⟶ K)
    (hc : c = F.map e.hom ≫ b.counit.app K) :
    IsIso (a.homEquiv X K c) := by
  rw [hc, a.homEquiv_naturality_left]
  have := adjunct_counit_isIso a b K
  infer_instance

private theorem adjunct_isIso_of_iso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (b : F ⊣ H) (K : D)
    {X : C} (e : X ≅ H.obj K) (c : F.obj X ⟶ K)
    [IsIso c] [IsIso (b.counit.app K)] : IsIso (a.homEquiv X K c) := by
  let z : K ⟶ K := inv (F.map e.hom ≫ b.counit.app K) ≫ c
  have hz : c = (F.map e.hom ≫ b.counit.app K) ≫ z := by
    simp [z]
  rw [hz, a.homEquiv_naturality_right]
  have ha := normalized_adjunct_isIso a b K e
    (F.map e.hom ≫ b.counit.app K) rfl
  have hz : IsIso z := by dsimp [z]; infer_instance
  exact IsIso.comp_isIso' ha (Functor.map_isIso G z)

private theorem derived_isIso_of_cover (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    {M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (φ : M ⟶ N)
    (h : ∀ i, IsIso ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
    a ha _ fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (DerivedCategory.homologyFunctor _ n)
      ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ))

private theorem mate_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    {V : C ⥤ C'} {U : D ⥤ D'} (a : F ⊣ G) (b : F' ⊣ G')
    (e : TwoSquare V F F' U) (X : C) (K : D) (c : F.obj X ⟶ K) :
    V.map (a.homEquiv X K c) ≫ (mateEquiv a b e).app K =
      b.homEquiv _ _ (e.natTrans.app X ≫ U.map c) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Equiv.symm_apply_apply]
  rw [mateEquiv_counit]
  have hn := e.natTrans.naturality (a.homEquiv X K c)
  dsimp only [Functor.comp_map] at hn
  change F'.map (V.map (a.homEquiv X K c)) ≫
    e.natTrans.app (G.obj K) ≫ U.map (a.counit.app K) = _
  rw [reassoc_of% hn]
  rw [← U.map_comp]
  have hc := (a.homEquiv X K).symm_apply_apply c
  rw [Adjunction.homEquiv_counit] at hc
  rw [hc]

private def affineLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    affineTraceLeft A S d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      affineTraceLeft A S n ≅
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
        rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d

private theorem integration_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorBundleIntegration N hN A hA S hS d M) := by
  classical
  obtain ⟨t, D, htD, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  have hn : VectorIntegrationNormalization N hN A hA S hS d M
      (vectorBundleIntegration N hN A hA S hS d M) :=
    (existsUnique_vectorIntegrationGluing N hN A hA S hS d M).2.exists.choose_spec.2
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  apply derived_isIso_of_cover A (fun i : I ↦ (V i).ι) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let hi := affineTracePullbackInvertible N (V i).ι hS
    let := (htrace (V i).toScheme hi d).2.2.1
    let := isIso_rightDerivedLowerShriekBaseChangeMap A
      (vectorIntegrationChart_isPullback S d M (V i) (e i).some)
    have hl : IsIso (vectorIntegrationLocalTrace N hN A hA t D S hS d M
        (V i) (e i).some) := by
      dsimp only [vectorIntegrationLocalTrace]
      infer_instance
    have heq := hn t D (V i) (e i).some
    rw [← heq] at hl
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (V i).ι) _).1
    exact (isIso_comp_right_iff _ (ordinaryFiniteUnitPullback A (V i).ι).hom).1 hl
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩

private theorem affine_unit_adjunct_isIso (N : ℕ) (_hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (hc : IsIso (affineTraceCounit A N hA t D S hS d))
    {X : DerivedCategoryModule A (affineTraceTower S d)}
    (e : X ≅ (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))
    (c : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj X ⟶ ordinaryFiniteUnit A S) [IsIso c] :
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).homEquiv _ _ c) := by
  let b := (affineTraceAdjunction A N hA t D S hS d).ofNatIsoLeft
    (affineLeftIso A S d (HasCompactification.compactification (affineTraceProjection S d)))
  let : IsIso (b.counit.app (ordinaryFiniteUnit A S)) := by
    dsimp only [b, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    let := hc
    change IsIso (_ ≫ affineTraceCounit A N hA t D S hS d)
    infer_instance
  exact adjunct_isIso_of_iso
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)) b _ e c

open scoped CategoryTheory.Functor

section UnitMate
attribute [local irreducible] rightDerivedLowerShriek rightDerivedUpperShriek
  rightDerivedUpperShriekAdjunction
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

private theorem integration_unit_adjunct_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    let : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    let : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d M)).homEquiv _ _
        (vectorBundleIntegration N hN A hA S hS d M)) := by
  classical
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  have hi : IsIso (vectorBundleIntegration N hN A hA S hS d M) :=
    integration_isIso N hN A hA S hS d M
  let := (vectorIntegration_geometry S d M).2.2
  obtain ⟨t, D, htD, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  apply derived_isIso_of_cover A
    (fun i : I ↦ vectorIntegrationChart S d M (V i) (e i).some) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let sq := vectorIntegrationChart_isPullback S d M (V i) (e i).some
    let := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    have hbiso : IsIso (rightDerivedUpperShriekBaseChangeMap A sq) :=
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A sq
    let : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M)).IsLeftAdjoint :=
      inferInstance
    let : (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection (V i).toScheme d)).IsLeftAdjoint :=
      inferInstance
    let a : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M) ⊣
        rightDerivedUpperShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S d M) :=
      rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d M)
    let b := rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (affineTraceProjection (V i).toScheme d)
    let c := (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app
        (vectorIntegrationCoefficient A N hA S d M) ≫
      (ordinaryFinitePullback A (V i).ι).map
        (vectorBundleIntegration N hN A hA S hS d M)
    have hc : IsIso c := IsIso.comp_isIso'
      (Functor.map_isIso ((CategoryTheory.evaluation _ _).obj _)
        (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
      (Functor.map_isIso (ordinaryFinitePullback A (V i).ι)
        (vectorBundleIntegration N hN A hA S hS d M))
    have hm := affine_unit_adjunct_isIso N hN A hA t D (V i).toScheme
      (affineTracePullbackInvertible N (V i).ι hS) d
      (htrace (V i).toScheme (affineTracePullbackInvertible N (V i).ι hS) d).2.2.1
      (vectorIntegrationChartCoefficient A N hA t S hS d M (V i) (e i).some)
      (c ≫ (ordinaryFiniteUnitPullback A (V i).ι).hom)
    rw [b.homEquiv_naturality_right] at hm
    have hm' : IsIso (b.homEquiv _ _ c) :=
      (isIso_comp_right_iff _ ((rightDerivedUpperShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection (V i).toScheme d)).map
          (ordinaryFiniteUnitPullback A (V i).ι).hom)).1 hm
    have he := mate_naturality a b
      (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap A sq)))
      (vectorIntegrationCoefficient A N hA S d M) (ordinaryFiniteUnit A S)
      (vectorBundleIntegration N hN A hA S hS d M)
    change _ ≫ (rightDerivedUpperShriekBaseChangeMap A sq).app _ = b.homEquiv _ _ c
      at he
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (vectorIntegrationChart S d M (V i) (e i).some)) _).1
    apply (isIso_comp_right_iff _
      ((rightDerivedUpperShriekBaseChangeMap A sq).app _)).1
    rw [he]
    exact hm'
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ ((VectorBundleZeroSection.π S d M).base x)) :
        (VectorBundleZeroSection.π S d M).base x ∈ ⨆ i, V i)
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
      (vectorIntegrationChart_isPullback S d M (V i) (e i).some) x
      ⟨(VectorBundleZeroSection.π S d M).base x, hi⟩ rfl
    exact ⟨i, y, hy⟩

end UnitMate

private theorem tensor_adjunct_transport
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (TX : C ⥤ C) (TY : D ⥤ D)
    (π : ∀ X : C, TY.obj (F.obj X) ⟶ F.obj (TX.obj X)) [∀ X, IsIso (π X)]
    (hπ : ∀ {X Y : C} (e : X ⟶ Y), TY.map (F.map e) ≫ π Y = π X ≫ F.map (TX.map e))
    {X : C} {Q K : D} (c : F.obj X ⟶ Q) (r : TY.obj Q ⟶ K) :
    a.homEquiv _ _ (inv (π X) ≫ TY.map c ≫ r) =
      TX.map (a.homEquiv X Q c) ≫
        a.homEquiv _ _ (inv (π (G.obj Q)) ≫ TY.map (a.counit.app Q) ≫ r) := by
  rw [← a.homEquiv_naturality_left]
  apply congrArg (a.homEquiv _ _)
  have hn := hπ (a.homEquiv X Q c)
  rw [← cancel_epi (inv (π X)), ← cancel_mono (inv (π (G.obj Q)))]
    at hn
  simp only [Category.assoc, IsIso.hom_inv_id, IsIso.inv_hom_id_assoc,
    Category.comp_id] at hn
  rw [← reassoc_of% hn, ← TY.map_comp_assoc]
  have hc := (a.homEquiv X Q).symm_apply_apply c
  rw [Adjunction.homEquiv_counit] at hc
  rw [hc]

open CategoryTheory.MonoidalCategory

private theorem bundle_smooth (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d] :
    SmoothOfRelativeDimension d (VectorBundleZeroSection.π S d M) := by
  classical
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := d)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) U hU
  intro i
  let E := (e i).some
  let := (VectorBundleZeroSection.trivializationMap_spec S d M (U i) E).1
  rw [← (VectorBundleZeroSection.trivializationMap_spec S d M (U i) E).2.1]
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) (U i).toScheme ↘ (U i).toScheme) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over
      (ULift.{u} (Fin d)) (U i).toScheme
  simpa using smoothOfRelativeDimension_comp
    (n := 0) (m := d) (VectorBundleZeroSection.trivializationMap S d M (U i) E)
    (AffineSpace (ULift.{u} (Fin d)) (U i).toScheme ↘ (U i).toScheme)

private instance coefficient_projection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (K : DerivedCategoryModule A S) (C : DerivedCategoryModule A X) :
    IsIso (compactProjectionMapCoeffFirst A f K C) := by
  have := isIso_projectionMap_of_finite A f
  unfold compactProjectionMapCoeffFirst
  infer_instance

private theorem three_squares
    {C : Type*} [Category C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : A ⟶ D) (d : D ⟶ C₁)
    (e : C₁ ⟶ E) (f : D ⟶ F) (g : F ⟶ E)
    (h : E ⟶ G) (i : F ⟶ H) (j : H ⟶ G)
    (ha : a ≫ b = c ≫ d) (hb : d ≫ e = f ≫ g) (hc : g ≫ h = i ≫ j) :
    a ≫ b ≫ e ≫ h = c ≫ f ≫ i ≫ j := by
  rw [reassoc_of% ha, reassoc_of% hb, hc]

private theorem coefficient_projection_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (K : DerivedCategoryModule A S) {C D : DerivedCategoryModule A X} (φ : C ⟶ D) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ) ≫
      compactProjectionMapCoeffFirst A f K D =
    compactProjectionMapCoeffFirst A f K C ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFinitePullback A f).obj K)).map φ) := by
  have hp : ((derivedTensor (ModuleCat.{u + 1} A) S).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ)).app K ≫
      ((projectionMap (ModuleCat.{u + 1} A) f).app D).app K =
    ((projectionMap (ModuleCat.{u + 1} A) f).app C).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map φ).app
          ((ordinaryFinitePullback A f).obj K)) := by
    exact NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} A) f).naturality φ) K
  have hτ := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app K).naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ)
  have hσ := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).congr_map
    (NatTrans.congr_app
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality φ)
      ((ordinaryFinitePullback A f).obj K))
  simp only [NatTrans.comp_app, Functor.map_comp] at hσ
  dsimp only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.flip_obj_map, Functor.whiskeringLeft_obj_obj,
    Functor.whiskeringRight_obj_obj] at hp
  simpa only [compactProjectionMapCoeffFirst, Functor.flip_map_app,
    Functor.flip_obj_obj, ordinaryFinitePullback,
    Category.assoc] using
    three_squares _ _ _ _ _ _ _ _ _ _ hτ hp hσ


attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
set_option backward.isDefEq.respectTransparency true

/-- The actual normalized integration counit has invertible adjunct for every unbounded K.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an, Steps 5(c), 6 and 7;
parent thm-amb-vector-bundle-purity, proof Steps 4--9.
(blueprint: lem-amb-vector-integration-mate)

Proof: compare the ordered affine-space compact-support functor with the ambient one
by induction using compactification independence and composition, starting with the
identity compactification in rank zero. The affine-space trace theorem supplies the
normalized affine adjunction and an invertible counit at the unit. On each bundle frame,
normalization identifies the actual integration map with the affine trace; exact inverse
image and cohomology detection first prove that the integration map itself is invertible.
For the unit adjunct, use the canonical exceptional open-base-change mate. The naturality
identity for the two adjunction Hom equivalences identifies the pullback of the global
adjunct with the affine unit adjunct, up to that invertible exchange. The affine
coefficient comparison and uniqueness of right adjoints make this local adjunct invertible.
Detect global invertibility on the frame cover using all cohomology sheaves.

For arbitrary K, projection naturality factors the actual integration adjunct as tensor
with the just-proved unit adjunct followed by the tensor-counit adjunct at the dualizing
object. Bundle charts prove smoothness of relative dimension d. The source library's
orientation-free smooth tensor theorem gives invertibility of its canonical tensor map.
The separate lem-amb-vector-integration-tensor-counit then gives invertibility of the
second factor. Thus the displayed, specified integration adjunct is invertible. No
boundedness or gluing of arbitrary derived morphisms is asserted.
-/
theorem vectorIntegrationMate_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    ∀ [IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
        (vectorIntegrationCoefficient A N hA S d M))],
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d M)).homEquiv _ K
        (inv (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
          (vectorIntegrationCoefficient A N hA S d M)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
            (vectorBundleIntegration N hN A hA S hS d M) ≫
              (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom)) := by
  intro hp
  classical
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  let := (vectorIntegration_geometry S d M).2.2
  let := bundle_smooth S d M
  let : HasInvertibleExponent A S := ⟨N, hN, hA, hS⟩
  let : HasInvertibleExponent A (VectorBundleZeroSection.scheme S d M) :=
    HasInvertibleExponent.of_hom (VectorBundleZeroSection.π S d M)
  have hθ : IsIso (dualizingComplexTensorMap A (VectorBundleZeroSection.π S d M) K) :=
    (exists_dualizingComplex_iso_and_tensor A
      (VectorBundleZeroSection.π S d M) d).choose_spec.2.2.2 K
  let := integration_unit_adjunct_isIso N hN A hA S hS d M
  erw [tensor_adjunct_transport
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d M))
    ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).obj
      ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d M)).obj K))
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K)
    (fun C ↦ compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K C)
    (coefficient_projection_naturality A (VectorBundleZeroSection.π S d M) K)]
  exact IsIso.comp_isIso'
    (Functor.map_isIso
      ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).obj
        ((ordinaryFinitePullback A (VectorBundleZeroSection.π S d M)).obj K)) _)
    (tensor_counit_adjunct_isIso A (VectorBundleZeroSection.π S d M) K hθ)

end AlgebraicGeometry.Etale
