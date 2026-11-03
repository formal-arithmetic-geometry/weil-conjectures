/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSheafProjectionData
public import WeilConjectures.AlgebraicGeometry.SmoothRepresentingPair
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportTorWindow
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
public import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackTwistTorWindow
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom

/-! # The finite Brown adjoint on a coordinate chart

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-finite-existence,
`det-sp-finite-existence-chart.md`, clauses 1--3
(blueprint: det-sp-finite-existence-chart).

The affine space is the library's ordered coordinate tower, with its canonical
`affineTraceAffineSpaceIso` to `AffineSpace (ULift (Fin d)) Y`. Counits use the
specified sum adjunction and the specified ordered affine-line adjunction.
The statement uses the ordinary etale presentation of Dctf; finite site comparison
identifies this with the pro-etale assertion, including its counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The canonical compact-support composition comparison for a coordinate chart.
Both factors are the graph-normalized etale sum/compact-support comparisons.
Source: chart proof, step 6 (blueprint: det-sp-finite-existence-chart). -/
def finiteChartLeftComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y d) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf :=
  letI := affineTraceNoetherian Y d
  let cp := HasCompactification.compactification (affineTraceProjection Y d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection Y d)
  let norm := canonicalEtaleCompactSupportNormalization A
  etaleAmbientLeftComparison A norm e (affineTraceProjection Y d) cp cg ≪≫
    (etaleAmbientLeftComparison A norm j f cf (cg.copy he)).symm

/-- The actual Brown counit restricted to the chart, expressed on its canonical
compact-support composite. No right-adjoint comparison is chosen here.
Source: chart proof, step 7 (blueprint: det-sp-finite-existence-chart). -/
def finiteChartBrownCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f)
    (H : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y)
    (counit : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) cf).obj H ⟶ K) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).obj
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H) ⟶ K :=
  (finiteChartLeftComparison A f j d e he cf).hom.app
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
      ((etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategoryAdjunction.counit.app
          H) ≫ counit

private theorem chart_sum_counit_section (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (m : ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.obj (op W)) :
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).counit.app
      N).hom.app (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
        (etaleSumSection A e ((upperStar (ModuleCat.{u + 1} A) e).obj N) W m) =
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
        (inferInstance : Etale e)).hom.app N).hom.app (op W) m := by
  let G := MorphismProperty.Over.map ⊤ (inferInstance : Etale e)
  let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    (inferInstance : Etale e)
  have : G.IsContinuous V.smallEtaleTopology T.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).IsContinuous
      (V.smallGrothendieckTopology (P := @Etale))
      (T.smallGrothendieckTopology (P := @Etale)))
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) V.smallEtaleTopology T.smallEtaleTopology
  have hc : a.homEquiv _ N
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).counit.app
        N) = i.hom.app N := by
    let c := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).counit.app N
    have h0 : (a.ofNatIsoRight i.symm).homEquiv _ N c = 𝟙 _ := by
      change (a.ofNatIsoRight i.symm).homEquiv _ N
        ((a.ofNatIsoRight i.symm).counit.app N) = 𝟙 _
      rw [← (a.ofNatIsoRight i.symm).homEquiv_symm_id N]
      exact ((a.ofNatIsoRight i.symm).homEquiv _ N).apply_symm_apply (𝟙 _)
    have h : a.homEquiv _ N c ≫ i.inv.app N = 𝟙 _ := by
      simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom] using h0
    calc
      a.homEquiv _ N c = (a.homEquiv _ N c ≫ i.inv.app N) ≫ i.hom.app N := by
        rw [Category.assoc, i.inv_hom_id_app]
        exact (Category.comp_id _).symm
      _ = i.hom.app N := by rw [h, Category.id_comp]
  have hW := congr_app (congrArg (fun f ↦ f.hom) hc) (op W)
  change (G.op.lanUnit.app _).app (op W) ≫
      (toSheafify T.smallEtaleTopology (G.op.lan.obj _)).app (op (G.obj W)) ≫
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).counit.app
        N).hom.app (op (G.obj W)) = _ at hW
  exact congrArg (fun f ↦ f m) hW

private theorem chart_sum_counit_stalk (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (z : Over.mk x ⟶ Over.mk e)
    (a : ((Scheme.pointSmallEtale z.left).sheafFiber
      (A := ModuleCat.{u + 1} A)).obj ((upperStar (ModuleCat.{u + 1} A) e).obj F)) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
      ((etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app F)
        ((etaleProjectionSumStalkIso A e x
          ((upperStar (ModuleCat.{u + 1} A) e).obj F)).inv
            (DirectSum.lof A _ _ z a)) = (etaleProjectionLiftStalkIso A e x z F).hom a := by
  classical
  obtain ⟨v, hv, rfl⟩ := Over.homMk_surjective z
  change Spec (.of Ω) ⟶ V at v
  change v ≫ e = x at hv
  subst x
  let M := (upperStar (ModuleCat.{u + 1} A) e).obj F
  let t := Scheme.pointSmallEtale (v ≫ e)
  let sum := etaleProjectionSumStalkIso A e (v ≫ e) M
  let σ := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).counit.app F
  let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    (inferInstance : Etale e)
  have hmor : ModuleCat.ofHom (DirectSum.lof A _ _ (Over.homMk v rfl)) ≫ sum.inv ≫
      t.sheafFiber.map σ =
        ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e v).app F).hom := by
    apply (Scheme.pointSmallEtale v).presheafFiber_hom_ext
    intro W w
    apply ModuleCat.hom_ext
    ext m
    let Z := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
    let w' : t.fiber.obj Z := Over.homMk w.left (by
      change w.left ≫ (W.hom ≫ e) = v ≫ e
      have hw : w.left ≫ W.hom = v := Over.w w
      rw [← Category.assoc, hw])
    have hg := projection_sum_germ A e (v ≫ e) M (Over.homMk v rfl) W w m
    have hi : sum.inv (DirectSum.lof A _ _ (Over.homMk v rfl)
        ((Scheme.pointSmallEtale v).toPresheafFiber W w M.obj m)) =
        t.toPresheafFiber Z w' ((etaleLowerShriek (ModuleCat.{u + 1} A) e
          inferInstance).obj M).obj (etaleSumSection A e M W m) := by
      change sum.hom _ = _ at hg
      exact (congrArg (fun n ↦ sum.inv n) hg).symm.trans (congrArg
        (fun f ↦ f (t.toPresheafFiber Z w'
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj
          (etaleSumSection A e M W m))) sum.hom_inv_id)
    have hn := t.toPresheafFiber_naturality σ.hom Z w'
    have hn' := congrArg (fun f ↦ f (etaleSumSection A e M W m)) hn
    have hl := projection_lift_germ A e v F W w
      ((i.hom.app F).hom.app (op W) m)
    have hm : etaleLiftSection A e F W ((i.hom.app F).hom.app (op W) m) = m := by
      have h := etaleLiftSection_iso A e F W
      have h' := congrArg (fun f ↦ f ((i.hom.app F).hom.app (op W) m)) h
      change ((i.inv.app F).hom.app (op W))
        ((i.hom.app F).hom.app (op W) m) = etaleLiftSection A e F W _ at h'
      rw [← h']
      exact congrArg (fun f ↦ f m)
        (congr_app (Sheaf.hom_ext_iff.1 (i.hom_inv_id_app F)) (op W))
    rw [hm] at hl
    change t.sheafFiber.map σ
        (sum.inv (DirectSum.lof A _ _ (Over.homMk v rfl)
          ((Scheme.pointSmallEtale v).toPresheafFiber W w M.obj m))) = _
    rw [hi]
    change t.presheafFiber.map σ.hom
      (t.toPresheafFiber Z w'
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M).obj
          (etaleSumSection A e M W m)) = _
    change _ = ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) e v).app F).hom
      ((Scheme.pointSmallEtale v).toPresheafFiber W w M.obj m)
    change _ = t.toPresheafFiber Z w' F.obj _ at hl
    simp only [ModuleCat.comp_apply] at hn'
    exact hn'.trans ((congrArg (fun n ↦ t.toPresheafFiber Z w' F.obj n)
      (chart_sum_counit_section A e F W m)).trans hl.symm)
  exact congrArg (fun f ↦ f a) hmor

private theorem chart_property_of_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    {K L : DerivedCategoryModule A T} (e : K ≅ L)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A T K) :
    ProEtale.AdjunctionTransfer.etaleProperty A T L := by
  refine ⟨⟨?_, ?_⟩, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e hK.2⟩
  · intro i
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1.1 i)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e))
  · obtain ⟨a, b, hab, hz⟩ := hK.1.2
    exact ⟨a, b, hab, fun i hi ↦ (hz i hi).of_iso
      (((_root_.DerivedCategory.homologyFunctor _ i).mapIso e).symm)⟩

private theorem chart_unique
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (P : C → Prop) {H G : C} {K : D} (hH : P H) (hG : P G)
    (cH : F.obj H ⟶ K) (cG : F.obj G ⟶ K)
    (bH : ∀ M, P M → Function.Bijective (fun a : M ⟶ H ↦ F.map a ≫ cH))
    (bG : ∀ M, P M → Function.Bijective (fun a : M ⟶ G ↦ F.map a ≫ cG)) :
    ∃! a : H ≅ G, F.map a.hom ≫ cG = cH := by
  obtain ⟨a, ha⟩ := (bG H hH).surjective cH
  obtain ⟨b, hb⟩ := (bH G hG).surjective cG
  change F.map a ≫ cG = cH at ha
  change F.map b ≫ cH = cG at hb
  have hab : a ≫ b = 𝟙 H := (bH H hH).injective (by
    rw [F.map_comp, Category.assoc, hb, ha, F.map_id, Category.id_comp])
  have hba : b ≫ a = 𝟙 G := (bG G hG).injective (by
    rw [F.map_comp, Category.assoc, ha, hb, F.map_id, Category.id_comp])
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro a' ha'
  exact Iso.ext ((bG H hH).injective (ha'.trans ha.symm))

private theorem chart_compact_preserves
    (ell n : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] (c : Compactification h)
    (K : DerivedCategoryModule A U)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A U K) :
    ProEtale.AdjunctionTransfer.etaleProperty A V
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) := by
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  obtain ⟨e, _, he⟩ := exists_etaleCompactSupport_torWindow k (ringChar k) ell
    (Fact.out : (ringChar k).Prime).pos Fact.out Fact.out c.g
  obtain ⟨a, b, ht⟩ := hK.2
  have hab : min a b ≤ b := min_le_right _ _
  have ht' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left a b) le_rfl)
  obtain ⟨P, hf, hc, hz, hP⟩ :=
    (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A U (min a b) b hab K hK.1).1 ht'
  have hprimary : ∃ m : ℕ, 1 ≤ m ∧ (ell ^ m : ℕ) • (1 : A) = 0 := by
    refine ⟨n + 1, by omega, ?_⟩
    simp only [pow_succ, Nat.cast_mul, nsmul_eq_mul, mul_one, hA, zero_mul]
  have hp := he U c.i A hprimary (min a b) b hab K hK.1 ht' P hP
    (fun i ↦ (hf i).tensorRight) hc hz
  exact ⟨hp.2.2.2.2.2.2.2.1, min a b, b + 2 * (e : ℤ),
    DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hp.2.2.2.2.2.2.2.2⟩

private theorem chart_twist_preserves
    (ell n : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0)
    {T T' : Scheme.{u}} [T.Over (Spec (.of k))] [T'.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T' ↘ Spec (.of k))] [QuasiCompact (T' ↘ Spec (.of k))]
    [IsSeparated (T' ↘ Spec (.of k))]
    (f : T' ⟶ T) [f.IsOver (Spec (.of k))]
    (a : ℕ) (b : ℤ) (K : DerivedCategoryModule A T)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A T K) :
    ProEtale.AdjunctionTransfer.etaleProperty A T'
      ((ProEtale.AdjunctionTransfer.etaleChartOperation A (ell ^ n) hA f a b).obj K) := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have : IsNoetherian T := ⟨⟩
  obtain ⟨i, j, ht⟩ := hK.2
  have hij : min i j ≤ j := min_le_right _ _
  have ht' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left i j) le_rfl)
  obtain ⟨P, hf, hc, hz, hP⟩ :=
    (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A T (min i j) j hij K hK.1).1 ht'
  have : IsSeparated (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹IsSeparated (T ↘ Spec (.of k))›
  have : LocallyOfFiniteType (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹LocallyOfFiniteType (T ↘ Spec (.of k))›
  have : QuasiCompact (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹QuasiCompact (T ↘ Spec (.of k))›
  have : IsSeparated (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹IsSeparated (T' ↘ Spec (.of k))›
  have : LocallyOfFiniteType (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹LocallyOfFiniteType (T' ↘ Spec (.of k))›
  have : QuasiCompact (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹QuasiCompact (T' ↘ Spec (.of k))›
  let g : Over.mk (T' ↘ Spec (.of k)) ⟶ Over.mk (T ↘ Spec (.of k)) :=
    Over.homMk f (comp_over f _)
  have h := (etale_pullback_twist_tor_window k (ringChar k) ell
    (Fact.out : (ringChar k).Prime).pos Fact.out
    (Ne.symm (Fact.out : ringChar k ≠ ell)) _ _ g n A hA (min i j) j hij).1
      K hK.1 ht' P hP (fun i ↦ (hf i).tensorRight) hc hz a b
  have := _root_.DerivedCategory.braidedCategory'
    (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
  let e : pullbackTwistDerived A f (ell ^ n) hA K a b ≅
      (ProEtale.AdjunctionTransfer.etaleChartOperation A (ell ^ n) hA f a b).obj K :=
    (shiftFunctor _ b).mapIso (β_ _ _)
  exact chart_property_of_iso A T' e
    ⟨h.2.2.2.2.2.1, min i j - b, j - b,
      DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2.2.2.2.2.2⟩

private theorem chart_pullback_preserves
    (ell n : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0)
    {T T' : Scheme.{u}} [T.Over (Spec (.of k))] [T'.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T' ↘ Spec (.of k))] [QuasiCompact (T' ↘ Spec (.of k))]
    [IsSeparated (T' ↘ Spec (.of k))]
    (f : T' ⟶ T) [f.IsOver (Spec (.of k))]
    (K : DerivedCategoryModule A T)
    (hK : ProEtale.AdjunctionTransfer.etaleProperty A T K) :
    ProEtale.AdjunctionTransfer.etaleProperty A T'
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) := by
  obtain ⟨a, b, ht⟩ := hK.2
  have hab : min a b ≤ b := min_le_right _ _
  have ht' := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (ht.mono (min_le_left a b) le_rfl)
  have : IsSeparated (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹IsSeparated (T ↘ Spec (.of k))›
  have : LocallyOfFiniteType (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹LocallyOfFiniteType (T ↘ Spec (.of k))›
  have : QuasiCompact (Over.mk (T ↘ Spec (.of k))).hom :=
    ‹QuasiCompact (T ↘ Spec (.of k))›
  have : IsSeparated (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹IsSeparated (T' ↘ Spec (.of k))›
  have : LocallyOfFiniteType (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹LocallyOfFiniteType (T' ↘ Spec (.of k))›
  have : QuasiCompact (Over.mk (T' ↘ Spec (.of k))).hom :=
    ‹QuasiCompact (T' ↘ Spec (.of k))›
  let g : Over.mk (T' ↘ Spec (.of k)) ⟶ Over.mk (T ↘ Spec (.of k)) :=
    Over.homMk f (comp_over f _)
  have h := (etale_pullback_twist_tor_window k (ringChar k) ell
    (Fact.out : (ringChar k).Prime).pos Fact.out
    (Ne.symm (Fact.out : ringChar k ≠ ell)) _ _ g n A hA (min a b) b hab).2 K hK.1 ht'
  exact ⟨h.1, min a b, b, DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 h.2⟩

/-- The finite chart adjunctions, with fibre-sum, tensor-trace, and Brown-counit
normalizations. The base field has characteristic p > 0 different from ell and
finite ell-cohomological dimension. Noetherian instances and exponent
invertibility are derived from this standing finite-type setting.
The Brown adjoint is supplied by its existing representing-pair interface on Dctf,
with no adjunction on the whole unbounded category assumed.

Source: latest blueprint `det-sp-finite-existence-chart`, clauses 1--3
(blueprint: det-sp-finite-existence-chart).

Proof:
1. Finite-type schemes over k are Noetherian and ell^n is invertible on them.
The graph-normalized compact-support comparison identifies Re! with exact sum
extension. Its termwise sum/evaluation adjunction restricts to Dctf. On stalks,
the germ-normalized direct-sum comparison sends each lift summand to that lift;
the inverse-image stalk comparison makes its evaluation the identity. Thus the
counit is the fibre sum, including an empty fibre.
2. Compose the normalized projective-line/open-chart adjunctions in coordinate
order, starting from the identity for d=0. The canonical reassociation identifies
the right functor with p* tensor the finite Tate object shifted by 2d. The actual
counit tensor normalization identifies its value at K with inverse projection,
then 1 tensor the unit trace, then the right unitor. Pullback, Tate tensor and
shift preserve Dctf, and compact support preserves it as well.
3. Compose the sum and affine Hom bijections. Use the canonical compact-support
composition comparison and the open sum adjunction to transport the Brown
counit; this is exactly finiteChartBrownCounit. Transpose it under the composite
adjunction. Transpose the composite counit in the opposite direction. The Hom
bijections show that the two maps are inverse and that the counit equation
uniquely determines the comparison. Finite site comparison transports these
Hom bijections and their actual counits to the pro-etale Dctf categories.
-/
theorem finite_existence_chart
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y U : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [U.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    (d : ℕ)
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [SmoothOfRelativeDimension d f]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth d f
    letI : HasCompactification f := cf.hasCompactification
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    letI : IsNoetherian X := ⟨⟩
    letI : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    letI : IsNoetherian Y := ⟨⟩
    letI : IsLocallyNoetherian U :=
      LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
    letI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
    letI : IsNoetherian U := ⟨⟩
    let hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
      have h : (ell : k) ≠ 0 :=
        CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
          (Fact.out : ringChar k ≠ ell)
      simpa only [map_natCast, map_pow, Nat.cast_pow] using
        (((Ne.isUnit h).pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom).map
          (Y ↘ Spec (.of k)).appTop.hom
    let A := ULift.{u + 1} (ZMod (ell ^ n))
    let N := ell ^ n
    let hA : (N : A) = 0 := CharP.cast_eq_zero A N
    let hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    let P := AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty A
    let T := affineTraceTower Y d
    let p := affineTraceProjection Y d
    let L := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p
    let E := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let R := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    let s := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction
    let W := SectionLocalDualizingComparisons.tateObject A N hA T d
    let Q := fun K : DerivedCategoryModule A Y ↦
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)).obj W
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (D : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS),
      (PreservesFiniteLimits (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ∧
       PreservesFiniteColimits (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)) ∧
      (∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
        letI : DecidableEq (Over.mk x ⟶ Over.mk e) := Classical.decEq _
        ∀ (z : Over.mk x ⟶ Over.mk e)
        (a : ((Scheme.pointSmallEtale z.left).sheafFiber
          (A := ModuleCat.{u + 1} A)).obj ((upperStar (ModuleCat.{u + 1} A) e).obj F)),
        ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app F)
          ((etaleProjectionSumStalkIso A e x
            ((upperStar (ModuleCat.{u + 1} A) e).obj F)).inv
              (DirectSum.lof A _ _ z a)) = (etaleProjectionLiftStalkIso A e x z F).hom a) ∧
      (∀ M, P U M → P T (E.obj M)) ∧
      (∀ B, P T B → P U (R.obj B)) ∧
      (∀ (B : DerivedCategoryModule A T), P T B →
        ∀ (M : DerivedCategoryModule A U), P U M →
          Function.Bijective (fun b : M ⟶ R.obj B ↦ E.map b ≫ s.counit.app B)) ∧
      (∀ M, P T M → P Y (L.obj M)) ∧
      (∀ (K : DerivedCategoryModule A Y), P Y K →
        P T (Q K) ∧
        (∀ (M : DerivedCategoryModule A T), P T M →
          Function.Bijective (fun b : M ⟶ Q K ↦ L.map b ≫
            OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K)) ∧
        (∃ proj : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
            (L.obj W) ≅ L.obj (Q K),
          proj.hom = compactSupportProjectionMap A p W K ∧
          OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K =
            proj.inv ≫ ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
              (OrdinaryAffineCounitTensorNormalization.trace A N hN hA t D Y hY d) ≫
                (derivedTensorSingleUnitIso K).hom) ∧
        (∀ B : RepresentingPair ell n f K, P X B.object →
          ∃! α :
            (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj B.object ≅
              R.obj (Q K),
          (E ⋙ L).map α.hom ≫
            L.map (s.counit.app (Q K)) ≫
              OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K =
            finiteChartBrownCounit A f j d e he
              (HasCompactification.compactification f) B.object K B.counit)) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : HasCompactification f := cf.hasCompactification
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  intro hY A N hA hN P T p L E R s W Q
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have : IsNoetherian T := affineTraceNoetherian Y d
  let : T.Over (Spec (.of k)) := ⟨p ≫ (Y ↘ Spec (.of k))⟩
  have : p.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType p := affineTraceProjection_locallyOfFiniteType Y d
  have : QuasiCompact p := affineTraceProjection_quasiCompact Y d
  have : IsSeparated p := affineTraceProjection_isSeparated Y d
  have : LocallyOfFiniteType (T ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (p ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (T ↘ Spec (.of k)) := by
    change QuasiCompact (p ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (T ↘ Spec (.of k)) := by
    change IsSeparated (p ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : e.IsOver (Spec (.of k)) := ⟨by
    change e ≫ (p ≫ (Y ↘ Spec (.of k))) = U ↘ Spec (.of k)
    rw [← Category.assoc, ← he]
    exact comp_over (j ≫ f) _⟩
  obtain ⟨t, D, ht, hD⟩ := exists_affineSpaceTopTrace N hN A hA
  let norm := canonicalEtaleCompactSupportNormalization A
  have hE : ∀ M, P U M → P T (E.obj M) := by
    intro M hM
    let c := HasCompactification.compactification e
    exact chart_property_of_iso A T ((norm.comparison e c).app M)
      (chart_compact_preserves ell n k A hA e c M hM)
  have hR : ∀ B, P T B → P U (R.obj B) :=
    chart_pullback_preserves ell n k A hA e
  have hL : ∀ M, P T M → P Y (L.obj M) :=
    chart_compact_preserves ell n k A hA p (HasCompactification.compactification p)
  have hs : ∀ B, P T B → ∀ M, P U M →
      Function.Bijective (fun b : M ⟶ R.obj B ↦ E.map b ≫ s.counit.app B) := by
    intro B _ M _
    change Function.Bijective (fun b ↦ (s.homEquiv M B).symm b)
    exact (s.homEquiv M B).symm.bijective
  refine ⟨t, D, ⟨inferInstance, inferInstance⟩, ?_, hE, hR, hs, hL, ?_⟩
  · intro F Ω _ _ x z a
    exact chart_sum_counit_stalk A e F Ω x z a
  · intro K hK
    have hQ : P T (Q K) := by
      have h := chart_twist_preserves ell n k A hA p d (2 * (d : ℤ)) K hK
      have := _root_.DerivedCategory.braidedCategory'
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
      let eQ : (ProEtale.AdjunctionTransfer.etaleChartOperation A N hA p d
          (2 * (d : ℤ))).obj K ≅ Q K :=
        (shiftFunctor _ (2 * (d : ℤ))).mapIso (β_ _ _) ≪≫
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj
          ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)).commShiftIso
            (2 * (d : ℤ))).symm.app
              ((_root_.DerivedCategory.singleFunctor _ 0).obj
                (Scheme.finiteEtaleTateTwist T N A hA d))
      exact chart_property_of_iso A T eQ h
    let adj := (affineTraceAdjunction A N hA t D Y hY d).ofNatIsoLeft
      (affineDualizingTowerComparison A Y d)
    have hq : ∀ M, P T M → Function.Bijective (fun b : M ⟶ Q K ↦ L.map b ≫
        OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K) := by
      intro M _
      let r := OrdinaryAffineCounitTensorNormalization.reassociation A N hN hA t Y hY d K
      have hb := (adj.homEquiv M K).symm.bijective.comp r.symm.homToEquiv.bijective
      convert hb using 1
      funext b
      change L.map b ≫
          OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K =
        (adj.homEquiv M K).symm (b ≫ r.inv)
      rw [Adjunction.homEquiv_counit, Functor.map_comp]
      simp only [OrdinaryAffineCounitTensorNormalization.counit, r, adj,
        Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
        Functor.whiskerLeft_app, L, Category.assoc]
      rfl
    refine ⟨hQ, hq, ordinaryAffineCounit_tensor_normalization N hN A hA t D Y hY d K, ?_⟩
    intro B hB
    let cb := HasCompactification.compactification f
    let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb
    let J := (etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategory
    let Rj := (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
    let adjJ := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategoryAdjunction
    let c := finiteChartLeftComparison A f j d e he cb
    have hJ : ∀ M, P U M → P X (J.obj M) := by
      intro M hM
      let cj := HasCompactification.compactification j
      exact chart_property_of_iso A X ((norm.comparison j cj).app M)
        (chart_compact_preserves ell n k A hA j cj M hM)
    have hbH : ∀ M, P U M → Function.Bijective
        (fun b : M ⟶ Rj.obj B.object ↦
          (E ⋙ L).map b ≫ finiteChartBrownCounit A f j d e he cb B.object K B.counit) := by
      intro M hM
      have hJM := hJ M hM
      obtain ⟨a, b, hb⟩ := hJM.2
      have htor : ∃ a b, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b (J.obj M) :=
        ⟨min a b, b, min_le_right _ _,
          DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
            (hb.mono (min_le_left _ _) le_rfl)⟩
      have hm := B.map_bijective (J.obj M) hJM.1 htor
      have h := (c.app M).symm.homFromEquiv.bijective.comp
        (hm.comp (adjJ.homEquiv M B.object).symm.bijective)
      convert h using 1
      funext b
      dsimp only [Function.comp_def, Iso.homFromEquiv_apply]
      rw [Adjunction.homEquiv_counit]
      change (E ⋙ L).map b ≫ c.hom.app (Rj.obj B.object) ≫
          F.map (adjJ.counit.app B.object) ≫ B.counit =
        c.hom.app M ≫ F.map (J.map b ≫ adjJ.counit.app B.object) ≫ B.counit
      rw [Functor.map_comp]
      have hn := c.hom.naturality b
      change (E ⋙ L).map b ≫ c.hom.app (Rj.obj B.object) =
        c.hom.app M ≫ F.map (J.map b) at hn
      simp only [← Category.assoc]
      rw [hn]
    have hbG : ∀ M, P U M → Function.Bijective
        (fun b : M ⟶ R.obj (Q K) ↦ (E ⋙ L).map b ≫
          (L.map (s.counit.app (Q K)) ≫
            OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K)) := by
      intro M hM
      simpa only [Function.comp_def, Functor.comp_obj, Functor.comp_map,
        Functor.map_comp, Category.assoc] using
        (hq (E.obj M) (hE M hM)).comp (hs (Q K) hQ M hM)
    exact chart_unique (E ⋙ L) (P U)
      (chart_pullback_preserves ell n k A hA j B.object hB)
      (hR (Q K) hQ) _ _ hbH hbG

end AlgebraicGeometry.Etale
