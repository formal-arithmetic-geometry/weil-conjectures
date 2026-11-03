/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBundle
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBaseChange
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorNormalizedUnitAdjunct
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-! # Cartesian transport of the normalized vector-bundle trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Etale (RfPullback RfShriek RfUpper purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting.OrientationRefinement

attribute [local implicit_reducible] Scheme.Modules

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.vectorBundleIntegration

-- Reuse the canonical localization instances cached by the ordinary pullback.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1
  Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3
  Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5
  Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7
  Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9
  Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11
  Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Etale.leftDerivedUpperStarIsoMapDerivedCategory

private theorem trace_of_mate_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (ex : L ⋙ H ≅ G ⋙ L') {W : C} {W' : C'} {U : D} {U' : D'}
    (a : G.obj W ⟶ W') (t : L.obj W ⟶ U) (t' : L'.obj W' ⟶ U')
    (c : H.obj U ⟶ U')
    (ht : G.map (adj.homEquiv W U t) ≫
      (mateEquiv adj adj' (TwoSquare.mk G L L' H ex.inv)).natTrans.app U ≫ R'.map c =
      a ≫ adj'.homEquiv W' U' t') :
    ex.hom.app W ≫ L'.map a ≫ t' = H.map t ≫ c := by
  have h := congrArg ((adj'.homEquiv _ _).symm) ht
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc] at h
  have hc := adj'.counit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc] at h
  rw [reassoc_of% (mateEquiv_counit adj adj' (TwoSquare.mk G L L' H ex.inv) U)] at h
  rw [reassoc_of% ex.inv.naturality (adj.homEquiv W U t)] at h
  rw [← H.map_comp_assoc, ← adj.homEquiv_counit, Equiv.symm_apply_apply] at h
  rw [← adj'.homEquiv_counit, Equiv.symm_apply_apply] at h
  have h' := congrArg (fun k ↦ ex.hom.app W ≫ k) h
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using h'.symm

private theorem tensor_unit_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G : C ⥤ D) (μ : ∀ X Y, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (hμ : ∀ (X Y Z : C) (f : Y ⟶ Z), G.map (X ◁ f) ≫ μ X Z =
      μ X Y ≫ G.obj X ◁ G.map f)
    (unit : G.obj (𝟙_ C) ≅ 𝟙_ D)
    (hu : ∀ X, μ X (𝟙_ C) ≫ G.obj X ◁ unit.hom ≫ (ρ_ (G.obj X)).hom =
      G.map (ρ_ X).hom)
    (W U : C) (W' V : D) (e : U ≅ 𝟙_ C) (e' : V ≅ 𝟙_ D)
    (k : G.obj W ⟶ W') (q : G.obj U ⟶ V)
    (hq : q ≫ e'.hom = G.map e.hom ≫ unit.hom) :
    G.map ((ρ_ W).inv ≫ W ◁ e.inv) ≫ μ W U ≫ (k ⊗ₘ q) =
      k ≫ (ρ_ W').inv ≫ W' ◁ e'.inv := by
  apply (cancel_mono (W' ◁ e'.hom ≫ (ρ_ W').hom)).1
  simp only [Category.assoc, MonoidalCategory.tensorHom_def]
  rw [← whiskerLeft_comp_assoc, hq, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [reassoc_of% (hμ W U (𝟙_ C) e.hom).symm]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc (W ◁ e.inv) (W ◁ e.hom)]
  simp only [← whiskerLeft_comp, e.inv_hom_id, whiskerLeft_id,
    G.map_id, Category.id_comp]
  rw [← whisker_exchange_assoc k unit.hom, rightUnitor_naturality]
  rw [reassoc_of% hu W]
  simp

private theorem pullback_square_unit
    (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) :
    (purityPullbackSquare A sq (𝟙_ _)).hom ≫
      (RfPullback A f').map (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f').hom =
    (RfPullback A g').map (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g').hom := by
  simp only [Etale.leftDerivedUpperStarUnitIso_hom_eq_η,
    purityPullbackSquare, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Etale.ordinaryFinitePullback]
  rw [Etale.leftDerivedUpperStarComp_hom_app_unit,
    ← Etale.leftDerivedUpperStarComp_hom_app_unit _ g' f (g' ≫ f) rfl,
    Iso.inv_hom_id_app_assoc]

private theorem bundle_source_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    {b : B' ⟶ B}
    {v : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) b) :
    let W := Etale.vectorIntegrationCoefficient A N hA B d F
    let W' := Etale.vectorIntegrationCoefficient A N hA B' d F'
    let π := VectorBundleZeroSection.π B d F
    let π' := VectorBundleZeroSection.π B' d F'
    (RfPullback A v).map
        ((ρ_ W).inv ≫ W ◁ (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π).inv) ≫
      (purityBundleBaseChangeAssociator A N hN hA hB d F F' sq (𝟙_ _)).hom ≫
      W' ◁ (RfPullback A π').map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) b).hom =
    ((purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d)).hom ≫
      (RfPullback A π').map (Etale.vectorIntegrationBaseCoefficientPullback A N hA
        (purityTwistTransport A N hN hA) b hB d).hom) ≫
      (ρ_ W').inv ≫ W' ◁
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π').inv := by
  dsimp only
  let W := Etale.vectorIntegrationCoefficient A N hA B d F
  let W' := Etale.vectorIntegrationCoefficient A N hA B' d F'
  let π := VectorBundleZeroSection.π B d F
  let π' := VectorBundleZeroSection.π B' d F'
  let k := (purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d)).hom ≫
    (RfPullback A π').map (Etale.vectorIntegrationBaseCoefficientPullback A N hA
      (purityTwistTransport A N hN hA) b hB d).hom
  have h := tensor_unit_square (RfPullback A v)
    (fun X Y ↦ ((Etale.leftDerivedUpperStarTensorComparison
      (ModuleCat.{u + 1} A) v).app X).app Y)
    (fun X Y Z f ↦ ((Etale.leftDerivedUpperStarTensorComparison
      (ModuleCat.{u + 1} A) v).app X).naturality f)
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v)
    (Etale.leftDerivedUpperStarTensorComparison_rightUnitor_hom (ModuleCat.{u + 1} A) v)
    W ((RfPullback A π).obj (𝟙_ _)) W' ((RfPullback A π').obj (𝟙_ _))
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π)
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π') k
    ((purityPullbackSquare A sq (𝟙_ _)).hom ≫ (RfPullback A π').map
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) b).hom)
    (by simpa only [Category.assoc] using pullback_square_unit A sq)
  simp only [purityBundleBaseChangeAssociator, Iso.trans_hom, tensorIso_hom,
    Functor.mapIso_hom, MonoidalCategory.tensorHom_def, Category.assoc,
    Etale.leftDerivedUpperStarTensorIso_hom]
  simp only [W, W', π, π', k, MonoidalCategory.tensorHom_def,
    whiskerLeft_comp, Category.assoc] at h
  dsimp only [RfPullback, Etale.ordinaryFinitePullback, Etale.DerivedCategoryModule] at h ⊢
  exact h

private theorem change_trace_coefficient
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (L : C ⥤ D) (L' : C' ⥤ D') (G : C ⥤ C') (H : D ⥤ D')
    (ex : L ⋙ H ≅ G ⋙ L') {W T : C} {W' T' : C'} {U : D} {U' : D'}
    (j : W ≅ T) (j' : W' ≅ T') (k : G.obj W ⟶ W') (c : G.obj T ⟶ T')
    (t : L.obj W ⟶ U) (t' : L'.obj W' ⟶ U') (u : H.obj U ⟶ U')
    (hk : G.map j.inv ≫ k = c ≫ j'.inv)
    (ht : ex.hom.app W ≫ L'.map k ≫ t' = H.map t ≫ u) :
    ex.hom.app T ≫ L'.map c ≫ (L'.map j'.inv ≫ t') =
      H.map (L.map j.inv ≫ t) ≫ u := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← L'.map_comp_assoc, ← hk, L'.map_comp]
  simp only [Category.assoc]
  have he := ex.hom.naturality j.inv
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he.symm, ht]

/-- The trace calculation with abstract finite coefficients keeps the derived-category
instances independent of the concrete coefficient quotient. -/
private theorem finite_trace_cartesian
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B B' : Scheme.{u}) [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    (b : B' ⟶ B)
    (v : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F)
    (sq : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) b)
    (hE : IsUnit (N : Γ(VectorBundleZeroSection.scheme B d F, ⊤))) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := (Etale.vectorIntegration_geometry B' d F').1
    letI := (Etale.vectorIntegration_geometry B' d F').2.1
    let tw := purityTwistTransport A N hN hA
    let π := VectorBundleZeroSection.π B d F
    let π' := VectorBundleZeroSection.π B' d F'
    let L := RfShriek A π
    let L' := RfShriek A π'
    let j := Etale.vectorIntegrationBaseCoefficientPullback A N hA tw π hB d
    let j' := Etale.vectorIntegrationBaseCoefficientPullback A N hA tw π' hB' d
    let t := Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom
    let t' := Etale.vectorBundleIntegration N hN A hA B' hB' d F' ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B').hom
    (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app
        (Etale.affineLinearBaseCoefficient A N hA (VectorBundleZeroSection.scheme B d F) d) ≫
      L'.map (Etale.vectorIntegrationBaseCoefficientPullback A N hA tw v hE d).hom ≫
        (L'.map j'.inv ≫ t') =
      (RfPullback A b).map (L.map j.inv ≫ t) ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) b).hom := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B' d F').1
  let := (Etale.vectorIntegration_geometry B' d F').2.1
  let π := VectorBundleZeroSection.π B d F
  let π' := VectorBundleZeroSection.π B' d F'
  let W := Etale.vectorIntegrationCoefficient A N hA B d F
  let W' := Etale.vectorIntegrationCoefficient A N hA B' d F'
  let L := RfShriek A π
  let L' := RfShriek A π'
  let G := RfPullback A v
  let H := RfPullback A b
  let adj := Etale.rightDerivedUpperShriekAdjunction A π
  let adj' := Etale.rightDerivedUpperShriekAdjunction A π'
  let uB := Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) b
  let s := (ρ_ W).inv ≫
    W ◁ (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π).inv
  let s' := (ρ_ W').inv ≫
    W' ◁ (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) π').inv
  let t := Etale.vectorBundleIntegration N hN A hA B hB d F ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom
  let t' := Etale.vectorBundleIntegration N hN A hA B' hB' d F' ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B').hom
  let tw := purityTwistTransport A N hN hA
  let k := (purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d)).hom ≫
    (RfPullback A π').map
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA tw b hB d).hom
  obtain ⟨_, γ, hn, hi⟩ := vectorBundleNormalized A N hN hA B hB d F
  obtain ⟨γ', hn', hbc⟩ :=
    vectorIntegrationCounit_baseChange A N hN hA B hB d F γ hn hi B' b hB' F' v sq
  have hbc' := (hbc ⟨𝟙_ _, Etale.constructibleFiniteTor_tensorUnit A B⟩).2
  have hγ : s ≫ γ.app (𝟙_ _) = adj.homEquiv _ _ t := by
    exact vector_normalized_unit_adjunct A N hN hA B hB d F γ hn
  have hγ' : s' ≫ γ'.app (𝟙_ _) = adj'.homEquiv _ _ t' := by
    exact vector_normalized_unit_adjunct A N hN hA B' hB' d F' γ' hn'
  have hsource : G.map s ≫
      (purityBundleBaseChangeAssociator A N hN hA hB d F F' sq (𝟙_ _)).hom ≫
        W' ◁ (RfPullback A π').map uB.hom = k ≫ s' :=
    bundle_source_unit A N hN hA hB d F F' sq
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let ex : L ⋙ H ≅ G ⋙ L' := asIso (Etale.rightDerivedLowerShriekBaseChangeMap A sq)
  have hm : G.map (adj.homEquiv _ _ t) ≫
      (mateEquiv adj adj' (TwoSquare.mk G L L' H ex.inv)).natTrans.app (𝟙_ _) ≫
        (RfUpper A π').map uB.hom =
      k ≫ adj'.homEquiv _ _ t' := by
    rw [← hγ, G.map_comp]
    simp only [Category.assoc]
    change G.map s ≫ G.map (γ.app (𝟙_ _)) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app (𝟙_ _) ≫
        (RfUpper A π').map uB.hom = _
    rw [reassoc_of% hbc']
    have hnat : W' ◁ (RfPullback A π').map uB.hom ≫ γ'.app (𝟙_ _) =
        γ'.app ((RfPullback A b).obj (𝟙_ _)) ≫ (RfUpper A π').map uB.hom := by
      exact γ'.naturality uB.hom
    rw [← hnat]
    rw [reassoc_of% hsource, hγ']
    rfl
  have ht := trace_of_mate_square adj adj' G H ex k t t' uB.hom hm
  let j := Etale.vectorIntegrationBaseCoefficientPullback A N hA tw π hB d
  let j' := Etale.vectorIntegrationBaseCoefficientPullback A N hA tw π' hB' d
  let cv := Etale.vectorIntegrationBaseCoefficientPullback A N hA tw v hE d
  have hk : G.map j.inv ≫ k = cv.hom ≫ j'.inv := by
    simpa only [G, j, j', k, cv, purityPullbackSquare, Iso.trans_hom, Iso.app_hom,
      NatTrans.comp_app, Iso.symm_hom, Category.assoc] using
      Etale.orderedTatePullbackSquare A N hA tw π π' v b sq.w.symm
        hB hE hB' d
  exact change_trace_coefficient L L' G H ex j j' k cv.hom t t' uB.hom hk ht

-- The general base-change law also covers maps preserving the zero section.
set_option linter.unusedVariables false in
/-- Integration, after moving the Tate coefficient to the total space, commutes
with a zero-preserving Cartesian presentation. This is an equation of compact
support traces, before taking any adjunction mate or zero-section inverse image.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, compatibility paragraph, and the zero-section
normalization of vector-bundle purity.
(blueprint: lem-pur-vector-normalized-trace-cartesian).

Proof: apply vectorBundleNormalized at the positive diagonal exponent to construct
an independently normalized family gamma, then vectorIntegrationCounit_baseChange
to obtain the normalized family gamma' on the Cartesian presentation and its
base-change equation. Test the equation on the coefficient tensor unit, which is
bounded constructible with finite Tor amplitude. Naturality of gamma' along the
pullback unit comparison moves its pulled-back-unit component to its unit component.
For either family the normalization equation at the unit and right-unitality of
the compact-support projection identify gamma at the unit, after the source unit
isomorphism, with the Brown adjunct of the actual vectorBundleIntegration followed
by singleFunctorObjUnitIso. Apply the inverse Brown Hom equivalence to the
base-change equation. The mate counit identity turns the exceptional exchange
into inverse compact-support exchange. Cancel that inverse exchange to recover
the compact-support trace square. Insert Rpi_!(c_pi inverse) and the corresponding
factor for pi'. The normalized finite Tate composition equation around the
Cartesian projection square identifies the resulting coefficient map with c_v.
The constant-to-unit pullback comparison is the actual monoidal unit comparison,
so the remaining arrows are precisely those displayed. The same projection-unit
and coefficient equations hold in
rank zero, on an empty base, and at every positive coefficient level.
-/
theorem vector_normalized_trace_cartesian (P : PurityFiniteSetting.{u})
    (B B' : Scheme.{u}) [IsNoetherian B] [IsNoetherian B']
    (aB : B ⟶ Spec (.of P.field.k)) (aB' : B' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    (b : B' ⟶ B)
    (v : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F)
    (sq : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) b)
    (hz : VectorBundleZeroSection.zero B' d F' ≫ v =
      b ≫ VectorBundleZeroSection.zero B d F) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := (Etale.vectorIntegration_geometry B' d F').1
    letI := (Etale.vectorIntegration_geometry B' d F').2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
    let t := purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
    let c (T S : Scheme.{u}) (f : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) :=
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t f (P.diagonalExponent_isUnit aS) d
    let π := VectorBundleZeroSection.π B d F
    let π' := VectorBundleZeroSection.π B' d F'
    let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π
    let L' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π'
    let τ := L.map (c _ _ π aB).inv ≫
      Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
    let τ' := L'.map (c _ _ π' aB').inv ≫
      Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B' (P.diagonalExponent_isUnit aB') d F' ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B').hom
    (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq).app
        (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates (VectorBundleZeroSection.scheme B d F) d) ≫
      L'.map (c _ _ v (π ≫ aB)).hom ≫ τ' =
    (Etale.ordinaryFinitePullback P.Coefficient b).map τ ≫
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom  := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let := (Etale.vectorIntegration_geometry B' d F').1
  let := (Etale.vectorIntegration_geometry B' d F').2.1
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
  let := Dnc.compactifiable P (VectorBundleZeroSection.π B' d F') aB'
  exact finite_trace_cartesian P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
    B B' (P.diagonalExponent_isUnit aB) (P.diagonalExponent_isUnit aB')
    d F F' b v sq (P.diagonalExponent_isUnit (VectorBundleZeroSection.π B d F ≫ aB))

end WeilConjectures.PurityFiniteSetting.OrientationRefinement
