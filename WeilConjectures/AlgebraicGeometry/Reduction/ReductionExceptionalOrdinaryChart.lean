/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartIdentityScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCounitScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSumNormalization
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactTowerScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartCompactScalar
public import WeilConjectures.AlgebraicGeometry.OrdinaryChart.OrdinaryChartAdjunctionObjects

/-! # The ordinary chart transpose calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
private theorem right_exchange_rec_eq {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    (R : ∀ d, C d ⥤ C (d + 1)) (R' : ∀ d, C' d ⥤ C' (d + 1))
    (B : ∀ d, C d ⥤ C' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (d : ℕ) (K : C 0) :
    (Nat.rec (motive := fun n ↦ ∀ K : C 0,
      (B n).obj ((affineTraceRightTower R n).obj K) ≅
        (affineTraceRightTower R' n).obj ((B 0).obj K))
      (fun _ ↦ Iso.refl _) (fun n ih K ↦ r n _ ≪≫ (R' n).mapIso (ih K)) d K) =
      affineTraceRightExchangeTower R R' B r d K := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [affineTraceRightExchangeTower]
    rw [ih]

private theorem tower_counit_scalar {C C' : ℕ → Type*}
    [∀ d, Category (C d)] [∀ d, Category (C' d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {L' : ∀ d, C' (d + 1) ⥤ C' d}
    {R : ∀ d, C d ⥤ C (d + 1)} {R' : ∀ d, C' d ⥤ C' (d + 1)}
    (a : ∀ d, L d ⊣ R d) (a' : ∀ d, L' d ⊣ R' d)
    (B : ∀ d, C d ⥤ C' d) (e : ∀ d, L d ⋙ B d ⟶ B (d + 1) ⋙ L' d)
    (r : ∀ d K, (B (d + 1)).obj ((R d).obj K) ≅ (R' d).obj ((B d).obj K))
    (K : C 0)
    (h : ∀ d, (e d).app ((R d).obj ((affineTraceRightTower R d).obj K)) ≫
      (L' d).map (r d ((affineTraceRightTower R d).obj K)).hom ≫
        (a' d).counit.app ((B d).obj ((affineTraceRightTower R d).obj K)) =
        (B d).map ((a d).counit.app ((affineTraceRightTower R d).obj K))) (d : ℕ) :
    (affineTraceExchangeTower L L' B e d).app ((affineTraceRightTower R d).obj K) ≫
      (affineTraceLeftTower L' d).map (affineTraceRightExchangeTower R R' B r d K).hom ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) =
    (B 0).map ((affineTraceAdjunctionTower a d).counit.app K) := by
  induction d with
  | zero =>
    rw [affineTraceExchangeTower_zero]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (B 0).map (𝟙 K)
    simp
  | succ d ih =>
    let M := (affineTraceRightTower R d).obj K
    let q := affineTraceRightExchangeTower R R' B r d K
    have hn := (a' d).counit.naturality q.hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hi : (e d).app ((R d).obj M) ≫
        (L' d).map ((r d M).hom ≫ (R' d).map q.hom) ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K)) =
        (B d).map ((a d).counit.app M) ≫ q.hom := by
      rw [Functor.map_comp, Category.assoc, hn]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ q.hom) (h d)
    rw [affineTraceExchangeTower_succ, affineTraceAdjunctionTower_counit_succ,
      affineTraceAdjunctionTower_counit_succ]
    change (_ ≫ (affineTraceLeftTower L' d).map ((e d).app ((R d).obj M))) ≫
      (affineTraceLeftTower L' d).map
        ((L' d).map ((r d M).hom ≫ (R' d).map q.hom)) ≫
      (affineTraceLeftTower L' d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj ((B 0).obj K))) ≫
      (affineTraceAdjunctionTower a' d).counit.app ((B 0).obj K) = _
    have hi' := congrArg (fun z ↦ (affineTraceLeftTower L' d).map z) hi
    simp only [Functor.map_comp, Category.assoc] at hi'
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hi']
    have he := (affineTraceExchangeTower L L' B e d).naturality ((a d).counit.app M)
    simp only [Functor.comp_map] at he
    change _ ≫ (affineTraceExchangeTower L L' B e d).app M =
      (affineTraceExchangeTower L L' B e d).app
        ((L d).obj ((affineTraceRightTower R (d + 1)).obj K)) ≫ _ at he
    rw [← Category.assoc, ← Category.assoc, ← he]
    simp only [Category.assoc]
    rw [ih, ← Functor.map_comp]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] affineTraceTower
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

private theorem rightAdjointUniq_scalar_of_counits
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G J : D ⥤ C} {F' : C' ⥤ D'} {G' J' : D' ⥤ C'}
    (g : F ⊣ G) (j : F ⊣ J) (g' : F' ⊣ G') (j' : F' ⊣ J')
    (S : C ⥤ C') (T : D ⥤ D') (b : F ⋙ T ⟶ S ⋙ F')
    (K : D) (K' : D') (v : T.obj K ⟶ K')
    (q : S.obj (G.obj K) ⟶ G'.obj K')
    (a : S.obj (J.obj K) ⟶ J'.obj K')
    (hq : b.app (G.obj K) ≫ F'.map q ≫ g'.counit.app K' =
      T.map (g.counit.app K) ≫ v)
    (hb : Epi (b.app (G.obj K)))
    (ha : b.app (J.obj K) ≫ F'.map a ≫ j'.counit.app K' =
      T.map (j.counit.app K) ≫ v) :
    S.map ((g.rightAdjointUniq j).hom.app K) ≫ a =
      q ≫ (g'.rightAdjointUniq j').hom.app K' := by
  have := hb
  apply (j'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (b.app (G.obj K))).mp
  rw [g'.rightAdjointUniq_hom_app_counit j']
  rw [hq]
  have hn := b.naturality ((g.rightAdjointUniq j).hom.app K)
  change T.map (F.map _) ≫ b.app (J.obj K) =
    b.app (G.obj K) ≫ F'.map (S.map _) at hn
  rw [← reassoc_of% hn, ha, ← T.map_comp_assoc, g.rightAdjointUniq_hom_app_counit j]

private def scalarComposite
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {M : D ⥤ E} {L' : C' ⥤ D'} {M' : D' ⥤ E'}
    {S : C ⥤ C'} {T : D ⥤ D'} {U : E ⥤ E'}
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M') :
    (L ⋙ M) ⋙ U ⟶ S ⋙ (L' ⋙ M') where
  app X := γ.app (L.obj X) ≫ M'.map (β.app X)
  naturality X Y f := by
    have hγ := γ.naturality (L.map f)
    have hβ := β.naturality f
    simp only [Functor.comp_map] at hγ hβ ⊢
    rw [← Category.assoc, hγ, Category.assoc, ← M'.map_comp, hβ]
    simp only [Functor.map_comp, Category.assoc]

private theorem compose_counit_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {Q : E ⥤ D}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {M' : D' ⥤ E'} {Q' : E' ⥤ D'}
    (a : L ⊣ R) (b : M ⊣ Q) (a' : L' ⊣ R') (b' : M' ⊣ Q')
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (β : L ⋙ T ⟶ S ⋙ L') (γ : M ⋙ U ⟶ T ⋙ M')
    (K : E) (r : S.obj (R.obj (Q.obj K)) ⟶ R'.obj (T.obj (Q.obj K)))
    (q : T.obj (Q.obj K) ⟶ Q'.obj (U.obj K))
    (hr : β.app (R.obj (Q.obj K)) ≫ L'.map r ≫ a'.counit.app (T.obj (Q.obj K)) =
      T.map (a.counit.app (Q.obj K)))
    (hq : γ.app (Q.obj K) ≫ M'.map q ≫ b'.counit.app (U.obj K) =
      U.map (b.counit.app K)) :
    γ.app (L.obj (R.obj (Q.obj K))) ≫ M'.map (β.app (R.obj (Q.obj K))) ≫
      M'.map (L'.map (r ≫ R'.map q)) ≫ (a'.comp b').counit.app (U.obj K) =
      U.map ((a.comp b).counit.app K) := by
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  have hn := a'.counit.naturality q
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg (fun z ↦ M'.map z) hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  have hr' := congrArg (fun z ↦ M'.map z) hr
  simp only [Functor.map_comp] at hr'
  rw [reassoc_of% hr']
  have hm := γ.naturality (a.counit.app (Q.obj K))
  simp only [Functor.comp_map] at hm
  rw [← reassoc_of% hm, hq, ← U.map_comp]

private theorem composite_left_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    {F Fc : C ⥤ D} {G Gc : D ⥤ E}
    {F' Fc' : C' ⥤ D'} {G' Gc' : D' ⥤ E'}
    (S : C ⥤ C') (T : D ⥤ D') (U : E ⥤ E')
    (f : F ⋙ T ⟶ S ⋙ F') (fc : Fc ⋙ T ⟶ S ⋙ Fc')
    (g : G ⋙ U ⟶ T ⋙ G') (gc : Gc ⋙ U ⟶ T ⋙ Gc')
    (a : F ≅ Fc) (a' : F' ≅ Fc') (b : G ≅ Gc) (b' : G' ≅ Gc')
    (ha : ∀ X, T.map (a.hom.app X) ≫ fc.app X = f.app X ≫ a'.hom.app (S.obj X))
    (hb : ∀ Y, U.map (b.hom.app Y) ≫ gc.app Y = g.app Y ≫ b'.hom.app (T.obj Y))
    (X : C) :
    U.map (G.map (a.hom.app X) ≫ b.hom.app (Fc.obj X)) ≫
        gc.app (Fc.obj X) ≫ Gc'.map (fc.app X) =
      g.app (F.obj X) ≫ G'.map (f.app X) ≫
        G'.map (a'.hom.app (S.obj X)) ≫ b'.hom.app (Fc'.obj (S.obj X)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hb (Fc.obj X))]
  have hn := g.naturality (a.hom.app X)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn' := b'.hom.naturality (fc.app X)
  simp only [Functor.comp_obj] at hn'
  rw [← hn']
  rw [← G'.map_comp_assoc, ha, G'.map_comp]
  simp only [Category.assoc]

private theorem transported_counit_scalar
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F H : C ⥤ D} {J : D ⥤ C} {F' H' : C' ⥤ D'} {J' : D' ⥤ C'}
    (a : H ⊣ J) (a' : H' ⊣ J') (e : H ≅ F) (e' : H' ≅ F')
    (S : C ⥤ C') (T : D ⥤ D')
    (β : F ⋙ T ⟶ S ⋙ F') (γ : H ⋙ T ⟶ S ⋙ H')
    (K : D) (r : S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (hs : ∀ X, T.map (e.hom.app X) ≫ β.app X = γ.app X ≫ e'.hom.app (S.obj X))
    (hc : γ.app (J.obj K) ≫ H'.map r ≫ a'.counit.app (T.obj K) =
      T.map (a.counit.app K)) :
    β.app (J.obj K) ≫ F'.map r ≫
      (a'.ofNatIsoLeft e').counit.app (T.obj K) =
        T.map ((a.ofNatIsoLeft e).counit.app K) := by
  apply (cancel_epi (T.map (e.hom.app (J.obj K)))).mp
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp]
  rw [reassoc_of% (hs (J.obj K))]
  have hn := e'.inv.naturality r
  rw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc, ← T.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hc

private def affineLeftScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (S : Scheme.{u}) (d : ℕ) :
    affineTraceLeft A S d ⋙ scalarExtension φ S ⟶
      scalarExtension φ (affineTraceTower S d) ⋙ affineTraceLeft B S d :=
  affineTraceExchangeTower
    (fun r ↦ affineTraceLineLeft A (affineTraceTower S r))
    (fun r ↦ affineTraceLineLeft B (affineTraceTower S r))
    (fun r ↦ scalarExtension φ (affineTraceTower S r))
    (fun r ↦ compactScalarMap φ (affineTraceLineCompactification
      (affineTraceTower S r))) d

attribute [local irreducible] affineLeftScalar

private theorem sum_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] (K : DerivedCategoryModule A V) :
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app
        ((ordinaryFinitePullback A e).obj K) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
        ((scalarPullbackIso φ e).inv.app K) ≫
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) e).symm).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      (((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) e).symm).counit.app K) := by
  have h := firstDerived_eq_second φ e K
  let jA := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  let jB := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e
  have hn := (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.naturality
    (jA.hom.app K)
  simp only [Functor.comp_map] at hn
  have hh := congrArg (fun z ↦ (scalarExtension φ V).map
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
      (jA.hom.app K)) ≫ z) h
  simp only [etaleCounitScalarFirstDerived, properOpenCoefficientPullbackIso,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, Functor.map_comp,
    Category.assoc] at hh
  rw [reassoc_of% hn] at hh
  dsimp only [jA, jB] at hh
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simpa only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, ordinaryFinitePullback,
    Iso.symm_inv, Functor.map_comp, Category.assoc, jA, jB] using hh

private theorem line_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (DB : OrdinaryFiniteP1Datum B N hB tB S hS)
    (K : DerivedCategoryModule A S) :
    (compactScalarMap φ (affineTraceLineCompactification S)).app
        ((affineTraceLineRight A N hA S).obj K) ≫
      (affineTraceLineLeft B S).map
        (ProEtale.reductionEtaleLineScalarIso φ S N hA hB hS K).hom ≫
      (affineTraceLineAdjunction B N hB tB S hS DB).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((affineTraceLineAdjunction A N hA tA S hS DA).counit.app K) := by
  have h := compose_counit_scalar
    (affineTraceOpenAdjunction A S) DA.adjunction
    (affineTraceOpenAdjunction B S) DB.adjunction
    (scalarExtension φ (AffineSpace PUnit.{u + 1} S))
    (scalarExtension φ (ProjectiveLine S)) (scalarExtension φ S)
    (ExceptionalCoefficients.openIso φ (ProjectiveLine.affineChart S)).hom
    (scalarMate φ (ProjectiveLine S ↘ S)) K
    ((scalarPullbackIso φ (ProjectiveLine.affineChart S)).inv.app
      ((ordinaryFiniteP1Right A N hA S).obj K))
    (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom
    (by simpa only [affineTraceOpenAdjunction, affineTraceOpenLeft] using
      (open_scalar_counit φ (ProjectiveLine.affineChart S)
        ((ordinaryFiniteP1Right A N hA S).obj K)))
    (ordinaryChartP1CounitScalar φ N hN hA hB S hS tA tB DA DB K)
  simpa only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    affineTraceLineCompactification, Compactification.copy, Functor.comp_map,
    ProEtale.reductionEtaleLineScalarIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, affineTraceLineAdjunction, affineTraceComposeAdjunction_eq,
    affineTraceOpenLeft, affineTraceLineRight, affineTraceLineLeft,
    rightDerivedLowerShriekOfCompactification, ordinaryFinitePushforward, rightDerivedLowerStar,
    Functor.comp_obj, Category.assoc] using h

private theorem affine_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (d : ℕ) (K : DerivedCategoryModule A S) :
    (affineLeftScalar φ S d).app ((affineTraceRight A N hA S d).obj K) ≫
      (affineTraceLeft B S d).map
        (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom ≫
      (affineTraceAdjunction B N hB tB PB S hS d).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map ((affineTraceAdjunction A N hA tA PA S hS d).counit.app K) := by
  have hr : ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K =
      affineTraceRightExchangeTower
        (fun r ↦ affineTraceLineRight A N hA (affineTraceTower S r))
        (fun r ↦ affineTraceLineRight B N hB (affineTraceTower S r))
        (fun r ↦ scalarExtension φ (affineTraceTower S r))
        (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
          N hA hB (affineTraceInvertible _ S hS r)) d K := by
    unfold ProEtale.reductionEtaleAffineScalarIso
    exact right_exchange_rec_eq
      (fun r ↦ affineTraceLineRight A N hA (affineTraceTower S r))
      (fun r ↦ affineTraceLineRight B N hB (affineTraceTower S r))
      (fun r ↦ scalarExtension φ (affineTraceTower S r))
      (fun r ↦ ProEtale.reductionEtaleLineScalarIso φ (affineTraceTower S r)
        N hA hB (affineTraceInvertible _ S hS r)) d K
  rw [hr]
  unfold affineTraceAdjunction affineLeftScalar
  apply tower_counit_scalar
  intro r
  have : IsNoetherian (affineTraceTower S r) := affineTraceNoetherian S r
  exact line_scalar_counit φ N hN hA hB (affineTraceTower S r)
    (affineTraceInvertible _ S hS r) tA tB _ _ _

private theorem affine_left_zero
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (c : Compactification (affineTraceProjection S 0)) :
    ProEtale.reductionEtaleAffineLeftIso A S 0 c =
      (Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).symm ≪≫
      rightDerivedLowerShriekOfCompactificationIso A
        (Compactification.ofIsProper (𝟙 S)) c := rfl

private theorem affine_left_succ
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S (d + 1))) :
    ProEtale.reductionEtaleAffineLeftIso A S (d + 1) c =
      let cp := HasCompactification.compactification (affineTraceProjection S d)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationIso A
          (affineTraceLineCompactification (affineTraceTower S d)) ce.restrict) _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtale.reductionEtaleAffineLeftIso A S d cp) ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c := rfl

private theorem affine_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (scalarExtension φ S).map
        ((ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app K) ≫
      (compactScalarMap φ c).app K =
    (affineLeftScalar φ S d).app K ≫
      (ProEtale.reductionEtaleAffineLeftIso B S d c).hom.app
        ((scalarExtension φ (affineTraceTower S d)).obj K) := by
  induction d with
  | zero =>
    have hi := ordinaryChartIdentityCompactScalar φ S K
    have hr := ordinaryChartCompactificationScalar φ
      (Compactification.ofIsProper (𝟙 S)) c K
    rw [affine_left_zero, affine_left_zero]
    simp only [Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
      affineLeftScalar, affineTraceExchangeTower_zero]
    rw [hr]
    apply (cancel_epi ((scalarExtension φ S).map
      ((Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
          Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S).hom.app K))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← hi]
    simp only [Category.assoc, affineTraceTower]
    erw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  | succ d ih =>
    have : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
    have : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    have : IsNoetherian (affineTraceTower S (d + 1)) := affineTraceNoetherian S (d + 1)
    let cp := HasCompactification.compactification (affineTraceProjection S d)
    let ce := c.ofComp cp
    let cl := affineTraceLineCompactification (affineTraceTower S d)
    have hr := ordinaryChartCompactificationScalar φ (cp.comp ce) c K
    have ht := ordinaryChartCompactTowerScalar φ
      (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
      (affineTraceProjection S d) cp ce K
    have hl := ordinaryChartCompactificationScalar φ cl ce.restrict
    have hf := composite_left_scalar
      (scalarExtension φ (AffineSpace PUnit.{u + 1} (affineTraceTower S d)))
      (scalarExtension φ (affineTraceTower S d)) (scalarExtension φ S)
      (compactScalarMap φ cl) (compactScalarMap φ ce.restrict)
      (affineLeftScalar φ S d) (compactScalarMap φ cp)
      (rightDerivedLowerShriekOfCompactificationIso A cl ce.restrict)
      (rightDerivedLowerShriekOfCompactificationIso B cl ce.restrict)
      (ProEtale.reductionEtaleAffineLeftIso A S d cp)
      (ProEtale.reductionEtaleAffineLeftIso B S d cp) hl (ih cp) K
    have hp := congrArg (fun z ↦ z ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B cp ce).hom.app
        ((scalarExtension φ (affineTraceTower S (d + 1))).obj K) ≫
      (rightDerivedLowerShriekOfCompactificationIso B (cp.comp ce) c).hom.app
        ((scalarExtension φ (affineTraceTower S (d + 1))).obj K)) hf
    simp only [Category.assoc] at hp
    erw [← reassoc_of% ht] at hp
    erw [← hr] at hp
    simpa only [affine_left_succ, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      affineLeftScalar, affineTraceExchangeTower_succ, Category.assoc,
      affineTraceLeft, affineTraceLeftTower, affineTraceLineLeft,
      rightDerivedLowerShriekOfCompactification,
      affineTraceLineCompactification, Compactification.copy, affineTraceOpenLeft,
      ordinaryFinitePushforward, rightDerivedLowerStar, Functor.comp_obj,
      affineTraceTower, cp, ce, cl] using hp

private theorem chart_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (d : ℕ) {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A S) :
    (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom
        (affineLeftScalar φ S d)).app
        ((ordinaryFinitePullback A e).obj ((affineTraceRight A N hA S d).obj K)) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory ⋙
          affineTraceLeft B S d).map
        (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom ≫
      (ProEtale.reductionEtaleChartAdjunction B S N hB tB PB hS d e).counit.app
        ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((ProEtale.reductionEtaleChartAdjunction A S N hA tA PA hS d e).counit.app K) := by
  have h := compose_counit_scalar
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm)
    (affineTraceAdjunction A N hA tA PA S hS d)
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e).symm)
    (affineTraceAdjunction B N hB tB PB S hS d)
    (scalarExtension φ U) (scalarExtension φ (affineTraceTower S d)) (scalarExtension φ S)
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom (affineLeftScalar φ S d)
    K ((scalarPullbackIso φ e).inv.app ((affineTraceRight A N hA S d).obj K))
    (ProEtale.reductionEtaleAffineScalarIso φ S N hA hB hS d K).hom
    (sum_scalar_counit φ e _) (affine_scalar_counit φ N hN hA hB S hS tA tB PA PB d K)
  simpa only [scalarComposite, ProEtale.reductionEtaleChartAdjunction,
    OrdinaryChart.adjunction,
    ProEtale.reductionEtaleChartScalarIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc, ordinaryFinitePullback,
    affineTraceLeft] using h

private theorem ambient_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (MA : EtaleCompactSupportNormalization A)
    (MB : EtaleCompactSupportNormalization B)
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (e : U ⟶ V) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (f : V ⟶ S) (c : Compactification f) (d : Compactification (e ≫ f))
    (K : DerivedCategoryModule A U) :
    (scalarExtension φ S).map ((etaleAmbientLeftComparison A MA e f c d).hom.app K) ≫
      (compactScalarMap φ d).app K =
    (compactScalarMap φ c).app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K) ≫
      (etaleAmbientLeftComparison B MB e f c d).hom.app
        ((scalarExtension φ U).obj K) := by
  let ce := d.ofComp c
  have hr := ordinaryChartCompactificationScalar φ (c.comp ce) d K
  have ht := ordinaryChartCompactTowerScalar φ e f c ce K
  have hn := (compactScalarMap φ c).naturality ((MA.comparison e ce.restrict).inv.app K)
  simp only [Functor.comp_map] at hn
  have hs := ordinaryChartSumNormalization φ e ce.restrict MA MB K
  have hsi : (scalarExtension φ V).map ((MA.comparison e ce.restrict).inv.app K) ≫
      (compactScalarMap φ ce.restrict).app K =
    (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K ≫
      (MB.comparison e ce.restrict).inv.app ((scalarExtension φ U).obj K) := by
    apply (cancel_mono ((MB.comparison e ce.restrict).hom.app
      ((scalarExtension φ U).obj K))).mp
    simp only [Category.assoc, hs, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      ]
    erw [Category.comp_id]
  have hmap := congrArg (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} B) c).map hsi
  simp only [Functor.map_comp] at hmap
  simp only [etaleAmbientLeftComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  erw [hr, reassoc_of% ht, reassoc_of% hn]
  erw [reassoc_of% hmap]
  rfl

private theorem chart_left_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (MA : EtaleCompactSupportNormalization A)
    (MB : EtaleCompactSupportNormalization B)
    {U V S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) (cf : Compactification g) (i : U ⟶ V) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g = e ≫ affineTraceProjection S d)
    (K : DerivedCategoryModule A U) :
    (scalarExtension φ S).map
        ((ProEtale.reductionEtaleChartLeftIso A MA g i d e he
          cf).hom.app K) ≫
      (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ i).hom
        (compactScalarMap φ cf)).app K =
    (scalarComposite (ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom
        (affineLeftScalar φ S d)).app K ≫
      (ProEtale.reductionEtaleChartLeftIso B MB g i d e he
        cf).hom.app
          ((scalarExtension φ U).obj K) := by
  have : IsNoetherian (affineTraceTower S d) := affineTraceNoetherian S d
  let cp := HasCompactification.compactification (affineTraceProjection S d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection S d)
  have hi := ambient_left_scalar φ MA MB i g cf (cg.copy he) K
  have hj := ambient_left_scalar φ MA MB e (affineTraceProjection S d) cp cg K
  have ha := affine_left_scalar φ S d cp
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj K)
  have hn := (ProEtale.reductionEtaleAffineLeftIso B S d cp).hom.naturality
    ((ProEtale.CoefficientCompatibility.sumCoefficientIso φ e).hom.app K)
  simp only [Functor.comp_map] at hn
  dsimp only [cp, cg] at hi hj ha hn ⊢
  apply (cancel_mono ((etaleAmbientLeftComparison B MB i g cf (cg.copy he)).hom.app
    ((scalarExtension φ U).obj K))).mp
  dsimp only [scalarComposite]
  simp only [Category.assoc]
  erw [← hi]
  simp only [ProEtale.reductionEtaleChartLeftIso, OrdinaryChart.leftIso,
    Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  simp only [Category.comp_id, Functor.map_comp, Category.assoc]
  erw [hj, reassoc_of% ha, ← reassoc_of% hn]

/-- In ordinary etale coordinates, the scalar counit equation forces the ordered
chart scalar formula at a single input. Source: blueprint latest, reduction-
exceptional proof, Locality and Charts (blueprint: lem-sp-reduction-ordinary-chart).

Proof: compose the adjunction of open sum/evaluation along i with each of the
specified compact-support adjunctions. The scalar/open counit identity identifies
the restriction of q with the transpose of the scalar-extended composite counit,
postcomposed with a. Transport the two adjunctions by reductionEtaleChartLeftIso.
The chart counit scalar equation for sum followed by ordered affine integration
identifies this transpose with reductionEtaleChartScalarIso, followed by the
chart right functor applied to a. This uses the generator-normalized Tate-line
comparison: both maps send (z tensor x) tensor b to z tensor φ(x)b. The P1
normalizations fix the trace and diagonal classes, and their ordered composites
fix all dimensions. Injectivity of the B-chart adjunction Hom equivalence gives
the equality. Right-adjoint uniqueness is precisely reductionEtaleChartRightIso.
For d=0 the affine adjunction is the identity. The zero coefficient ring is
included by the same generator and adjunction identities. This statement has no
site realization, no intrinsic coefficient transpose and no input-origin choice. -/
theorem reductionExceptional_ordinary_chart
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (GA : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (GB : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (adjA : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) cf ⊣ GA)
    (adjB : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} B) cf ⊣ GB)
    (L : Etale.DerivedCategoryModule A Y)
    (hL : Etale.DerivedCategory.boundedConstructibleFiniteTor A Y L)
    (LB : Etale.DerivedCategoryModule B Y)
    (a : (Etale.scalarExtension φ Y).obj L ⟶ LB)
    (q : (Etale.scalarExtension φ X).obj (GA.obj L) ⟶ GB.obj LB)
    (hq : (Etale.compactScalarMap φ cf).app (GA.obj L) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).map q ≫
        adjB.counit.app LB = (Etale.scalarExtension φ Y).map (adjA.counit.app L) ≫ a) :
    (Etale.scalarPullbackIso φ i).inv.app (GA.obj L) ≫
        (Etale.ordinaryFinitePullback B i).map q ≫
        (reductionEtaleChartRightIso B MB f i d e he cf GB adjB N hB tB DB hY).hom.app LB =
      (Etale.scalarExtension φ U).map
        ((reductionEtaleChartRightIso A MA f i d e he cf GA adjA N hA tA DA hY).hom.app L) ≫
      (reductionEtaleChartScalarIso φ N hA hB hY d e L).hom ≫
      (Etale.affineTraceRight B N hB Y d ⋙ Etale.ordinaryFinitePullback B e).map a := by
  have _ := hL
  let aA := ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) i).symm).comp adjA
  let aB := ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) i inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} B) i).symm).comp adjB
  let hA' := reductionEtaleChartAdjunction A Y N hA tA DA hY d e
  let hB' := reductionEtaleChartAdjunction B Y N hB tB DB hY d e
  let lA := reductionEtaleChartLeftIso A MA f i d e he cf
  let lB := reductionEtaleChartLeftIso B MB f i d e he cf
  let β := scalarComposite (CoefficientCompatibility.sumCoefficientIso φ i).hom
    (Etale.compactScalarMap φ cf)
  let γ := scalarComposite (CoefficientCompatibility.sumCoefficientIso φ e).hom
    (affineLeftScalar φ Y d)
  let qi := (Etale.scalarPullbackIso φ i).inv.app (GA.obj L) ≫
    (Etale.ordinaryFinitePullback B i).map q
  let r := (reductionEtaleChartScalarIso φ N hA hB hY d e L).hom
  have hqi : β.app ((GA ⋙ Etale.ordinaryFinitePullback A i).obj L) ≫
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} B) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).map qi ≫
      aB.counit.app LB = (Etale.scalarExtension φ Y).map (aA.counit.app L) ≫ a := by
    have h := compose_counit_scalar_to
      ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) i).symm) adjA
      ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) i inferInstance).ofNatIsoRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) i).symm) adjB
      (Etale.scalarExtension φ U) (Etale.scalarExtension φ X) (Etale.scalarExtension φ Y)
      (CoefficientCompatibility.sumCoefficientIso φ i).hom
      (Etale.compactScalarMap φ cf) L LB a
      ((Etale.scalarPullbackIso φ i).inv.app (GA.obj L)) q
      (sum_scalar_counit φ i _) hq
    simpa only [β, qi, aA, aB, scalarComposite, Functor.comp_map,
      Etale.ordinaryFinitePullback, Functor.comp_obj, Category.assoc] using h
  have hb : Epi (β.app ((GA ⋙ Etale.ordinaryFinitePullback A i).obj L)) := by
    dsimp only [β, scalarComposite]
    have := Etale.compactScalarMap_isIso φ cf
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) i inferInstance).mapDerivedCategory.obj
        ((GA ⋙ Etale.ordinaryFinitePullback A i).obj L))
    infer_instance
  have hr : β.app ((Etale.affineTraceRight A N hA Y d ⋙
        Etale.ordinaryFinitePullback A e).obj L) ≫
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} B) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).map r ≫
      (hB'.ofNatIsoLeft lB).counit.app ((Etale.scalarExtension φ Y).obj L) =
        (Etale.scalarExtension φ Y).map ((hA'.ofNatIsoLeft lA).counit.app L) := by
    exact transported_counit_scalar hA' hB' lA lB
      (Etale.scalarExtension φ U) (Etale.scalarExtension φ Y) β γ L r
      (chart_left_scalar φ MA MB f cf i d e he)
      (chart_scalar_counit φ N hN hA hB Y hY tA tB DA DB d e L)
  have hr' : β.app ((Etale.affineTraceRight A N hA Y d ⋙
        Etale.ordinaryFinitePullback A e).obj L) ≫
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} B) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) cf).map
        (r ≫ (Etale.affineTraceRight B N hB Y d ⋙
          Etale.ordinaryFinitePullback B e).map a) ≫
      (hB'.ofNatIsoLeft lB).counit.app LB =
        (Etale.scalarExtension φ Y).map ((hA'.ofNatIsoLeft lA).counit.app L) ≫ a := by
    exact counit_postcompose (hB'.ofNatIsoLeft lB) _ r a _ hr
  have h := rightAdjointUniq_scalar_of_counits aA (hA'.ofNatIsoLeft lA)
    aB (hB'.ofNatIsoLeft lB) (Etale.scalarExtension φ U) (Etale.scalarExtension φ Y)
    β L LB a qi
    (r ≫ (Etale.affineTraceRight B N hB Y d ⋙ Etale.ordinaryFinitePullback B e).map a)
    hqi hb hr'
  simpa only [aA, aB, hA', hB', lA, lB, qi, r,
    reductionEtaleChartRightIso, OrdinaryChart.rightIso,
    Category.assoc] using h.symm

attribute [local irreducible] ProEtale.reductionEtaleChartAdjunction
  ProEtale.reductionEtaleChartLeftIso ProEtale.reductionEtaleChartRightIso

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale

end AlgebraicGeometry.ProEtale
