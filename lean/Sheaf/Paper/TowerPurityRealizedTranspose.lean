/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.TowerPurityRealizedData
import Sheaf.Paper.TowerPurityRealizedNormalization

/-! # Realized integral tower purity transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md,
Clause (2), tensor transpose and integral realization
(blueprint: lem-pur-tower-purity-realized-transpose).

This interface records the integral transpose before any finite-level evaluation. The
concrete coefficient towers, completed operations, realization comparison and finite
purity maps are supplied by the dependency nodes listed in the DAG record.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.IntegralSystemRealization

private theorem combineProjection
    {C D : Type*} [Category C] [Category D] (T : D × D ⥤ D)
    {k U V W : D} {A B : C} (F : C ⥤ D)
    (a : A ⟶ B) (pW : F.obj B ⟶ T.obj (k, V))
    (pT : F.obj A ⟶ T.obj (k, U)) (f : U ⟶ V) (eps : V ⟶ W)
    (h : F.map a ≫ pW = pT ≫ T.map (Prod.mkHom (𝟙 k) f)) :
    F.map a ≫ pW ≫ T.map (Prod.mkHom (𝟙 k) eps) =
      pT ≫ T.map (Prod.mkHom (𝟙 k) (f ≫ eps)) := by
  rw [← Category.assoc, h, Category.assoc, ← T.map_comp]
  simp only [prod_comp, Prod.mkHom, Category.id_comp]

private theorem mapThroughIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (R : B ⥤ D) (S : A ⥤ C) (P : C ⥤ D)
    (e : F ⋙ R ≅ S ⋙ P) {M N : A} (v : M ⟶ N) :
    R.map (F.map v) = e.hom.app M ≫ P.map (S.map v) ≫ e.inv.app N := by
  have hi : e.hom.app N ≫ e.inv.app N = 𝟙 (R.obj (F.obj N)) := e.hom_inv_id_app N
  have hn : R.map (F.map v) ≫ e.hom.app N = e.hom.app M ≫ P.map (S.map v) :=
    e.hom.naturality v
  calc
    R.map (F.map v) =
        (R.map (F.map v) ≫ e.hom.app N) ≫ e.inv.app N := by
      rw [Category.assoc, hi, Category.comp_id]
    _ = (e.hom.app M ≫ P.map (S.map v)) ≫ e.inv.app N :=
      congrArg (fun z ↦ z ≫ e.inv.app N) hn
    _ = _ := Category.assoc _ _ _

private theorem mapAdjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (H : B ⥤ A) (adj : F ⊣ H)
    (P : C ⥤ D) (G : D ⥤ C) (ab : P ⊣ G) (RX : A ⥤ C) (RY : B ⥤ D)
    (b : F ⋙ RY ≅ RX ⋙ P) (c : H ⋙ RX ≅ RY ⋙ G)
    (hc : ∀ K : B, RY.map (adj.counit.app K) =
      b.hom.app (H.obj K) ≫ P.map (c.hom.app K) ≫ ab.counit.app (RY.obj K))
    {M : A} {K : B} (v : M ⟶ H.obj K) :
    RY.map (F.map v ≫ adj.counit.app K) =
      b.hom.app M ≫ P.map (RX.map v ≫ c.hom.app K) ≫ ab.counit.app (RY.obj K) := by
  have hn : RY.map (F.map v) ≫ b.hom.app (H.obj K) =
      b.hom.app M ≫ P.map (RX.map v) := b.hom.naturality v
  rw [Functor.map_comp, hc]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [hn]

private theorem conjugateCounit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (iX : C ⥤ A) (iY : D ⥤ B)
    (P : A ⥤ B) (s : F ⋙ iY ≅ iX ⋙ P)
    {Q : A} (M : C) (K : D) (c : Q ≅ iX.obj M) (v : M ⟶ G.obj K)
    (p : P.obj Q ⟶ iY.obj K)
    (h : iY.map (F.map v ≫ adj.counit.app K) =
      s.hom.app M ≫ P.map c.inv ≫ p) :
    P.map (c.hom ≫ iX.map v) ≫ s.inv.app (G.obj K) ≫ iY.map (adj.counit.app K) = p := by
  have hn : P.map (iX.map v) ≫ s.inv.app (G.obj K) =
      s.inv.app M ≫ iY.map (F.map v) := s.inv.naturality v
  have hi : s.inv.app M ≫ s.hom.app M = 𝟙 (P.obj (iX.obj M)) := s.inv_hom_id_app M
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (P.map (iX.map v)) _ _, hn]
  simp only [Category.assoc, ← iY.map_comp]
  rw [h]
  rw [← Category.assoc (s.inv.app M) (s.hom.app M), hi]
  simp only [← Category.assoc, Category.comp_id, ← P.map_comp, c.hom_inv_id,
    P.map_id, Category.id_comp]

private theorem reconstructionTriangle
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B) (L : B ⥤ A)
    (adj : R ⊣ L) {M : A} {N : B} (z : R.obj M ⟶ N) :
    R.map (adj.unit.app M ≫ L.map z) ≫ adj.counit.app N = z := by
  exact (adj.eq_unit_comp_map_iff z _).mp rfl

private def conjugateTransformation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F G : A ⥤ B) (e : B ≌ C) (t : F ⋙ e.functor ⟶ G ⋙ e.functor) : F ⟶ G :=
  Functor.whiskerLeft F e.unitIso.hom ≫
    Functor.whiskerRight t e.inverse ≫ Functor.whiskerLeft G e.unitIso.inv

namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard

variable {X Z Y : Scheme.{u}}
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
  (RX : SpReductionTower l E X (q.abelian X))
  (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
  (RY : SpReductionTower l E Y (q.abelian Y))
  (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (Gb : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (ab : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF Gb ab)
  (r : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF Gb ab lv)

private theorem realized_isIso
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K) := by
  let := r.noetherianX
  let := r.noetherianY
  exact r.purity_realization r.sourceComparison K

private theorem realized_naturality
    {K K' : sfIntegralConstructibleCategory l E Y} (v : K ⟶ K') :
    (SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).map v ≫
        realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K' =
      realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K ≫
        ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).map v).hom := by
  let := r.noetherianX
  let := r.noetherianY
  let src := SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))
  let red := SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY
  let H := SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed
  let ex := SpTowerCalculus.realization l E b X (q.abelian X)
  let L := SpIntegralAdjunction.limit l E X (q.abelian X) RX NX
  let gamma : red ⋙ SpTowerGamma.source l E b o q (j ≫ p) w d ⟶
      red ⋙ SpTowerGamma.exceptional l E b q Gb :=
    { app K := SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
        r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem
        r.purity.orientation (red.obj K) (r.purity.tensor_mem _) (r.purity.projection_iso _)
      naturality _ _ v := r.purity.naturality _ _ (red.map v) }
  let t := r.sourceComparison.hom ≫ gamma
  let z := conjugateTransformation
    (src ⋙ spCompletedReduction l E X (q.abelian X) RX)
    (red ⋙ Gb ⋙ SpTowerCalculus.inclusion l E b q X) ex t
  let a : src ⟶ H ⋙ (sfIntegralConstructible l E X).ι :=
    Functor.whiskerLeft src NX.adjunction.unit ≫ Functor.whiskerRight z L
  exact a.naturality v

private theorem tensorMate_counit
    (K : SpTowerCalculus.C l E b q Y) :
    letI := r.noetherianX
    letI := r.noetherianY
    (SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)).map
        (SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p)
          r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem K
          (r.purity.tensor_mem K) (r.purity.projection_iso K)) ≫
      SpTowerGamma.counit l E b o q (SpTowerGamma.factorization j p) hF Gb ab K =
    SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p)
      r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem K
      (r.purity.projection_iso K) := by
  let := r.noetherianX
  let := r.noetherianY
  let ex := SpTowerCalculus.realization l E b X (q.abelian X)
  let ey := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let F := SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF
  let P := SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)
  let iX := SpTowerCalculus.inclusion l E b q X ⋙ ex.functor
  let iY := SpTowerCalculus.inclusion l E b q Y ⋙ ey.functor
  let s : F ⋙ iY ≅ iX ⋙ P := NatIso.ofComponents
    (fun M ↦ (SpCoordinateAdjunction.supportRealization l E b o q
      (SpTowerGamma.factorization j p)).app M.obj)
    (fun v ↦ (SpCoordinateAdjunction.supportRealization l E b o q
      (SpTowerGamma.factorization j p)).hom.naturality v.hom)
  let Q := (SpTowerGamma.tensorSource l E b o q (j ≫ p)
    ((SpTowerGamma.exceptional l E b q Gb).obj
      ⟨SpTowerGamma.originalUnit l E b q Y, r.purity.unit_mem⟩)).obj K
  let M : SpTowerCalculus.C l E b q X := ⟨ex.inverse.obj Q, r.purity.tensor_mem K⟩
  let c : Q ≅ iX.obj M := (ex.counitIso.app Q).symm
  let p := SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p)
    r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem K
    (r.purity.projection_iso K)
  let z : F.obj M ⟶ K := ObjectProperty.homMk
    (ey.functor.preimage (s.hom.app M ≫ P.map c.inv ≫ p))
  let v := ab.homEquiv M K z
  have h : iY.map (F.map v ≫ ab.counit.app K) = s.hom.app M ≫ P.map c.inv ≫ p := by
    change ey.functor.map (((ab.homEquiv M K).symm ((ab.homEquiv M K) z)).hom) = _
    rw [Equiv.symm_apply_apply]
    exact ey.functor.map_preimage _
  exact conjugateCounit F Gb ab iX iY P s M K c v p h

private theorem realized_reduction
    (K : sfIntegralConstructibleCategory l E Y) :
    letI := r.noetherianX
    letI := r.noetherianY
    (SpTwistedPullback.reduction l E b X (q.abelian X) RX).map
        (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K) ≫
      (SpTowerCalculus.realization l E b X (q.abelian X)).functor.map
        (r.rightComparison.hom.app K).hom =
    r.sourceComparison.hom.app K ≫
      SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
        r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem r.purity.orientation
        ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY).obj K)
        (r.purity.tensor_mem _) (r.purity.projection_iso _) := by
  let := r.noetherianX
  let := r.noetherianY
  let ex := SpTowerCalculus.realization l E b X (q.abelian X)
  let t := r.sourceComparison.hom.app K ≫
    SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
      r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem r.purity.orientation
      ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY).obj K)
      (r.purity.tensor_mem _) (r.purity.projection_iso _)
  change ex.functor.map ((spCompletedReduction l E X (q.abelian X) RX).map
    (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K)) ≫
      ex.functor.map (r.rightComparison.hom.app K).hom = t
  rw [← ex.functor.map_comp, r.right_normalization K]
  erw [reconstructionTriangle]
  exact ex.fullyFaithfulFunctor.map_preimage t

private theorem realized_adjunct_reduction
    (K : sfIntegralConstructibleCategory l E Y) :
    let D : sfIntegralConstructibleCategory l E X :=
      ⟨(SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K,
        r.source_complete K⟩
    (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.map
      ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY).map
        (show (SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
            r.support_closed).obj D ⟶ K from ObjectProperty.homMk
          ((CompleteProjectionDescent.integralImage l E (SpTowerGamma.factorization j p)).map
            (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K) ≫
              (r.adjunction.counit.app K).hom))).hom =
        towerProjection l E b o q j p d w RX NX RY NY hF Gb ab lv r K := by
  let := r.noetherianX
  let := r.noetherianY
  let D : sfIntegralConstructibleCategory l E X :=
    ⟨(SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K,
      r.source_complete K⟩
  let F := SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p) r.support_closed
  let H := SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed
  let rx := SpIntegralAdjunction.reduce l E X (q.abelian X) RX r.reductionX
  let ry := SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY
  let fb := SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF
  let ex := SpTowerCalculus.realization l E b X (q.abelian X)
  let ey := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let P := SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)
  let v : D ⟶ H.obj K := ObjectProperty.homMk
    (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r K)
  let ix := SpTowerCalculus.inclusion l E b q X ⋙ ex.functor
  let iy := SpTowerCalculus.inclusion l E b q Y ⋙ ey.functor
  let ss : fb ⋙ iy ≅ ix ⋙ P := NatIso.ofComponents
    (fun M ↦ (SpCoordinateAdjunction.supportRealization l E b o q
      (SpTowerGamma.factorization j p)).app M.obj)
    (fun u ↦ (SpCoordinateAdjunction.supportRealization l E b o q
      (SpTowerGamma.factorization j p)).hom.naturality u.hom)
  let z := rx.map v ≫ r.rightComparison.hom.app K
  have hz : ix.map z = r.sourceComparison.hom.app K ≫
      SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
        r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem r.purity.orientation
        (ry.obj K) (r.purity.tensor_mem _) (r.purity.projection_iso _) := by
    change ex.functor.map
      ((SpIntegralAdjunction.reduce l E X (q.abelian X) RX r.reductionX).map v ≫
        r.rightComparison.hom.app K).hom = _
    rw [ObjectProperty.FullSubcategory.comp_hom, ex.functor.map_comp]
    exact realized_reduction l E b o q j p d w RX NX RY NY hF Gb ab lv r K
  change iy.map (ry.map (F.map v ≫ r.adjunction.counit.app K)) = _
  rw [mapAdjunct F H r.adjunction fb Gb ab rx ry r.leftComparison r.rightComparison
    r.counit_reduction v]
  rw [iy.map_comp, iy.map_comp, mapThroughIso fb iy ix P ss z, hz]
  simp only [Functor.map_comp, SpTowerGamma.gamma, Category.assoc]
  change iy.map (r.leftComparison.hom.app D) ≫ ss.hom.app (rx.obj D) ≫
    P.map (r.sourceComparison.hom.app K) ≫
    P.map ((SpTowerShriek.tensor l E b X).map
      (Prod.mkHom (𝟙 _) r.purity.orientation.hom)) ≫
    (P.map (SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p)
      r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem (ry.obj K)
      (r.purity.tensor_mem _) (r.purity.projection_iso _)) ≫
      SpTowerGamma.counit l E b o q (SpTowerGamma.factorization j p) hF Gb ab (ry.obj K)) = _
  rw [tensorMate_counit l E b o q j p d w RX NX RY NY hF Gb ab lv r]
  simp only [towerProjection, Functor.map_comp, Category.assoc]
  rfl

private theorem reduceWord_injective (K : finiteTorConstructibleIntegralCategory l E Y) :
    Function.Injective (reduceWord l E b o q j p d w RX NX RY NY hF Gb ab lv r K) := by
  intro a a' h
  unfold reduceWord at h
  have h' := (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.map_injective h
  have hh := r.fullyFaithfulY.map_injective (ObjectProperty.hom_ext _ h')
  exact congrArg (fun z ↦ z.hom) hh

variable (hH : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
    finiteTorConstructibleIntegral l E X
      ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).obj)
  (hP : ∀ M : finiteTorConstructibleIntegralCategory l E X,
    finiteTorConstructibleIntegral l E Y
      ((CompleteCompactificationLimit.image l E (SpTowerGamma.factorization j p)).obj M.obj))
  (G : finiteTorConstructibleIntegralCategory l E Y ⥤
    finiteTorConstructibleIntegralCategory l E X)
  (adj : support l E (SpTowerGamma.factorization j p) hP ⊣ G)

private theorem component_isIso (K : finiteTorConstructibleIntegralCategory l E Y) :
    IsIso (component l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) := by
  have := realized_isIso l E b o q j p d w RX NX RY NY hF Gb ab lv r
    ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)
  let delta := (WeilConjectures.RealizedTowerPurity.restrictedAdjunction l E
    (SpTowerGamma.factorization j p) r.support_closed _ r.adjunction hP hH).rightAdjointUniq adj
  have : IsIso ((delta.hom.app K).hom) :=
    Functor.map_isIso (finiteTorConstructibleIntegral l E X).ι (delta.hom.app K)
  unfold component
  exact IsIso.comp_isIso

private theorem component_naturality
    {K K' : finiteTorConstructibleIntegralCategory l E Y} (u : K ⟶ K') :
    (SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).map
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).map u) ≫
      component l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K' =
    component l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K ≫
      (G.map u).hom := by
  let delta := (WeilConjectures.RealizedTowerPurity.restrictedAdjunction l E
    (SpTowerGamma.factorization j p) r.support_closed _ r.adjunction hP hH).rightAdjointUniq adj
  have hn :
      ((SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed).map
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).map u)).hom ≫
        (delta.hom.app K').hom = (delta.hom.app K).hom ≫ (G.map u).hom :=
    congrArg (fun z ↦ z.hom) (delta.hom.naturality u)
  unfold component
  rw [← Category.assoc, realized_naturality l E b o q j p d w RX NX RY NY hF Gb ab lv r]
  simpa only [Category.assoc] using congrArg (fun z ↦
    realized l E b o q j p d w RX NX RY NY hF Gb ab lv r
      ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K) ≫ z) hn

private theorem component_reduction (K : finiteTorConstructibleIntegralCategory l E Y) :
    letI := r.noetherianX
    letI := r.noetherianY
    (SpTwistedPullback.reduction l E b X (q.abelian X) RX).map
        (component l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
      componentReduction l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K =
    r.sourceComparison.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K) ≫
      SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d
        r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem r.purity.orientation
        ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY r.reductionY).obj
          ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K))
        (r.purity.tensor_mem _) (r.purity.projection_iso _) := by
  let := r.noetherianX
  let := r.noetherianY
  let delta := (WeilConjectures.RealizedTowerPurity.restrictedAdjunction l E
    (SpTowerGamma.factorization j p) r.support_closed _ r.adjunction hP hH).rightAdjointUniq adj
  have hi : (delta.hom.app K).hom ≫ (delta.inv.app K).hom = 𝟙 _ :=
    congrArg (fun z ↦ z.hom) (delta.hom_inv_id_app K)
  let R := SpTwistedPullback.reduction l E b X (q.abelian X) RX
  unfold component componentReduction
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (delta.hom.app K).hom (delta.inv.app K).hom, hi,
    R.map_id, Category.id_comp]
  exact realized_reduction l E b o q j p d w RX NX RY NY hF Gb ab lv r _

private theorem component_adjunct (K : finiteTorConstructibleIntegralCategory l E Y) :
    (CompleteProjectionDescent.integralImage l E (SpTowerGamma.factorization j p)).map
        (component l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
      (adj.counit.app K).hom =
    (CompleteProjectionDescent.integralImage l E (SpTowerGamma.factorization j p)).map
        (realized l E b o q j p d w RX NX RY NY hF Gb ab lv r
          ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)) ≫
      (r.adjunction.counit.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).hom := by
  let ar := WeilConjectures.RealizedTowerPurity.restrictedAdjunction l E
    (SpTowerGamma.factorization j p) r.support_closed _ r.adjunction hP hH
  let delta := ar.rightAdjointUniq adj
  have hc :
      (CompleteProjectionDescent.integralImage l E (SpTowerGamma.factorization j p)).map
          (delta.hom.app K).hom ≫ (adj.counit.app K).hom = (ar.counit.app K).hom :=
    congrArg (fun z ↦ z.hom) (ar.rightAdjointUniq_hom_app_counit adj K)
  have hh := r.adjunction.map_restrictFullyFaithful_counit_app
      (L := support l E (SpTowerGamma.factorization j p) hP)
      (R := WeilConjectures.RealizedTowerPurity.restrictedRight l E
        (SpIntegralAdjunction.right l E b q RX NX RY r.reductionY Gb r.closed) hH)
      (ObjectProperty.fullyFaithfulιOfLE
        (P := finiteTorConstructibleIntegral l E X) (P' := sfIntegralConstructible l E X)
        (fun _ h ↦ h.1))
      (ObjectProperty.fullyFaithfulιOfLE
        (P := finiteTorConstructibleIntegral l E Y) (P' := sfIntegralConstructible l E Y)
        (fun _ h ↦ h.1))
      (Iso.refl _) (Iso.refl _) K
  simp only [Functor.comp_obj, Iso.refl_inv, NatTrans.id_app] at hh
  change (PurCompactSupport.finiteTorIntegralInclusion l E Y).map (ar.counit.app K) =
    𝟙 _ ≫ (SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
      r.support_closed).map (𝟙 _) ≫ r.adjunction.counit.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K) at hh
  simp only [Category.id_comp] at hh
  have hid := (SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
    r.support_closed).map_id ((SpIntegralAdjunction.right l E b q RX NX RY
      r.reductionY Gb r.closed).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K))
  have hfull := hh.trans ((congrArg (fun z ↦ z ≫ r.adjunction.counit.app
    ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)) hid).trans
      (Category.id_comp _))
  have hr : (ar.counit.app K).hom =
      (r.adjunction.counit.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E Y).obj K)).hom :=
    congrArg (fun z ↦ z.hom) hfull
  unfold component
  rw [Functor.map_comp, Category.assoc, hc, hr]

end AlgebraicGeometry.ProEtale.RealizedTowerPurity

namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

attribute [local irreducible] integralCompletedTensor integralDerivedPullback
  HasDerivedCategory.standard realized component componentReduction

set_option maxHeartbeats 800000 in
-- Unpacking the fixed nested existential statement needs more elaboration heartbeats.
/-- The normalized realized tower purity has both integral projection-counit adjuncts.
Source: latest blueprint, sec-smooth-purity, gamma proof Clause (2), with Clause (1)
(blueprint: lem-pur-tower-purity-realized-transpose).

Proof:
1. Use det-sp-integral-adjunction-bijection and the reconstruction unit to realize
   the actual gamma tower. Restrict the Hom chain along the full finite-Tor inclusions.
   Transfer to G by the unique right-adjoint isomorphism, preserving the counit.
2. Write ell = u pi^e. The quotient projection cocone identifies the ell system
   with the eN restriction of the uniformizer system. Arithmetic limit restriction
   carries both augmentations and morphisms. Completed-operation substitution is
   applied to the uniformizer system first, then conjugated by that comparison.
3. At the unit, the tensor mate is identity: proper projection becomes the proper
   counit and its triangle identity; the open factor is fixed by open-unit tensor
   normalization. Injectivity of the Hom transpose gives the unit orientation.
4. Transpose tower gamma to obtain the first projection/counit word. Naturality
   of the projection gives its second form, in the category of entire systems.
5. The fully faithful restriction with the pinned b and reconstruction counit c
   gives red(epsilon) = epsilon_bullet F(c) b. CompactificationBProjection's square
   uses that same b and the augmentation-defined completed projection.
6. Reduce the integral word using this square. Move c across projection by its
   naturality and use c red(a_H) = a_bullet q_unit. The two resulting tower maps
   agree by step 4. Full faithfulness of simultaneous reduction gives integral
   equality, without inferring it from separate finite evaluations.
7. Projection naturality for a_H gives the second integral word.
8. Counit preservation for delta transfers both words from H to G.
9. The triangle identity for reduction/limit gives the whole-system reduction
   equation below, using c red(delta inverse). FiniteLevels identifies its every
   evaluation with the diagonal-normalized finite purity map, including the unit.
10. For any positive uniformizer exponent choose eN at least that exponent.
    Derived quotient reassociation and reduction compatibility give its finite
    purity map, independently of N. The common Tor interval is unchanged.
    All comparisons include d=0, identity quotient maps, zero objects and empty schemes. -/
theorem realized_tower_purity_transpose
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (b : SpTowerShriek.Base C.l E) (o : SpTowerShriek.Operations C.l E b)
    (q : SpTowerCalculus.Coordinates C.l E b)
    (w : SpChartAdmissibility.Twists C.l E X)
    (RX : SpReductionTower C.l E X (q.abelian X))
    (NX : SpNormalizedEquivalence C.l E X (q.abelian X) RX)
    (RY : SpReductionTower C.l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence C.l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C C.l E b q X,
      spConstructibleTorTowers C.l E Y (q.abelian Y)
        ((SpTowerCalculus.F C.l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (Gb : SpTowerCalculus.C C.l E b q Y ⥤ SpTowerCalculus.C C.l E b q X)
    (ab : SpTowerGluing.support C.l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
    (lv : SpTowerGluing.Levels C.l E b o q (SpTowerGamma.factorization j p) hF Gb ab) :
    ∃ (r : SpIntegralAdjunction.Realization C.l E b o q j p d w RX NX RY NY hF Gb ab lv)
      (hP : ∀ M : finiteTorConstructibleIntegralCategory C.l E X,
        finiteTorConstructibleIntegral C.l E Y
          ((CompleteCompactificationLimit.image C.l E
            (SpTowerGamma.factorization j p)).obj M.obj))
      (hH : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
        finiteTorConstructibleIntegral C.l E X
          ((SpIntegralAdjunction.right C.l E b q RX NX RY r.reductionY Gb r.closed).obj
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)).obj)
      (m : CompleteProjectionDescent.DescentModels C.l E)
      (S : ConstructibleExceptionalCoefficients.RingSystem
        C.l C.Qbar D C.different (f := j ≫ p))
      (normal : WeilConjectures.RealizedTowerPurity.FiniteNormalization
        D C E (j ≫ p) S (SpTowerGamma.factorization j p))
      (core : CompletedUnitPullback.Core C.l E (j ≫ p))
      (muX : integralConstantCoefficientObject C.l E X ≅
        (calculus C.l E X).integralClosed.monoidal.tensorUnit)
      (muY : integralConstantCoefficientObject C.l E Y ≅
        (calculus C.l E Y).integralClosed.monoidal.tensorUnit),
    letI := r.noetherianX
    letI := r.noetherianY
    (∃ hX : (PurUnitTrace.unitComplex D C E X).IsKFlatIndependentCoefficients,
      PurUnitTrace.IsUnitNormalized D C E X hX muX) ∧
    (∃ hY : (PurUnitTrace.unitComplex D C E Y).IsKFlatIndependentCoefficients,
      PurUnitTrace.IsUnitNormalized D C E Y hY muY) ∧
    ∀ (G : finiteTorConstructibleIntegralCategory C.l E Y ⥤
        finiteTorConstructibleIntegralCategory C.l E X)
      (adj : support C.l E (SpTowerGamma.factorization j p) hP ⊣ G),
      (∀ K : finiteTorConstructibleIntegralCategory C.l E Y, IsIso (component C.l E b o q j p d w
        RX NX RY NY hF Gb ab lv r hH hP G adj K)) ∧
      (∃ (e : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
          (G.obj K).obj ≅ purAdicTarget D C E (j ≫ p) K.obj)
        (s : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
          purAdicSource D C E (j ≫ p) d K.obj ≅
            (SpTwistedPullback.source C.l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj
              ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)),
        (∃ hL : ((CochainComplex.singleFunctor (scalarReductionSource C.l E X) 0).obj
            (integralTwistLine C.l E X (d : ℤ))).IsKFlatIndependentCoefficients,
          WeilConjectures.RealizedTowerPurity.SourceNormalized D C E (j ≫ p) d hL s) ∧
        (∀ (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ),
          (scalarReductionDerivedExtension C.l E X n).map (e K).hom ≫
              purAdicTargetReduction D C E (j ≫ p) d K.obj K.property n =
            (scalarReductionDerivedExtension C.l E X n).map
              (((WeilConjectures.RealizedTowerPurity.specifiedAdjunction D C E
                (j ≫ p) S (SpTowerGamma.factorization j p) hP).rightAdjointUniq
                  adj).inv.app K).hom ≫
              WeilConjectures.RealizedTowerPurity.finiteReduction D C E (j ≫ p) S
                (SpTowerGamma.factorization j p) normal K n) ∧
        ∀ (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ),
          (scalarReductionDerivedExtension C.l E X n).map
              ((s K).hom ≫ component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K ≫
                (e K).hom) ≫
              purAdicTargetReduction D C E (j ≫ p) d K.obj K.property n =
            purAdicSourceReduction D C E (j ≫ p) d K.obj K.property n ≫
              (purAdicFiniteArrow D C E (j ≫ p) d K.obj K.property n).hom) ∧
      (∀ (K K' : finiteTorConstructibleIntegralCategory C.l E Y) (u : K ⟶ K'),
        (SpTwistedPullback.source C.l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).map
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).map u) ≫
            component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K' =
          component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K ≫ (G.map u).hom) ∧
      (∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
        (SpTwistedPullback.reduction C.l E b X (q.abelian X) RX).map
            (component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
            componentReduction C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K =
          r.sourceComparison.hom.app
              ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K) ≫
            (SpTowerGamma.gamma C.l E b o q (SpTowerGamma.factorization j p) w d
              r.purity.tensorX r.purity.tensorY hF Gb ab r.purity.unit_mem
              r.purity.orientation
              ((SpIntegralAdjunction.reduce C.l E Y (q.abelian Y) RY r.reductionY).obj
                ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K))
              (r.purity.tensor_mem _) (r.purity.projection_iso _))) ∧
      (∀ (K : finiteTorConstructibleIntegralCategory C.l E Y),
        ∃ (hvT : IsIso (CompactificationBProjection.sourceUnit C.l E m
            (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E
              X d)))
        (hhT : IsIso (CompactificationBProjection.innerUnit C.l E m
            (j ≫ p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E X d)))
        (hvW : IsIso (CompactificationBProjection.sourceUnit C.l E m
            (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l
              E Y, core.admissibleY.1⟩).obj)))
        (hhW : IsIso (CompactificationBProjection.innerUnit C.l E m
            (j ≫ p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l E Y,
              core.admissibleY.1⟩).obj)))
        (hu : IsIso (((m.integral.tensor Y).chi C.l E).app
          (K.obj, integralConstantCoefficientObject C.l E Y))),
        IsIso (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ∧
        ∀
        (hpT : IsIso (CompactificationBProjection.alpha C.l E m
            (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E
              X d)
            (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit C.l E m
              (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l
                E X d)) hvT)
            (@asIso _ _ _ _ (CompactificationBProjection.innerUnit C.l E m
              (j ≫ p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E X d)) hhT)))
        (hpW : IsIso (CompactificationBProjection.alpha C.l E m
            (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l
              E Y, core.admissibleY.1⟩).obj)
            (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit C.l E m
              (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject
                C.l E Y, core.admissibleY.1⟩).obj)) hvW)
            (@asIso _ _ _ _ (CompactificationBProjection.innerUnit C.l E m
              (j ≫ p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l E Y,
                core.admissibleY.1⟩).obj)) hhW))),
        (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
          (component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
            (adj.counit.app K).hom =
          (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
            (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ≫
          (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
            ((integralCompletedTensor C.l E X).map (Prod.mkHom (𝟙 ((integralDerivedPullback C.l E
              (j ≫ p)).obj K.obj)) ((WeilConjectures.RealizedTowerPurity.sourceUnit C.l E (j ≫ p)
                d core muX).inv ≫ component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G
                  adj ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩))) ≫
          WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
              (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject
                C.l E Y, core.admissibleY.1⟩).obj) hvW hhW hpW ≫
          (integralCompletedTensor C.l E Y).map (Prod.mkHom (𝟙 K.obj) (adj.counit.app
            ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).hom) ≫
          WeilConjectures.RealizedTowerPurity.rightUnit C.l E Y m.integral muY K.obj hu ∧
        (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
          (component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
            (adj.counit.app K).hom =
          (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
            (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ≫
          WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
              (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l
                E X d) hvT hhT hpT ≫
          (integralCompletedTensor C.l E Y).map (Prod.mkHom (𝟙 K.obj)
            ((CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
              ((WeilConjectures.RealizedTowerPurity.sourceUnit C.l E (j ≫ p) d core muX).inv ≫
                component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj
                  ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩) ≫
                    (adj.counit.app ⟨integralConstantCoefficientObject C.l E Y,
                      core.admissibleY.1⟩).hom)) ≫
          WeilConjectures.RealizedTowerPurity.rightUnit C.l E Y m.integral muY K.obj hu) := by
  obtain ⟨r, hP, hH, m, S, normal, core, muX, muY, hX, hY, hnormal⟩ :=
    realized_tower_purity_normalization D C E j p d b o q w RX NX RY NY hF Gb ab lv
  let := r.noetherianX
  let := r.noetherianY
  refine ⟨r, hP, hH, m, S, normal, core, muX, muY, hX, hY, ?_⟩
  intro G adj
  obtain ⟨hfinite, hprojection⟩ := hnormal G adj
  refine ⟨?_, hfinite, ?_, ?_, ?_⟩
  · exact component_isIso C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj
  · intro K K' u
    exact component_naturality C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj u
  · exact component_reduction C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj
  · intro K
    obtain ⟨hvT, hhT, hvW, hhW, hu, hsigma, hsquares⟩ := hprojection K
    refine ⟨hvT, hhT, hvW, hhW, hu, hsigma, ?_⟩
    intro hpT hpW
    obtain ⟨hsquare, hnat⟩ := hsquares hpT hpW
    have hleft : reduceWord C.l E b o q j p d w RX NX RY NY hF Gb ab lv r K
        ((CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
          (component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K) ≫
            (adj.counit.app K).hom) =
        towerProjection C.l E b o q j p d w RX NX RY NY hF Gb ab lv r
          ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K) := by
      rw [component_adjunct C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj]
      exact realized_adjunct_reduction C.l E b o q j p d w RX NX RY NY hF Gb ab lv r _
    have hfirst := reduceWord_injective C.l E b o q j p d w RX NX RY NY hF Gb ab lv r K
      (hleft.trans hsquare.symm)
    refine ⟨hfirst, hfirst.trans ?_⟩
    let a := (WeilConjectures.RealizedTowerPurity.sourceUnit C.l E (j ≫ p)
      d core muX).inv ≫ component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj
        ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩
    let eps := (adj.counit.app
      ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).hom
    let P := CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)
    let T := integralCompletedTensor C.l E Y
    let piT := WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
      (SpTowerGamma.factorization j p) K.obj
      (WeilConjectures.RealizedTowerPurity.line C.l E X d) hvT hhT hpT
    let piW := WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
      (SpTowerGamma.factorization j p) K.obj
      ((G.obj ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).obj) hvW hhW hpW
    have hc := combineProjection T P
      ((integralCompletedTensor C.l E X).map
        (Prod.mkHom (𝟙 ((integralDerivedPullback C.l E (j ≫ p)).obj K.obj)) a))
      piW piT (P.map a) eps (hnat a)
    have hc' := congrArg (fun z ↦ P.map
      (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
        ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ≫ z ≫
          WeilConjectures.RealizedTowerPurity.rightUnit C.l E Y m.integral muY K.obj hu) hc
    simpa only [Category.assoc] using hc'


end AlgebraicGeometry.ProEtale.RealizedTowerPurity
