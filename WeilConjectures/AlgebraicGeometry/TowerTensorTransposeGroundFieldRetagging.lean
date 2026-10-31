/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerOperationsGroundFieldRetagging
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.TowerTensorAdjointDomains

/-! # Retagging the tower projection and its tensor transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, clause (2),
and equivariance of purity and trace, Steps 1--3
(blueprint: lem-pur-tower-tensor-transpose-ground-field-retagging).

All arrows are in the ordinary derived category of strict coefficient towers,
written in the dependency's section-preserving coordinates. The existential
witnesses only make the prescribed inverse projection and its transpose well typed;
no orientation or reduction-isomorphism condition is supplied as an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerTensorRetagging

variable (P : PurityFiniteSetting.{u})
  (b : SpTowerShriek.Base P.coefficients.l P.extension)
  (o : SpTowerShriek.Operations P.coefficients.l P.extension b)
  (q : SpTowerCalculus.Coordinates P.coefficients.l P.extension b)

/-- The component of the given right-adjoint comparison in the ordinary tower category.
The main statement uses the canonical counit-preserving rightAdjointUniq comparison.
Source: gamma clause (2), comparison of representing pairs
(blueprint: lem-pur-tower-tensor-transpose-ground-field-retagging). -/
def rightComparison {X Y : Scheme.{u}}
    {Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X}
    (ρ : Gσ ≅ G) (K : SpTowerCalculus.C P.coefficients.l P.extension b q Y) :
    (SpTowerGamma.exceptional P.coefficients.l P.extension b q Gσ).obj K ⟶
      (SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj K :=
  (SpTowerGamma.realization P.coefficients.l P.extension b q X).map (ρ.hom.app K)

/-- Identity on pullback tensor the comparison of dualizing objects. The unit is the
actual coefficient tower; hU only witnesses its membership in the recorded full domain.
Source: gamma clause (2), the arrow 1 tensor rho at the coefficient unit
(blueprint: lem-pur-tower-tensor-transpose-ground-field-retagging). -/
def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X}
    (ρ : Gσ ≅ G)
    (hU : spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
      (SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y))
    (K : SpTowerCalculus.C P.coefficients.l P.extension b q Y) :=
  (SpTowerShriek.tensor P.coefficients.l P.extension b X).map
    (Prod.mkHom
      (𝟙 ((SpTowerShriek.pull P.coefficients.l P.extension b (o.geometry f)).obj
        ((SpTowerGamma.realization P.coefficients.l P.extension b q Y).obj K)))
      (rightComparison P b q ρ
        ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y, hU⟩))

attribute [local irreducible] SpTowerCalculus.realization
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem proper_projection_natural
    {C D : Type*} [Category* C] [Category* D]
    (TX : C × C ⥤ C) (TY : D × D ⥤ D)
    (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (μ : TY ⋙ P ≅ (P.prod P) ⋙ TX)
    {N N' : C} (u : N ⟶ N') (K : D) :
    TY.map (Prod.mkHom (R.map u) (𝟙 K)) ≫
        adj.homEquiv _ _ (μ.hom.app (R.obj N', K) ≫
          TX.map (Prod.mkHom (adj.counit.app N') (𝟙 _))) =
      adj.homEquiv _ _ (μ.hom.app (R.obj N, K) ≫
          TX.map (Prod.mkHom (adj.counit.app N) (𝟙 _))) ≫
        R.map (TX.map (Prod.mkHom u (𝟙 (P.obj K)))) := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  have hμ := μ.hom.naturality (Prod.mkHom (R.map u) (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map] at hμ
  rw [← Category.assoc, hμ]
  simp only [Category.assoc]
  rw [← TX.map_comp, ← TX.map_comp]
  congr 2
  ext
  · exact adj.counit_naturality u
  · simp

private theorem open_tensor_natural
    {C D : Type*} [Category* C] [Category* D]
    (TX : C × C ⥤ C) (TY : D × D ⥤ D)
    (J : C ⥤ D) (P : D ⥤ C) (adj : J ⊣ P)
    (μ : TY ⋙ P ≅ (P.prod P) ⋙ TX)
    (χ : ∀ (N : C) (K : D), TY.obj (J.obj N, K) ≅
      J.obj (TX.obj (N, P.obj K)))
    (hχ : ∀ (N : C) (K : D),
      adj.homEquiv _ _ (χ N K).inv =
        TX.map (Prod.mkHom (adj.unit.app N) (𝟙 _)) ≫ μ.inv.app (J.obj N, K))
    {N N' : C} (u : N ⟶ N') (K : D) :
    TY.map (Prod.mkHom (J.map u) (𝟙 K)) ≫ (χ N' K).hom =
      (χ N K).hom ≫ J.map (TX.map (Prod.mkHom u (𝟙 (P.obj K)))) := by
  apply (cancel_mono (χ N' K).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (χ N K).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, hχ, hχ]
  have hμ := μ.inv.naturality (Prod.mkHom (J.map u) (𝟙 K))
  simp only [Functor.comp_map, Functor.prod_map] at hμ
  simp only [Category.assoc]
  rw [← hμ]
  simp only [← Category.assoc]
  rw [← TX.map_comp, ← TX.map_comp]
  congr 2
  ext
  · exact adj.unit_naturality u
  · simp

set_option maxHeartbeats 800000 in
-- Elaborating the concrete derived tensor functors requires a larger local budget.
private theorem projection_natural {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {M N : SpTowerShriek.D P.coefficients.l P.extension X}
    (v : M ⟶ N) (K : SpTowerShriek.D P.coefficients.l P.extension Y) :
    (SpTowerShriek.tensor P.coefficients.l P.extension b Y).map
        (Prod.mkHom ((SpTowerShriek.F P.coefficients.l P.extension b o c).map v) (𝟙 K)) ≫
      SpTowerShriek.projection P.coefficients.l P.extension b o c N K =
    SpTowerShriek.projection P.coefficients.l P.extension b o c M K ≫
      (SpTowerShriek.F P.coefficients.l P.extension b o c).map
        ((SpTowerShriek.tensor P.coefficients.l P.extension b X).map
          (Prod.mkHom v (𝟙 _))) := by
  let TX := SpTowerShriek.tensor P.coefficients.l P.extension b X
  let TZ := SpTowerShriek.tensor P.coefficients.l P.extension b c.Z
  let TY := SpTowerShriek.tensor P.coefficients.l P.extension b Y
  let J := SpTowerShriek.openD P.coefficients.l P.extension b (o.openOp c.i)
  let R := SpTowerShriek.push P.coefficients.l P.extension b (o.geometry c.g)
  let L := SpTowerShriek.pull P.coefficients.l P.extension b (o.geometry c.g)
  let π := fun W ↦ (SpTowerShriek.adjunction P.coefficients.l P.extension b
      (o.geometry c.g)).homEquiv _ _
    ((o.geometry c.g).tensorPullback.hom.app (R.obj W, K) ≫
      TZ.map (Prod.mkHom ((SpTowerShriek.adjunction P.coefficients.l P.extension b
        (o.geometry c.g)).counit.app W) (𝟙 _)))
  let e := (o.comp c.i c.g).hom.app K ≫
    (eqToIso (congrArg (fun h ↦ SpTowerShriek.pull P.coefficients.l P.extension b
      (o.geometry h)) c.comm.symm)).hom.app K
  let χ := fun W ↦ (o.openTensor c.i W (L.obj K)).hom ≫
    J.map (TX.map (Prod.mkHom (𝟙 W) e))
  have hπ := proper_projection_natural TZ TY L R
    (SpTowerShriek.adjunction P.coefficients.l P.extension b (o.geometry c.g))
    (o.geometry c.g).tensorPullback (J.map v) K
  have hχ₀ := open_tensor_natural TX TZ J
    (SpTowerShriek.pull P.coefficients.l P.extension b (o.geometry c.i))
    (o.openOp c.i).derivedAdjunction (o.geometry c.i).tensorPullback
    (o.openTensor c.i) (o.openTensor_mate c.i) v (L.obj K)
  have hχ : TZ.map (Prod.mkHom (J.map v) (𝟙 (L.obj K))) ≫ χ N =
      χ M ≫ J.map (TX.map (Prod.mkHom v (𝟙 _))) := by
    dsimp only [χ]
    rw [← Category.assoc, hχ₀]
    simp only [Category.assoc]
    rw [← J.map_comp, ← J.map_comp, ← TX.map_comp, ← TX.map_comp]
    congr 3
    ext <;> simp
  change TY.map (Prod.mkHom (R.map (J.map v)) (𝟙 K)) ≫
    (π (J.obj N) ≫ R.map (χ N)) =
      (π (J.obj M) ≫ R.map (χ M)) ≫ R.map (J.map (TX.map (Prod.mkHom v (𝟙 _))))
  rw [← Category.assoc, hπ, Category.assoc, ← R.map_comp, hχ,
    R.map_comp, Category.assoc]

private theorem rightComparison_counit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X,
      spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q c).obj M.obj))
    (Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X)
    (adjσ : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ Gσ)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ G)
    (K : SpTowerCalculus.C P.coefficients.l P.extension b q Y) :
    (SpTowerShriek.F P.coefficients.l P.extension b o c).map
        (rightComparison P b q (adjσ.rightAdjointUniq adj) K) ≫
      SpTowerGamma.counit P.coefficients.l P.extension b o q c hF G adj K =
        SpTowerGamma.counit P.coefficients.l P.extension b o q c hF Gσ adjσ K := by
  let RY := (SpTowerCalculus.realization P.coefficients.l P.extension b Y
    (q.abelian Y)).functor
  let e := SpCoordinateAdjunction.supportRealization P.coefficients.l P.extension b o q c
  let u := ((adjσ.rightAdjointUniq adj).hom.app K).hom
  change (SpTowerShriek.F P.coefficients.l P.extension b o c).map
      ((SpTowerCalculus.realization P.coefficients.l P.extension b X
        (q.abelian X)).functor.map u) ≫
      (e.inv.app (G.obj K).obj ≫ RY.map (adj.counit.app K).hom) =
    e.inv.app (Gσ.obj K).obj ≫ RY.map (adjσ.counit.app K).hom
  have hn := e.inv.naturality u
  change (SpTowerShriek.F P.coefficients.l P.extension b o c).map
      ((SpTowerCalculus.realization P.coefficients.l P.extension b X
        (q.abelian X)).functor.map u) ≫ e.inv.app (G.obj K).obj =
    e.inv.app (Gσ.obj K).obj ≫
      RY.map ((SpTowerCalculus.F P.coefficients.l P.extension b o q c).map u) at hn
  have hc := congrArg (fun t ↦ t.hom) (adjσ.rightAdjointUniq_hom_app_counit adj K)
  change (SpTowerCalculus.F P.coefficients.l P.extension b o q c).map u ≫
    (adj.counit.app K).hom = (adjσ.counit.app K).hom at hc
  have hc' := congrArg RY.map hc
  rw [Functor.map_comp] at hc'
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ RY.map (adj.counit.app K).hom) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t ↦ e.inv.app (Gσ.obj K).obj ≫ t) hc')))

private theorem inverse_projection_counit_natural
    {C D : Type*} [Category* C] [Category* D]
    (TX : C × C ⥤ C) (TY : D × D ⥤ D) (F : C ⥤ D)
    (K : D) (B : C) (U : D)
    (sx : ∀ W : C, TX.obj (B, W) ≅ TX.obj (W, B))
    (sy : ∀ W : D, TY.obj (W, K) ≅ TY.obj (K, W))
    (pf : ∀ W : C, TY.obj (F.obj W, K) ⟶ F.obj (TX.obj (W, B)))
    (r : TY.obj (K, U) ⟶ K)
    {Wσ W : C} (u : Wσ ⟶ W) (εσ : F.obj Wσ ⟶ U) (ε : F.obj W ⟶ U)
    (hε : F.map u ≫ ε = εσ)
    (hsx : TX.map (Prod.mkHom (𝟙 B) u) ≫ (sx W).hom =
      (sx Wσ).hom ≫ TX.map (Prod.mkHom u (𝟙 B)))
    (hsy : TY.map (Prod.mkHom (F.map u) (𝟙 K)) ≫ (sy (F.obj W)).hom =
      (sy (F.obj Wσ)).hom ≫ TY.map (Prod.mkHom (𝟙 K) (F.map u)))
    (hpf : TY.map (Prod.mkHom (F.map u) (𝟙 K)) ≫ pf W =
      pf Wσ ≫ F.map (TX.map (Prod.mkHom u (𝟙 B))))
    [IsIso (pf Wσ)] [IsIso (pf W)] :
    F.map (TX.map (Prod.mkHom (𝟙 B) u)) ≫
        (F.map (sx W).hom ≫ inv (pf W) ≫ (sy (F.obj W)).hom ≫
          TY.map (Prod.mkHom (𝟙 K) ε) ≫ r) =
      F.map (sx Wσ).hom ≫ inv (pf Wσ) ≫ (sy (F.obj Wσ)).hom ≫
        TY.map (Prod.mkHom (𝟙 K) εσ) ≫ r := by
  have hi : F.map (TX.map (Prod.mkHom u (𝟙 B))) ≫ inv (pf W) =
      inv (pf Wσ) ≫ TY.map (Prod.mkHom (F.map u) (𝟙 K)) := by
    apply (cancel_epi (pf Wσ)).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hpf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, hsx, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hi, reassoc_of% hsy]
  have he : Prod.mkHom (𝟙 K) (F.map u) ≫ Prod.mkHom (𝟙 K) ε =
      Prod.mkHom (𝟙 K) εσ := by
    ext
    · simp
    · exact hε
  have het := congrArg TY.map he
  simp only [Functor.map_comp] at het
  rw [reassoc_of% het]

private theorem projectionCounit_comparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (tx : SpTowerP1.TensorData P.coefficients.l P.extension b X)
    (ty : SpTowerP1.TensorData P.coefficients.l P.extension b Y)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X,
      spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q c).obj M.obj))
    (Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X)
    (adjσ : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ Gσ)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ G)
    (hU : spConstructibleTorTowers P.coefficients.l P.extension Y (q.abelian Y)
      (SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y))
    (K : SpTowerCalculus.C P.coefficients.l P.extension b q Y)
    (hpfσ : IsIso (SpTowerShriek.projection P.coefficients.l P.extension b o c
      ((SpTowerGamma.exceptional P.coefficients.l P.extension b q Gσ).obj
        ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y, hU⟩)
      ((SpTowerGamma.realization P.coefficients.l P.extension b q Y).obj K)))
    (hpf : IsIso (SpTowerShriek.projection P.coefficients.l P.extension b o c
      ((SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj
        ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y, hU⟩)
      ((SpTowerGamma.realization P.coefficients.l P.extension b q Y).obj K))) :
    (SpTowerShriek.F P.coefficients.l P.extension b o c).map
        (tensorComparison P b o q f (adjσ.rightAdjointUniq adj) hU K) ≫
      SpTowerGamma.projectionCounit P.coefficients.l P.extension b o q c tx ty
        hF G adj hU K hpf =
      SpTowerGamma.projectionCounit P.coefficients.l P.extension b o q c tx ty
        hF Gσ adjσ hU K hpfσ := by
  let U : SpTowerCalculus.C P.coefficients.l P.extension b q Y :=
    ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y, hU⟩
  let u := rightComparison P b q (adjσ.rightAdjointUniq adj) U
  let K' := (SpTowerGamma.realization P.coefficients.l P.extension b q Y).obj K
  let B := (SpTowerShriek.pull P.coefficients.l P.extension b (o.geometry f)).obj K'
  have hsx : (SpTowerShriek.tensor P.coefficients.l P.extension b X).map
      (Prod.mkHom (𝟙 B) u) ≫
      ((tx.symmetry P.coefficients.l P.extension).braiding _ _).hom =
    ((tx.symmetry P.coefficients.l P.extension).braiding _ _).hom ≫
      (SpTowerShriek.tensor P.coefficients.l P.extension b X).map
        (Prod.mkHom u (𝟙 B)) := by
    let instMonoidal := (b.calculus X).closed.monoidal
    let instSymmetric := tx.symmetry P.coefficients.l P.extension
    exact BraidedCategory.braiding_naturality (𝟙 B) u
  have hsy : (SpTowerShriek.tensor P.coefficients.l P.extension b Y).map
      (Prod.mkHom ((SpTowerShriek.F P.coefficients.l P.extension b o c).map u) (𝟙 K')) ≫
      ((ty.symmetry P.coefficients.l P.extension).braiding _ _).hom =
    ((ty.symmetry P.coefficients.l P.extension).braiding _ _).hom ≫
      (SpTowerShriek.tensor P.coefficients.l P.extension b Y).map
        (Prod.mkHom (𝟙 K') ((SpTowerShriek.F P.coefficients.l P.extension b o c).map u)) := by
    let instMonoidal := (b.calculus Y).closed.monoidal
    let instSymmetric := ty.symmetry P.coefficients.l P.extension
    exact BraidedCategory.braiding_naturality _ (𝟙 K')
  have hε := rightComparison_counit P b o q c hF Gσ G adjσ adj U
  have hε' := congrArg (fun v ↦ v ≫
    (SpTowerCalculus.realization P.coefficients.l P.extension b Y
      (q.abelian Y)).counitIso.hom.app (SpTowerGamma.unit P.coefficients.l P.extension Y)) hε
  simp only [Category.assoc] at hε'
  exact inverse_projection_counit_natural
    (SpTowerShriek.tensor P.coefficients.l P.extension b X)
    (SpTowerShriek.tensor P.coefficients.l P.extension b Y)
    (SpTowerShriek.F P.coefficients.l P.extension b o c) K' B
    (SpTowerGamma.unit P.coefficients.l P.extension Y)
    (fun W ↦ (tx.symmetry P.coefficients.l P.extension).braiding B W)
    (fun W ↦ (ty.symmetry P.coefficients.l P.extension).braiding W K')
    (fun W ↦ SpTowerShriek.projection P.coefficients.l P.extension b o c W K')
    (ty.rightUnit P.coefficients.l P.extension K').hom u _ _ hε' hsx hsy
    (projection_natural P b o c u K')

private theorem realized_mate_comparison
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    (F : C ⥤ D) (RX : C ⥤ A) (RY : D ⥤ B) (S : A ⥤ B)
    [RX.Full] [RY.Faithful]
    (lift : ∀ {M N : D}, (RY.obj M ⟶ RY.obj N) → (M ⟶ N))
    (hlift : ∀ {M N : D} (t : RY.obj M ⟶ RY.obj N), RY.map (lift t) = t)
    (e : F ⋙ RY ≅ RX ⋙ S) (Gσ G : D ⥤ C)
    (adjσ : F ⊣ Gσ) (adj : F ⊣ G)
    {Qσ Q : A} (Qσ₀ Q₀ : C) (iσ : RX.obj Qσ₀ ≅ Qσ) (i : RX.obj Q₀ ≅ Q)
    (K : D) (v : Qσ ⟶ Q) (cσ : S.obj Qσ ⟶ RY.obj K)
    (c : S.obj Q ⟶ RY.obj K) (hc : S.map v ≫ c = cσ) :
    v ≫ i.inv ≫ RX.map (adj.homEquiv Q₀ K
        (lift (e.hom.app Q₀ ≫ S.map i.hom ≫ c))) =
      (iσ.inv ≫ RX.map (adjσ.homEquiv Qσ₀ K
        (lift (e.hom.app Qσ₀ ≫ S.map iσ.hom ≫ cσ)))) ≫
          RX.map ((adjσ.rightAdjointUniq adj).hom.app K) := by
  let v₀ : Qσ₀ ⟶ Q₀ := RX.preimage (iσ.hom ≫ v ≫ i.inv)
  let a := lift (e.hom.app Q₀ ≫ S.map i.hom ≫ c)
  let aσ := lift (e.hom.app Qσ₀ ≫ S.map iσ.hom ≫ cσ)
  have hv : iσ.inv ≫ RX.map v₀ = v ≫ i.inv := by
    simp [v₀]
  have ha : F.map v₀ ≫ a = aσ := by
    apply RY.map_injective
    simp only [Functor.map_comp, a, aσ, hlift]
    have hn := e.hom.naturality v₀
    simp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Category.assoc _ (S.map i.hom), ← S.map_comp]
    simp only [v₀, Functor.map_preimage, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rw [S.map_comp, Category.assoc, hc]
  have hm : v₀ ≫ adj.homEquiv Q₀ K a =
      adjσ.homEquiv Qσ₀ K aσ ≫ (adjσ.rightAdjointUniq adj).hom.app K := by
    apply (adj.homEquiv Qσ₀ K).symm.injective
    rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ha]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.rightAdjointUniq_hom_app_counit]
    exact (adjσ.homEquiv Qσ₀ K).symm_apply_apply aσ |>.symm
  change v ≫ i.inv ≫ RX.map (adj.homEquiv Q₀ K a) =
    (iσ.inv ≫ RX.map (adjσ.homEquiv Qσ₀ K aσ)) ≫
      RX.map ((adjσ.rightAdjointUniq adj).hom.app K)
  rw [← Category.assoc, ← hv, Category.assoc, ← RX.map_comp, hm,
    RX.map_comp, Category.assoc]

set_option maxHeartbeats 800000 in
-- Elaborating the concrete derived tensor functors requires a larger local budget.
/-- The same compactification gives the same projection transformation; the actual
inverse-projection/counit composite and its actual adjoint transpose intertwine the
unique counit-preserving comparison of exceptional right adjoints. Tensor, unit and
source-membership witnesses are conclusions, not extra hypotheses on the input.
Source: gamma clause (2), and equivariance Steps 1--3
(blueprint: lem-pur-tower-tensor-transpose-ground-field-retagging).

Proof:
1. The operation-retagging lemma identifies the sites, strict coefficient systems,
   tensor constraints, ordinary adjunctions and their derived comparisons. The proper
   projection is the transpose of pullback-tensor comparison followed by counit tensor
   identity (def-exchange-projection, det-sp-tower-shriek-levels), so it is unchanged.
2. Follow that proper projection by proper image of the open-tensor comparison and
   pullback composition. These too are identified, proving equality of the entire
   compactification projection transformation, before any level evaluation.
3. Write B(W) as F of source symmetry, inverse projection, then target symmetry.
   Invert the projection naturality square at rho on the coefficient unit and apply
   symmetry naturality to obtain B(omega) F(1 tensor rho) =
   (1 tensor F(rho)) B(omega_sigma). The domain and inverse-projection witnesses are
   those of det-sp-tower-gamma clause (2); no orientation is needed to form them.
4. The comparison of representing pairs in det-sp-tower-gluing preserves counits.
   Follow the preceding equation by identity tensor counit and the right unitor.
   This gives the asserted equality of the two projectionCounit arrows.
5. Under the representing Hom bijection, both proposed composites of tensorMate map
   to that same projectionCounit arrow. Injectivity proves their equality. The full
   subcategories retain the ambient morphisms (sk-def-sp-normalized-towers), including
   quotient transitions. No normalization or orientation entered the argument. -/
theorem tensor_transpose_ground_field_retagging
    (σ : P.field.k ≃ₐ[P.field.k₀] P.field.k)
    (X Y : Over (Spec (CommRingCat.of P.field.k))) (f : X ⟶ Y) (d : ℕ)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C P.coefficients.l P.extension b q X.left,
      spConstructibleTorTowers P.coefficients.l P.extension Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F P.coefficients.l P.extension b o q c).obj M.obj))
    (Gσ G : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left ⥤
      SpTowerCalculus.C P.coefficients.l P.extension b q X.left)
    (adjσ : SpTowerGluing.support P.coefficients.l P.extension b o q
      (spGroundFieldRetagCompactification P σ c) hF ⊣ Gσ)
    (adj : SpTowerGluing.support P.coefficients.l P.extension b o q c hF ⊣ G) :
    (∀ (M : SpTowerCalculus.C P.coefficients.l P.extension b q X.left)
      (K : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left),
      SpTowerShriek.projection P.coefficients.l P.extension b o
          (spGroundFieldRetagCompactification P σ c)
          ((SpTowerGamma.realization P.coefficients.l P.extension b q X.left).obj M)
          ((SpTowerGamma.realization P.coefficients.l P.extension b q Y.left).obj K) =
        SpTowerShriek.projection P.coefficients.l P.extension b o c
          ((SpTowerGamma.realization P.coefficients.l P.extension b q X.left).obj M)
          ((SpTowerGamma.realization P.coefficients.l P.extension b q Y.left).obj K)) ∧
    ∃ tx : SpTowerP1.TensorData P.coefficients.l P.extension b X.left,
    ∃ ty : SpTowerP1.TensorData P.coefficients.l P.extension b Y.left,
    ∃ hU : spConstructibleTorTowers P.coefficients.l P.extension Y.left (q.abelian Y.left)
      (SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left),
    ∀ K : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left,
    ∃ hQσ : spConstructibleTorTowers P.coefficients.l P.extension X.left (q.abelian X.left)
      ((SpTowerCalculus.realization P.coefficients.l P.extension b X.left
        (q.abelian X.left)).inverse.obj
        ((SpTowerGamma.tensorSource P.coefficients.l P.extension b o q f.left
          ((SpTowerGamma.exceptional P.coefficients.l P.extension b q Gσ).obj
            ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left, hU⟩)).obj K)),
    ∃ hQ : spConstructibleTorTowers P.coefficients.l P.extension X.left (q.abelian X.left)
      ((SpTowerCalculus.realization P.coefficients.l P.extension b X.left
        (q.abelian X.left)).inverse.obj
        ((SpTowerGamma.tensorSource P.coefficients.l P.extension b o q f.left
          ((SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj
            ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left, hU⟩)).obj K)),
    ∃ hpfσ : IsIso (SpTowerShriek.projection P.coefficients.l P.extension b o c
      ((SpTowerGamma.exceptional P.coefficients.l P.extension b q Gσ).obj
        ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left, hU⟩)
      ((SpTowerGamma.realization P.coefficients.l P.extension b q Y.left).obj K)),
    ∃ hpf : IsIso (SpTowerShriek.projection P.coefficients.l P.extension b o c
      ((SpTowerGamma.exceptional P.coefficients.l P.extension b q G).obj
        ⟨SpTowerGamma.originalUnit P.coefficients.l P.extension b q Y.left, hU⟩)
      ((SpTowerGamma.realization P.coefficients.l P.extension b q Y.left).obj K)),
      (SpTowerShriek.F P.coefficients.l P.extension b o c).map
          (tensorComparison P b o q f.left (adjσ.rightAdjointUniq adj) hU K) ≫
        SpTowerGamma.projectionCounit P.coefficients.l P.extension b o q c tx ty
          hF G adj hU K hpf =
      SpTowerGamma.projectionCounit P.coefficients.l P.extension b o q
        (spGroundFieldRetagCompactification P σ c) tx ty hF Gσ adjσ hU K hpfσ ∧
      tensorComparison P b o q f.left (adjσ.rightAdjointUniq adj) hU K ≫
        SpTowerGamma.tensorMate P.coefficients.l P.extension b o q c tx ty
          hF G adj hU K hQ hpf =
      SpTowerGamma.tensorMate P.coefficients.l P.extension b o q
          (spGroundFieldRetagCompactification P σ c) tx ty hF Gσ adjσ hU K hQσ hpfσ ≫
        rightComparison P b q (adjσ.rightAdjointUniq adj) K := by
  refine ⟨fun _ _ ↦ rfl, ?_⟩
  obtain ⟨tx, ty, hU, hdom⟩ := tensor_adjoint_domains P b o q X Y f d c hF G adj
  obtain ⟨_, _, hUσ, hdomσ⟩ := tensor_adjoint_domains P b o q X Y f d c hF Gσ adjσ
  refine ⟨tx, ty, hU, ?_⟩
  intro K
  obtain ⟨hQ, hpf⟩ := hdom K
  obtain ⟨hQσ, hpfσ⟩ := hdomσ K
  refine ⟨hQσ, hQ, hpfσ, hpf, ?_⟩
  have hC := projectionCounit_comparison P b o q c tx ty hF Gσ G adjσ adj hU K hpfσ hpf
  refine ⟨hC, ?_⟩
  let RX := SpTowerGamma.realization P.coefficients.l P.extension b q X.left
  let RY := SpTowerGamma.realization P.coefficients.l P.extension b q Y.left
  let instRX : RX.Full := by
    dsimp [RX, SpTowerGamma.realization]
    infer_instance
  let instRY : RY.Faithful := by
    dsimp [RY, SpTowerGamma.realization]
    infer_instance
  let S := SpTowerShriek.F P.coefficients.l P.extension b o c
  let F := SpTowerGluing.support P.coefficients.l P.extension b o q c hF
  let e : F ⋙ RY ≅ RX ⋙ S := NatIso.ofComponents
    (fun M ↦ (SpCoordinateAdjunction.supportRealization
      P.coefficients.l P.extension b o q c).app M.obj)
    (by
      intro M N v
      exact (SpCoordinateAdjunction.supportRealization
        P.coefficients.l P.extension b o q c).hom.naturality v.hom)
  let lift {M N : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left}
      (t : RY.obj M ⟶ RY.obj N) : M ⟶ N :=
    ObjectProperty.homMk
      ((SpTowerCalculus.realization P.coefficients.l P.extension b Y.left
        (q.abelian Y.left)).functor.preimage t)
  have hlift {M N : SpTowerCalculus.C P.coefficients.l P.extension b q Y.left}
      (t : RY.obj M ⟶ RY.obj N) : RY.map (lift t) = t := by
    exact (SpTowerCalculus.realization P.coefficients.l P.extension b Y.left
      (q.abelian Y.left)).functor.map_preimage t
  exact realized_mate_comparison F RX RY S lift @hlift e Gσ G adjσ adj
    ⟨_, hQσ⟩ ⟨_, hQ⟩
    ((SpTowerCalculus.realization P.coefficients.l P.extension b X.left
      (q.abelian X.left)).counitIso.app _)
    ((SpTowerCalculus.realization P.coefficients.l P.extension b X.left
      (q.abelian X.left)).counitIso.app _)
    K (tensorComparison P b o q f.left (adjσ.rightAdjointUniq adj) hU K) _ _ hC

end AlgebraicGeometry.ProEtale.SpTowerTensorRetagging
