/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.FiniteAdjointCompositorTransposes
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.SecSmoothPurity.ReductionDirectImage
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCompactSiteCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.TowerCompositorFiniteEvaluation
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-! # Actual tower adjoint compositors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
`sk-prop-sp-composition-comparisons.proof.md`, (1)--(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization).

The indices m,n denote positive exponents m+1,n+1. The full categories retain actual
ordinary derived-tower morphisms. The left arrow is the existing tower-calculus
composition arrow, and the right arrow is characterized by its composite counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u w
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

section Evaluation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
open WeilConjectures.SemilinearSections
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type w}
  [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
  [Category.{w} D₁] [Category.{w} D₂] [Category.{w} D₃]

private theorem evaluation_transpose
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {l : D₁ ⥤ D₂} {r : D₂ ⥤ D₁}
    (adj : L ⊣ R) (level : l ⊣ r) (A : AdjunctionEvaluation E₁ E₂ adj level)
    {P : C₁} {Q : C₂} (f : L.obj P ⟶ Q) :
    E₁.map (adj.homEquiv _ _ f) ≫ A.right.hom.app Q =
      level.homEquiv _ _ (A.left.inv.app P ≫ E₂.map f) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := A.right.hom.naturality f
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu : E₁.map (adj.unit.app P) ≫ A.right.hom.app (L.obj P) =
      level.unit.app (E₁.obj P) ≫ r.map (A.left.inv.app P) := by
    rw [← A.unit P]
    have hi := (r.mapIso (A.left.app P)).hom_inv_id
    change r.map (A.left.hom.app P) ≫ r.map (A.left.inv.app P) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu, Category.assoc]

private theorem evaluated_compositor
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
    {RF : C₂ ⥤ C₁} {RG : C₃ ⥤ C₂} {RH : C₃ ⥤ C₁}
    {f : D₁ ⥤ D₂} {g : D₂ ⥤ D₃} {h : D₁ ⥤ D₃}
    {rf : D₂ ⥤ D₁} {rg : D₃ ⥤ D₂} {rh : D₃ ⥤ D₁}
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
    (aF : F ⊣ RF) (aG : G ⊣ RG) (aH : H ⊣ RH)
    (af : f ⊣ rf) (ag : g ⊣ rg) (ah : h ⊣ rh)
    (AF : AdjunctionEvaluation E₁ E₂ aF af)
    (AG : AdjunctionEvaluation E₂ E₃ aG ag)
    (AH : AdjunctionEvaluation E₁ E₃ aH ah)
    (alpha : F ⋙ G ≅ H) (alphaₙ : f ⋙ g ≅ h)
    (theta : RH ≅ RG ⋙ RF) (thetaₙ : rh ≅ rg ⋙ rf)
    (hc : ∀ K, (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K =
      alpha.hom.app (RH.obj K) ≫ aH.counit.app K)
    (hcn : ∀ K, (f ⋙ g).map (thetaₙ.hom.app K) ≫ (af.comp ag).counit.app K =
      alphaₙ.hom.app (rh.obj K) ≫ ah.counit.app K)
    (ha : ∀ M, E₃.map (alpha.hom.app M) ≫ AH.left.hom.app M =
      AG.left.hom.app (F.obj M) ≫ g.map (AF.left.hom.app M) ≫
        alphaₙ.hom.app (E₁.obj M)) (K : C₃) :
    E₁.map (theta.hom.app K) ≫ AF.right.hom.app (RG.obj K) ≫
        rf.map (AG.right.hom.app K) =
      AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K) := by
  have ht : theta.hom.app K = (aF.comp aG).homEquiv _ _
      (alpha.hom.app (RH.obj K) ≫ aH.counit.app K) := by
    apply ((aF.comp aG).homEquiv _ _).symm.injective
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K = _
    exact hc K
  have hl : E₁.map (theta.hom.app K) ≫ AF.right.hom.app (RG.obj K) ≫
      rf.map (AG.right.hom.app K) =
      (af.comp ag).homEquiv _ _
        (g.map (AF.left.inv.app (RH.obj K)) ≫ AG.left.inv.app (F.obj (RH.obj K)) ≫
          E₃.map (alpha.hom.app (RH.obj K) ≫ aH.counit.app K)) := by
    rw [ht, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    change E₁.map (aF.homEquiv _ _ (aG.homEquiv _ _ _)) ≫ _ =
      af.homEquiv _ _ (ag.homEquiv _ _ _)
    dsimp only [Functor.id_obj, Functor.comp_obj]
    have hF := evaluation_transpose aF af AF (P := RH.obj K) (Q := RG.obj K)
      (aG.homEquiv (F.obj (RH.obj K)) K (alpha.hom.app (RH.obj K) ≫ aH.counit.app K))
    have hG := evaluation_transpose aG ag AG (P := F.obj (RH.obj K)) (Q := K)
      (alpha.hom.app (RH.obj K) ≫ aH.counit.app K)
    dsimp only [Functor.comp_obj, Functor.id_obj] at hF hG
    rw [← Category.assoc, hF]
    rw [← af.homEquiv_naturality_right, Category.assoc, hG,
      ← ag.homEquiv_naturality_left]
  have hr : AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K) =
      (af.comp ag).homEquiv _ _
        (alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) ≫
          E₃.map (aH.counit.app K)) := by
    apply ((af.comp ag).homEquiv _ _).symm.injective
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change (f ⋙ g).map (AH.right.hom.app K ≫ thetaₙ.hom.app (E₃.obj K)) ≫
      (af.comp ag).counit.app (E₃.obj K) = _
    rw [Functor.map_comp, Category.assoc, hcn]
    change (f ⋙ g).map (AH.right.hom.app K) ≫
      alphaₙ.hom.app _ ≫ ah.counit.app _ = _
    rw [alphaₙ.hom.naturality_assoc, AH.counit K]
    rfl
  rw [hl, hr]
  congr 1
  let B := AG.left.app (F.obj (RH.obj K)) ≪≫ g.mapIso (AF.left.app (RH.obj K))
  have hA : E₃.map (alpha.hom.app (RH.obj K)) ≫ AH.left.hom.app (RH.obj K) =
      B.hom ≫ alphaₙ.hom.app (E₁.obj (RH.obj K)) := by
    simpa only [B, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
      ha (RH.obj K)
  have hw' : g.map (AF.left.inv.app (RH.obj K)) ≫ AG.left.inv.app (F.obj (RH.obj K)) ≫
      E₃.map (alpha.hom.app (RH.obj K)) =
      alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
    have he : B.inv ≫ E₃.map (alpha.hom.app (RH.obj K)) =
        alphaₙ.hom.app (E₁.obj (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
      calc
        _ = B.inv ≫ (E₃.map (alpha.hom.app (RH.obj K)) ≫
            AH.left.hom.app (RH.obj K)) ≫ AH.left.inv.app (RH.obj K) := by
          simp only [Category.assoc, Iso.hom_inv_id_app]
          dsimp only [Functor.comp_obj]
          rw [Category.comp_id]
        _ = B.inv ≫ (B.hom ≫ alphaₙ.hom.app (E₁.obj (RH.obj K))) ≫
            AH.left.inv.app (RH.obj K) := by rw [hA]
        _ = _ := by
          have hi := B.inv_hom_id_assoc (alphaₙ.hom.app (E₁.obj (RH.obj K)))
          dsimp only [Functor.comp_obj] at hi ⊢
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫ AH.left.inv.app (RH.obj K)) hi
    simpa only [B, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using he
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ E₃.map (aH.counit.app K)) hw'
end Evaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProEtale.TowerAdjointCompositor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Package the given actual tower adjunction with its counit-preserving evaluations.
This adds no operations to the interfaces of det-sp-tower-gluing.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Pair {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  closed : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj M.obj)
  right : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X
  adj : SpTowerGluing.support l E b o q c closed ⊣ right
  levels : SpTowerGluing.Levels l E b o q c closed right adj

/-- The given restricted compact-support functor of a packaged adjunction.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
abbrev left {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : Pair l E b o q c) := SpTowerGluing.support l E b o q c P.closed

/-- The given finite compact-support functor, retaining its actual derived morphisms.
Source: blueprint comparisons (1),(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
abbrev finiteLeft {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : Pair l E b o q c) (n : ℕ) :=
  reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (P.levels.finite_closed n)

/-- The specified finite coefficient counit mate, with no flatness assumption.
Source: blueprint comparisons (2),(3); det-sp-reduction-exceptional
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def coefficient {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : Pair l E b o q c) {m n : ℕ} (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :=
  SpTowerGluing.coefficientMate l E b c m n h
    (P.levels.finite_closed n) (P.levels.finite_closed m)
    (P.levels.scalarX m n h) (P.levels.scalarY m n h)
    (P.levels.right n) (P.levels.right m)
    (P.levels.adjunction n) (P.levels.adjunction m) K (P.levels.direct_image_iso m n h K)

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  {cf : Compactification f} {cg : Compactification g} {ch : Compactification (f ≫ g)}

/-- The finite right compositor is the unique counit-preserving adjunction comparison.
The finite datum supplies the proper/open normalized alpha, while the right adjunctions
are precisely those specified by the tower evaluations.
Source: blueprint comparisons (1),(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def finiteTheta (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg)
    (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (n : ℕ) : Ph.levels.right n ≅ Pg.levels.right n ⋙ Pf.levels.right n :=
  (Ph.levels.adjunction n).rightAdjointUniq
    (((Pf.levels.adjunction n).comp (Pg.levels.adjunction n)).ofNatIsoLeft (A n).alpha)

/-- The assumed finite b and c composition identities, with the proper/open compositors
inserted. Scalar functors are the existing derived extensions along the quotient maps.
Source: blueprint comparisons (2),(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure FiniteIdentities (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg)
    (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch) : Prop where
  left : ∀ (m n : ℕ) (h : m ≤ n)
    (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Z).map
        ((A n).alpha.hom.app M).hom ≫
      (reductionDirectImageComparison (SpTowerCalculus.quotient l E h) ch.i ch.g).app M.obj =
    (reductionDirectImageComparison (SpTowerCalculus.quotient l E h) cg.i cg.g).app
        ((finiteLeft l E b o q Pf n).obj M).obj ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) cg.i cg.g).map
        ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h) cf.i cf.g).app
          M.obj) ≫
      ((A m).alpha.hom.app
        ((reductionCtfScalar (SpTowerCalculus.quotient l E h) X
          (Pf.levels.scalarX m n h)).obj M)).hom
  right : ∀ (m n : ℕ) (h : m ≤ n)
    (K : spFiniteConstructibleTorCategory Z (SpTowerShriek.R l E n)),
    coefficient l E b o q Ph h K ≫
        (finiteTheta l E b o q Pf Pg Ph A m).hom.app
          ((reductionCtfScalar (SpTowerCalculus.quotient l E h) Z
            (Ph.levels.scalarY m n h)).obj K) =
      (reductionCtfScalar (SpTowerCalculus.quotient l E h) X
        (Ph.levels.scalarX m n h)).map
          ((finiteTheta l E b o q Pf Pg Ph A n).hom.app K) ≫
      coefficient l E b o q Pf h ((Pg.levels.right n).obj K) ≫
      (Pf.levels.right m).map (coefficient l E b o q Pg h K)

/-- Preservation of the normalized full subcategories by both members of the given
adjunction. The unnormalized uniform categories are already its source and target.
Source: blueprint comparisons (3) (blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def PreservesNormalized {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : Pair l E b o q c) : Prop :=
  (∀ M : SpTowerCalculus.C l E b q U,
    IsSpNormalizedTower l E U (q.abelian U) M.obj →
    IsSpNormalizedTower l E V (q.abelian V) ((left l E b o q P).obj M).obj) ∧
  (∀ K : SpTowerCalculus.C l E b q V,
    IsSpNormalizedTower l E V (q.abelian V) K.obj →
    IsSpNormalizedTower l E U (q.abelian U) (P.right.obj K).obj)

/-- Actual reduction equations for both image towers, conjugated only by the specified
finite evaluation identifications; in particular the right comparison is c_h itself.
Source: blueprint comparisons (3), actual reductions
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Reductions {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : Pair l E b o q c) : Prop where
  left : ∀ (m n : ℕ) (v : m ≤ n) (M : SpTowerCalculus.C l E b q U),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E v) V).map
        ((P.levels.support_evaluation n).comparison.hom.app M.obj) ≫
      (reductionDirectImageComparison (SpTowerCalculus.quotient l E v) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E U (q.abelian U) n).obj M.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v) M.obj) =
      SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v)
        ((left l E b o q P).obj M).obj ≫
      (P.levels.support_evaluation m).comparison.hom.app M.obj
  right : ∀ (m n : ℕ) (v : m ≤ n) (K : SpTowerCalculus.C l E b q V),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E v) U).map
        ((P.levels.comparison n).hom.app K).hom ≫
      (coefficient l E b o q P v ((SpTowerGluing.level l E b q V n).obj K)).hom ≫
      ((P.levels.right m).map (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v) K.obj))).hom =
      SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v) (P.right.obj K).obj ≫
        ((P.levels.comparison m).hom.app K).hom

/-- The reduction square for an actual natural transformation of tower functors.
The functors and the map are in ordinary derived-tower categories before evaluation.
Source: blueprint comparisons (3), two explicit squares
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
def ReductionSquare {U V : Scheme.{u}}
    {F G : SpTowerCalculus.C l E b q U ⥤ SpTowerCalculus.C l E b q V}
    (a : F ⟶ G) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q U),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) V).map
        ((spDerivedCoefficientEvaluation l E V (q.abelian V) n).map (a.app K).hom) ≫
      SpTowerCalculus.reduction l E V (q.abelian V) h (q.scalar V h) (G.obj K).obj =
    SpTowerCalculus.reduction l E V (q.abelian V) h (q.scalar V h) (F.obj K).obj ≫
      (spDerivedCoefficientEvaluation l E V (q.abelian V) m).map (a.app K).hom

/-- All comparisons, counits, finite evaluations and reduction squares of the node.
Source: blueprint comparisons (1)--(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization). -/
structure Laws (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg) (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (alpha : left l E b o q Pf ⋙ left l E b o q Pg ≅ left l E b o q Ph)
    (theta : Ph.right ≅ Pg.right ⋙ Pf.right) : Prop where
  proper_open : ∀ M : SpTowerCalculus.C l E b q X,
    (alpha.hom.app M).hom =
      (cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom.app M
  counit : ∀ K : SpTowerCalculus.C l E b q Z,
    (left l E b o q Pf ⋙ left l E b o q Pg).map (theta.hom.app K) ≫
      (Pf.adj.comp Pg.adj).counit.app K = alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K
  unique : ∀ t : Ph.right ≅ Pg.right ⋙ Pf.right,
    (∀ K : SpTowerCalculus.C l E b q Z,
      (left l E b o q Pf ⋙ left l E b o q Pg).map (t.hom.app K) ≫
        (Pf.adj.comp Pg.adj).counit.app K =
      alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) → t = theta
  composite_counit : ∀ K : SpTowerCalculus.C l E b q Z,
    (left l E b o q Pg).map (Pf.adj.counit.app (Pg.right.obj K)) ≫ Pg.adj.counit.app K =
      (Pf.adj.comp Pg.adj).counit.app K
  left_evaluation : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X),
    (spDerivedCoefficientEvaluation l E Z (q.abelian Z) n).map (alpha.hom.app M).hom ≫
        (Ph.levels.support_evaluation n).comparison.hom.app M.obj =
      (Pg.levels.support_evaluation n).comparison.hom.app ((left l E b o q Pf).obj M).obj ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) cg.i cg.g).map
        ((Pf.levels.support_evaluation n).comparison.hom.app M.obj) ≫
      ((A n).alpha.hom.app ((SpTowerGluing.level l E b q X n).obj M)).hom
  right_evaluation : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Z),
    (SpTowerGluing.level l E b q X n).map (theta.hom.app K) ≫
        (Pf.levels.comparison n).hom.app (Pg.right.obj K) ≫
        (Pf.levels.right n).map ((Pg.levels.comparison n).hom.app K) =
      (Ph.levels.comparison n).hom.app K ≫
        (finiteTheta l E b o q Pf Pg Ph A n).hom.app ((SpTowerGluing.level l E b q Z n).obj K)
  normalized_f : PreservesNormalized l E b o q Pf
  normalized_g : PreservesNormalized l E b o q Pg
  normalized_gf : PreservesNormalized l E b o q Ph
  reductions_f : Reductions l E b o q Pf
  reductions_g : Reductions l E b o q Pg
  reductions_gf : Reductions l E b o q Ph
  left_square : ReductionSquare l E b q alpha.hom
  right_square : ReductionSquare l E b q theta.hom

private def adjunction_evaluation {U V : Scheme.{u}} {h : U ⟶ V}
    {c : Compactification h} (P : Pair l E b o q c) (n : ℕ) :
    WeilConjectures.SemilinearSections.AdjunctionEvaluation
      (SpTowerGluing.level l E b q U n) (SpTowerGluing.level l E b q V n)
      P.adj (P.levels.adjunction n) where
  left := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((P.levels.support_evaluation n).comparison.app M.obj)) (by
      intro M N v
      apply ObjectProperty.hom_ext
      exact (P.levels.support_evaluation n).comparison.hom.naturality v.hom)
  right := P.levels.comparison n
  unit M := by
    apply ObjectProperty.hom_ext
    exact P.levels.unit n M
  counit K := by
    apply ObjectProperty.hom_ext
    exact (P.levels.counit n K).symm

private theorem evaluation_eq {U V : Scheme.{u}} {h : U ⟶ V}
    {c : Compactification h} {n : ℕ}
    (v w : SpTowerCalculus.Evaluation l E b o q c n) : v.comparison = w.comparison := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact (v.normalization M).trans (w.normalization M).symm

private theorem preserves_normalized_of_reductions
    {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : Pair l E b o q c) (hr : Reductions l E b o q P)
    (hb : ∀ (m n : ℕ) (v : m ≤ n) (M : SpTowerCalculus.C l E b q U),
      IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E v) c.i c.g).app
        ((spDerivedCoefficientEvaluation l E U (q.abelian U) n).obj M.obj))) :
    PreservesNormalized l E b o q P := by
  constructor
  · intro M hM m n v
    have hm := hM m n v
    have hi : IsIso (SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v)
        M.obj) := by
      unfold SpTowerCalculus.reduction
      infer_instance
    have hiB := hb m n v M
    have he := hr.left m n v M
    have ht : IsIso (SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v)
        ((left l E b o q P).obj M).obj ≫
          (P.levels.support_evaluation m).comparison.hom.app M.obj) := by
      rw [← he]
      infer_instance
    have hiR := (isIso_comp_right_iff _
      ((P.levels.support_evaluation m).comparison.hom.app M.obj)).mp ht
    exact (isIso_comp_left_iff _ _).mp hiR
  · intro K hK m n v
    have hk := hK m n v
    have hi : IsIso (SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v)
        K.obj) := by
      unfold SpTowerCalculus.reduction
      infer_instance
    have hiSub : IsIso (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E V (q.abelian V) v (q.scalar V v) K.obj) :
        (reductionCtfScalar (SpTowerCalculus.quotient l E v) V
          (P.levels.scalarY m n v)).obj ((SpTowerGluing.level l E b q V n).obj K) ⟶
        (SpTowerGluing.level l E b q V m).obj K) :=
      (ObjectProperty.isIso_hom_iff _).mp hi
    have hiC := P.levels.coefficient_iso m n v ((SpTowerGluing.level l E b q V n).obj K)
    have he := hr.right m n v K
    have ht : IsIso (SpTowerCalculus.reduction l E U (q.abelian U) v (q.scalar U v)
        (P.right.obj K).obj ≫ ((P.levels.comparison m).hom.app K).hom) := by
      rw [← he]
      unfold coefficient
      infer_instance
    have hiR := (isIso_comp_right_iff _ ((P.levels.comparison m).hom.app K).hom).mp ht
    exact (isIso_comp_left_iff _ _).mp hiR

/-- The proper/open tower compositor and its unique counit-normalized right comparison,
including evaluation and all reductions on the unnormalized uniform ctf categories.
Source: blueprint comparisons proof (1)--(3)
(blueprint: lem-sp-tower-adjoint-compositor-realization).

Proof:
1. The supplied cal already contains the actual proper/open tower compositor.
Restrict it componentwise to the full uniform ctf categories. Its finite evaluation
is towerCompositorFiniteEvaluation, the geometric finite-normalization step.
2. Compose the given adjunctions and transport the direct adjunction along inverse
alpha. rightAdjointUniq supplies theta with the required counit. Injectivity of
the inverse composite Hom bijection proves uniqueness; comp_counit_app identifies
the composite counit.
3. The specified units and counits make each level comparison an
AdjunctionEvaluation. Expand the transpose of theta and evaluate successively
for f and g. The left finite-evaluation identity and the h counit equation give
the finite transpose of finiteTheta. Injectivity of the finite composite Hom
bijection proves right evaluation, without faithfulness of tower evaluation.
4. Evaluation.normalization makes all given left evaluations equal to those in
cal.finite. Thus cal.reduction.reduction_formula and Pair.levels.reduction give
the two actual reduction formulas for f, g and gf.
5. For normalized inputs, the input reductions, finite coefficient comparisons
and evaluation comparisons are invertible. The formulas in step 4 and cancellation
of the scalar-coordinate comparisons prove preservation of normalization.
6. cal.reduction.reduction_naturality applied to alpha and theta gives both
reduction squares, including equal levels and unnormalized inputs.
-/
theorem towerAdjointCompositorRealization
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l) (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (Pf : Pair l E b o q cf) (Pg : Pair l E b o q cg) (Ph : Pair l E b o q ch)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (_finiteIdentities : FiniteIdentities l E b o q Pf Pg Ph A) :
    ∃ alpha : left l E b o q Pf ⋙ left l E b o q Pg ≅ left l E b o q Ph,
    ∃ theta : Ph.right ≅ Pg.right ⋙ Pf.right,
      Laws l E b o q k z hP cal Pf Pg Ph A alpha theta := by
  have hred : ∀ {U V : Scheme.{u}}
      [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
      [QuasiCompact (U ↘ Spec (.of k))]
      [IsSeparated (V ↘ Spec (.of k))] [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))]
      {h : U ⟶ V} [h.IsOver (Spec (.of k))]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      {c : Compactification h} (P : Pair l E b o q c), Reductions l E b o q P := by
    intro U V _ _ _ _ _ _ _ _ h _ _ _ _ c P
    refine ⟨?_, P.levels.reduction⟩
    intro m n v M
    rw [evaluation_eq l E b o q (P.levels.support_evaluation n)
        (cal.finite.evaluation c n),
      evaluation_eq l E b o q (P.levels.support_evaluation m)
        (cal.finite.evaluation c m)]
    exact cal.reduction.reduction_formula h c M v
  have hrf := hred Pf
  have hrg := hred Pg
  have hrh := hred Ph
  let a := cal.composition.composition f g (f ≫ g) rfl cf cg ch
  let alpha : left l E b o q Pf ⋙ left l E b o q Pg ≅ left l E b o q Ph :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (a.app M)) (by
      intro M N v
      apply ObjectProperty.hom_ext
      exact a.hom.naturality v)
  let adj := Pf.adj.comp Pg.adj
  let theta : Ph.right ≅ Pg.right ⋙ Pf.right :=
    (Ph.adj.ofNatIsoLeft alpha.symm).rightAdjointUniq adj
  have hc : ∀ K, (left l E b o q Pf ⋙ left l E b o q Pg).map
      (theta.hom.app K) ≫ adj.counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K := by
    intro K
    exact (Ph.adj.ofNatIsoLeft alpha.symm).rightAdjointUniq_hom_app_counit adj K
  refine ⟨alpha, theta, ?_⟩
  refine {
    proper_open := fun _ ↦ rfl
    counit := hc
    unique := ?_
    composite_counit := fun K ↦ (Pf.adj.comp_counit_app Pg.adj K).symm
    left_evaluation := ?_
    right_evaluation := ?_
    normalized_f := preserves_normalized_of_reductions l E b o q Pf hrf
      (fun _ _ v M ↦ cal.reduction.reduction_comparison_isIso f cf M v)
    normalized_g := preserves_normalized_of_reductions l E b o q Pg hrg
      (fun _ _ v M ↦ cal.reduction.reduction_comparison_isIso g cg M v)
    normalized_gf := preserves_normalized_of_reductions l E b o q Ph hrh
      (fun _ _ v M ↦ cal.reduction.reduction_comparison_isIso (f ≫ g) ch M v)
    reductions_f := hrf
    reductions_g := hrg
    reductions_gf := hrh
    left_square := ?_
    right_square := ?_
  }
  · intro t ht
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (adj.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using (ht K).trans (hc K).symm
  · intro n M
    exact towerCompositorFiniteEvaluation l E b o q p _hpl k d e z hP cal
      Pf.levels.support_evaluation Pg.levels.support_evaluation Ph.levels.support_evaluation
      A n M
  · intro n K
    apply evaluated_compositor Pf.adj Pg.adj Ph.adj
      (Pf.levels.adjunction n) (Pg.levels.adjunction n) (Ph.levels.adjunction n)
      (adjunction_evaluation l E b o q Pf n)
      (adjunction_evaluation l E b o q Pg n)
      (adjunction_evaluation l E b o q Ph n)
      alpha ((A n).alpha) theta (finiteTheta l E b o q Pf Pg Ph A n) hc
    · intro L
      have ht := (Ph.levels.adjunction n).rightAdjointUniq_hom_app_counit
        (((Pf.levels.adjunction n).comp (Pg.levels.adjunction n)).ofNatIsoLeft
          (A n).alpha) L
      apply (cancel_epi ((A n).alpha.inv.app _)).1
      simpa only [finiteTheta, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Category.assoc, ← NatTrans.naturality_assoc,
        Iso.inv_hom_id_app_assoc] using ht
    · intro M
      apply ObjectProperty.hom_ext
      exact towerCompositorFiniteEvaluation l E b o q p _hpl k d e z hP cal
        Pf.levels.support_evaluation Pg.levels.support_evaluation Ph.levels.support_evaluation
        A n M
  · intro m n h K
    exact cal.reduction.reduction_naturality Z h (alpha.hom.app K).hom
  · intro m n h K
    exact cal.reduction.reduction_naturality X h (theta.hom.app K).hom

end AlgebraicGeometry.ProEtale.TowerAdjointCompositor

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
