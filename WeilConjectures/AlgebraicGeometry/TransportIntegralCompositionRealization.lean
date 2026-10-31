/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisonData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompositionFactors

/-! # Composition of the realized integral purity maps

Source: purity-transport, the existing integral realization argument.
(blueprint: lem-pur-integral-composition-realization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem map_twice_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) {M N : A} {a b : M ⟶ N} (h : a = b) :
    G.map (F.map a) = G.map (F.map b) := congrArg (fun t ↦ G.map (F.map t)) h

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence
attribute [local irreducible] SpTowerCalculus.realization SpIntegralAdjunction.limit
  SpCompositionFactors.towerReassociate

open SpCompositionFactors

section Composition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Y Z V W U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [QuasiCompact (jf ≫ pf)] [QuasiCompact (jg ≫ pg)] [QuasiCompact (jh ≫ ph)]
  [HasCompactification (jf ≫ pf)] [HasCompactification (jg ≫ pg)]
  [HasCompactification (jh ≫ ph)]
  (d e : ℕ)
  (wf : SpChartAdmissibility.Twists l E X)
  (wg : SpChartAdmissibility.Twists l E Y)
  (wh : SpChartAdmissibility.Twists l E X)
  (Pf : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jh ph))
  (af : SpTowerGamma.Purity l E b o q jf pf d wf Pf.closed Pf.right Pf.adj Pf.levels)
  (ag : SpTowerGamma.Purity l E b o q jg pg e wg Pg.closed Pg.right Pg.adj Pg.levels)
  (ah : SpTowerGamma.Purity l E b o q jh ph (d + e) wh
    Ph.closed Ph.right Ph.adj Ph.levels)
  (c : Ph.right ≅ Pg.right ⋙ Pf.right)

variable (RX : SpReductionTower l E X (q.abelian X))
  (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)

/-- Composition for the actual total-limit purity maps, with the canonical tower
compositor and shifted Tate splitting. Applying the reconstruction units on both
sides is exactly the equation for gammaH, and counit-preserving adjoint uniqueness
conjugates it to gammaT. Thus this asserts a whole-system equation before any
separate finite evaluation.
Source: purity-transport Steps 1--2, composition-factors, tower consequence.
(blueprint: lem-pur-integral-composition-realization).

Proof: composition-factors gives the displayed equality of whole-tower morphisms
with the specified left compositor and its counit mate. Apply the exact coordinate
inverse and total derived inverse limit to that equality. The source comparisons
and reconstruction units identify the resulting words with the realized purity
components; their common intermediate units cancel by the reconstruction triangles.
Adjoint uniqueness identifies the realized compositor with the counit-preserving
compositor for the chosen exceptional adjoints. This proves the claimed equation
for the actual family, without identifying unrelated coherent lifts. -/
theorem composition_realization (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
    [IsSeparated (jf ≫ pf)] [IsSeparated (jg ≫ pg)]
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (pres : SpTowerCalculus.Preservation l E D.k b o q)
    (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
    (alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
      TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph)
    (_ha : ∀ M, (alpha.hom.app M).hom =
      (cal.composition.composition (jf ≫ pf) (jg ≫ pg) (jh ≫ ph) hcomp
        (SpTowerGamma.factorization jf pf) (SpTowerGamma.factorization jg pg)
        (SpTowerGamma.factorization jh ph)).hom.app M)
    (_hc : ∀ K,
      (TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg).map (c.hom.app K) ≫
          (Pf.adj.comp Pg.adj).counit.app K =
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
  ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
    TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s ∧
    ∀ K : SpTowerCalculus.C l E b q Z,
      (SpIntegralAdjunction.limit l E X (q.abelian X) RX NX).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
          (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jh ph) wh (d + e)
            ah.tensorX ah.tensorY Ph.closed Ph.right Ph.adj ah.unit_mem ah.orientation
            K (ah.tensor_mem K) (ah.projection_iso K) ≫
            (SpTowerGamma.realization l E b q X).map (c.hom.app K))) =
      (SpIntegralAdjunction.limit l E X (q.abelian X) RX NX).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.map
          ((SpTowerShriek.tensor l E b X).map (Prod.mkHom (𝟙 _) s.hom) ≫
          (towerReassociate l E b o jf pf jg pg jh ph hcomp
            ((SpTowerGamma.realization l E b q Z).obj K)
            (SpTowerGamma.orderedLine l E b Y wg e)
            (SpTowerGamma.orderedLine l E b X wf d)).hom ≫
          (SpTowerShriek.tensor l E b X).map
            (Prod.mkHom
              ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).map
                (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jg pg) wg e
                  ag.tensorX ag.tensorY Pg.closed Pg.right Pg.adj ag.unit_mem ag.orientation
                  K (ag.tensor_mem K) (ag.projection_iso K))) (𝟙 _)) ≫
          SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization jf pf) wf d
            af.tensorX af.tensorY Pf.closed Pf.right Pf.adj af.unit_mem af.orientation
            (Pg.right.obj K) (af.tensor_mem (Pg.right.obj K))
            (af.projection_iso (Pg.right.obj K)))) := by
  obtain ⟨s, hs, hR, hor, hgamma⟩ := SpCompositionFactors.towers l E b o q
    jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah c D _hl hcomp z pres cal
    alpha _ha _hc
  refine ⟨s, hs, ?_⟩
  intro K
  exact map_twice_eq
    (SpTowerCalculus.realization l E b X (q.abelian X)).inverse
    (SpIntegralAdjunction.limit l E X (q.abelian X) RX NX) (hgamma K).2

end Composition
end AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence
