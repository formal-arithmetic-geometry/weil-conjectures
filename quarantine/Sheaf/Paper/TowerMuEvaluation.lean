/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Sheaf.Paper.SmoothPurityCompositionFactors
public import Sheaf.Paper.TowerTensorTransposeWords
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Finite evaluation of the tower mu map

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, (1), tower paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCompositionFactors

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)


section Composite
variable {X Y Z V W U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [QuasiCompact (jf ≫ pf)] [QuasiCompact (jg ≫ pg)] [QuasiCompact (jh ≫ ph)]
  [HasCompactification (jf ≫ pf)] [HasCompactification (jg ≫ pg)]
  [HasCompactification (jh ≫ ph)]
  (d e : ℕ) (wf : SpChartAdmissibility.Twists l E X)
  (wg : SpChartAdmissibility.Twists l E Y) (wh : SpChartAdmissibility.Twists l E X)
  (Pf : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l E b o q (SpTowerGamma.factorization jh ph))
  (af : SpTowerGamma.Purity l E b o q jf pf d wf Pf.closed Pf.right Pf.adj Pf.levels)
  (ag : SpTowerGamma.Purity l E b o q jg pg e wg Pg.closed Pg.right Pg.adj Pg.levels)
  (ah : SpTowerGamma.Purity l E b o q jh ph (d + e) wh
    Ph.closed Ph.right Ph.adj Ph.levels)
  (c : Ph.right ≅ Pg.right ⋙ Pf.right)


/-- Finite evaluation of the inverse tensor mate and exceptional compositor.
The comparison starts at the dualizing complex, before any diagonal orientation.
Source: composition-factors proof (1), tower paragraph, evaluation of mu
(blueprint: lem-sp-tower-mu-evaluation).

Proof: apply tensor-transpose-evaluation for f to K=omega_g. Its tensor-domain
and invertible-projection witnesses are af.tensor_mem and af.projection_iso.
Transport the retained origin of omega_g through the g right-adjoint comparison
and the normalized coefficient-unit identification uiG. Naturality of the tensor
mate and its finite counterpart identifies the evaluated rho with finiteRho.
Finite smooth purity for f makes finiteRho invertible: the supplied finite
purity for g identifies its input omega_g with a shifted finite Tate line,
which has bounded constructible cohomology and finite Tor amplitude.
Apply composition-comparisons to the three given adjunction pairs. Uniqueness
of right adjoints and the equations _ha and _hc identify its right compositor
with c. The finite right-adjoint comparisons and uiH, uiG identify its evaluation
at the coefficient unit with the canonical finiteCompositor, including the
hcomp congruence and the derived tensor-unit identification. Evaluation takes
inverses to inverses. Substitute towerMu=c_1 followed by rho inverse to obtain
the displayed square. All identifications preserve the actual counits, hence
also their adjunction units. This argument evaluates the constructed tower map;
it does not detect arbitrary derived-map equality through evaluations. -/
theorem tower_mu_evaluation
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
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
        alpha.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K)
    (hR : IsIso (towerRho l E b o q jf pf jg pg d e wf wg Pf Pg af ag))
    (n : ℕ)
    (uiF : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jf pf)
      Pf.closed Pf.right Pf.adj Pf.levels n
        ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩).etale ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y)
    (huF : (SpTowerP1.nu l E n Y).map uiF.hom ≫
        (SpTowerP1.unitWord l E n Y (af.coefficientsY n)).comparison =
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jf pf)
        Pf.closed Pf.right Pf.adj Pf.levels n
          ⟨SpTowerGamma.originalUnit l E b q Y, af.unit_mem⟩).comparison ≫
        (SpTowerShriek.Ev l E Y n).map
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
            (SpTowerGamma.unit l E Y)))
    (uiG : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jg pg)
      Pg.closed Pg.right Pg.adj Pg.levels n
        ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩).etale ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Z)
    (huG : (SpTowerP1.nu l E n Z).map uiG.hom ≫
        (SpTowerP1.unitWord l E n Z (ag.coefficientsY n)).comparison =
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jg pg)
        Pg.closed Pg.right Pg.adj Pg.levels n
          ⟨SpTowerGamma.originalUnit l E b q Z, ag.unit_mem⟩).comparison ≫
        (SpTowerShriek.Ev l E Z n).map
          ((SpTowerCalculus.realization l E b Z (q.abelian Z)).counitIso.hom.app
            (SpTowerGamma.unit l E Z)))
    (uiH : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jh ph)
      Ph.closed Ph.right Ph.adj Ph.levels n
        ⟨SpTowerGamma.originalUnit l E b q Z, ah.unit_mem⟩).etale ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Z)
    (huH : (SpTowerP1.nu l E n Z).map uiH.hom ≫
        (SpTowerP1.unitWord l E n Z (ah.coefficientsY n)).comparison =
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization jh ph)
        Ph.closed Ph.right Ph.adj Ph.levels n
          ⟨SpTowerGamma.originalUnit l E b q Z, ah.unit_mem⟩).comparison ≫
        (SpTowerShriek.Ev l E Z n).map
          ((SpTowerCalculus.realization l E b Z (q.abelian Z)).counitIso.hom.app
            (SpTowerGamma.unit l E Z)))
 :
    ∃ hr : IsIso (finiteRho (SpTowerP1.levelRing l E n) (jf ≫ pf) (jg ≫ pg)),
      SpTowerP1.WordComparison l E n
        (SpTensorTranspose.dualizingWord l E b o q jh ph
          Ph.closed Ph.right Ph.adj Ph.levels ah.unit_mem n uiH)
        (SpTowerP1.tensorWord l E n b (af.tensors n)
          (SpTowerP1.pullWord l E n b (o.geometry (jf ≫ pf)) (af.geometry n)
            (SpTensorTranspose.dualizingWord l E b o q jg pg
              Pg.closed Pg.right Pg.adj Pg.levels ag.unit_mem n uiG))
          (SpTensorTranspose.dualizingWord l E b o q jf pf
            Pf.closed Pf.right Pf.adj Pf.levels af.unit_mem n uiF))
        (towerMu l E b o q jf pf jg pg jh ph d e wf wg Pf Pg Ph af ag c hR).hom
        ((Etale.rightDerivedUpperShriekCongr (SpTowerP1.levelRing l E n)
            hcomp.symm).hom.app (MonoidalCategory.tensorUnit _) ≫
          (finiteMu (SpTowerP1.levelRing l E n) (jf ≫ pf) (jg ≫ pg) hr).hom) := by sorry

end Composite
end AlgebraicGeometry.ProEtale.SpCompositionFactors
