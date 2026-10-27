/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Sheaf.Paper.SmoothPurityCompositionFactors
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Normalized shifted Tate splitting of towers

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


/-- Existence of the shifted Tate splitting with its prescribed finite comparison.
This asserts neither a composite orientation equation nor concentration.
Source: composition-factors proof (1), tower paragraph, shifted Tate identification
(blueprint: lem-sp-tower-tate-split-normalized).

Proof: use the sectionwise pullback and tensor functors on strict systems. Pullback
identifies each root line over Y with the root line over X, compatibly with the
quotient transition maps. Apply these identifications to the ordered e shifted
lines. The associator then concatenates these factors with the d factors over X;
use the specified root comparisons to replace wh by wf. At degree zero use the
coefficient-unit pullback comparison and the unitors. These give an isomorphism
from the (d+e)-fold ordered line to the displayed tensor. Compute evaluation on
K-flat representatives using the normalized tensor and pullback comparisons.
Their coherence identifies this calculation with finiteLineSplit. The shifts
are 2d and 2e, so their interchange sign is (-1)^(4de)=1. The scalar-unit and root
comparisons commute with quotient transitions, so this is an ordinary tower map.
No normalization of arbitrary input towers is used, and the zero-fold and empty
scheme cases use the same unitors. -/
theorem tower_tate_split_normalized
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
 :
    ∃ s : SpTowerGamma.orderedLine l E b X wh (d + e) ≅
      (SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry (jf ≫ pf))).obj
          (SpTowerGamma.orderedLine l E b Y wg e),
          SpTowerGamma.orderedLine l E b X wf d),
      TowerSplitNormalized l E b o q jf pf jg pg jh ph d e wf wg wh Pf Pg Ph af ag ah s := by sorry

end Composite
end AlgebraicGeometry.ProEtale.SpCompositionFactors
