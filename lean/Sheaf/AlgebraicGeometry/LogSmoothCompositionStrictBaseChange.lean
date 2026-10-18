/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/

import Sheaf.AlgebraicGeometry.LogFanChartBlowup
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteStability
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Composition, strict base change, and blowups in logarithmic smoothness

Source: ILO VI 1.1--1.7, 2.1--2.2; VIII 3.3.7--3.3.11; X 1.1, 1.3, 1.8
(blueprint: lem-per-log-smooth-composition-strict-base-change).

The existing `CompEq` specifies composites including their log maps. Strict pullback
squares are ordinary scheme pullbacks with strict first projection and commuting log
maps. Their fs log structure is therefore the associated pullback from the old source.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- All the composition, strict base change, strict étale locality, and saturated
blowup assertions for the chart notion of log smoothness and log étaleness.
Source: ILO VI 1.1--1.7, 2.1--2.2; VIII 3.3.7--3.3.11; X 1.1, 1.3, 1.8
(blueprint: lem-per-log-smooth-composition-strict-base-change).

Proof (the seven steps of the DAG node):
1. The unique-lifting implication of lem-per-fs-log-infinitesimal-criterion gives
   log étale implies log smooth. Identity and strict étale maps use the same monoid
   on both sides; lem-trf-associated-log-universal-stalks identifies these charts.
2. Lift twice across a strict square-zero thickening, first through the second map,
   then through the first. Finite presentation composes by
   lem-sbc-locally-finite-presentation-composition; pulled-back thickenings remain
   first order by lem-weil-pbc-first-order-thickening-base-change, and coverings
   compose by lem-weil-pbc-etale-covering-composition. Unique lifts also compose.
3. Form the ordinary scheme product and pull back the source log structure.
   The associated-log universal property gives the log product and fs charts.
   lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-finite-presentation-base-change-composition give finite presentation;
   pqf-lem-locnoeth-lft gives local Noetherianity of the product.
4. Project a strict square-zero lifting problem to the original smooth map, lift
   étale locally, then pair with the fixed map to the new base. Product uniqueness
   gives the prescribed restriction. Apply lem-per-fs-log-infinitesimal-criterion.
5. Compose chart neighborhoods for descent. Conversely factor a local map through
   the strict pullback; its remaining factor is strict étale. Use
   lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-etale-scheme-base-change,
   lem-weil-pbc-etale-covering-composition and lem-weil-pbc-etale-covering-base-change.
6. lem-trf-coherent-log-ideal-chart-construction gives saturated blowup charts with
   unchanged group completion and identity comparison to the chart fibre product.
   Kernel and cokernel have order one, so the charts are log étale. Universal
   properties identify every representative of the saturated blowup with this one.
7. Induct on the tower length. The initial identity is log étale by Step 1; each
   arrow is log étale by Step 6, and the unique-lifting argument of Step 2 composes
   them. Length zero, principal centers and empty schemes are included. -/
theorem logSmooth_composition_strictBaseChange :
    (∀ (X Y Z : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (g : EtaleLogHom Y Z), f.IsLogSmooth → g.IsLogSmooth →
      ∃ c : EtaleLogHom X Z, f.CompEq g c ∧ c.IsLogSmooth) ∧
    (∀ (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y),
      f.IsLogEtale → f.IsLogSmooth) ∧
    (∀ (X Y Z : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (g : EtaleLogHom Y Z), f.IsLogEtale → g.IsLogSmooth →
      ∃ c : EtaleLogHom X Z, f.CompEq g c ∧ c.IsLogSmooth) ∧
    (∀ (X Y Y' : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (h : EtaleLogHom Y' Y), f.IsLogSmooth → h.IsStrict →
      ∃ (X' : FineSaturatedLogScheme.{u}) (p : EtaleLogHom X' X)
        (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y),
        p.IsStrict ∧ IsPullback p.base q.base f.base h.base ∧
          p.CompEq f c ∧ q.CompEq h c ∧ q.IsLogSmooth) ∧
    (∀ (X X' Y Y' : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (h : EtaleLogHom Y' Y) (p : EtaleLogHom X' X) (q : EtaleLogHom X' Y')
      (c : EtaleLogHom X' Y), h.IsStrict → p.IsStrict →
      IsPullback p.base q.base f.base h.base → p.CompEq f c → q.CompEq h c →
      f.IsLogSmooth → q.IsLogSmooth) ∧
    (∀ (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (ι : Type v) (U V : ι → FineSaturatedLogScheme.{u})
      (a : ∀ i : ι, EtaleLogHom (U i) X) (b : ∀ i : ι, EtaleLogHom (V i) Y)
      (r : ∀ i : ι, EtaleLogHom (U i) (V i))
      (c : ∀ i : ι, EtaleLogHom (U i) Y),
      (∀ i : ι, (a i).IsStrict ∧ Etale (a i).base) →
      (∀ i : ι, (b i).IsStrict ∧ Etale (b i).base) →
      (∀ i : ι, (a i).CompEq f (c i) ∧ (r i).CompEq (b i) (c i)) →
      (∀ x : X.scheme, ∃ (i : ι) (z : (U i).scheme), (a i).base z = x) →
      (f.IsLogSmooth ↔ ∀ i : ι, (r i).IsLogSmooth) ∧
        (f.IsLogEtale ↔ ∀ i : ι, (r i).IsLogEtale)) ∧
    (∀ (X X' : FineSaturatedLogScheme.{u}) (b : EtaleLogHom X' X)
      (I : X.logStructure.IdealFamily), IsSaturatedLogBlowup b I → b.IsLogEtale) ∧
    (∀ T : SaturatedLogBlowupTower.{u},
      ∃ p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0),
        (p 0).IsIdentity ∧
          (∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ)) ∧
          (p ⟨T.length, Nat.lt_succ_self T.length⟩).IsLogEtale) := by
  sorry

end AlgebraicGeometry
