/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TowerGeometricPurityData

/-! # Isomorphism pullback on coefficient towers

Source: latest blueprint equivariance of purity and trace, Steps 1 and 5.
(blueprint: lem-pur-isomorphism-tower-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpGeometricPurity
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)


/-- Exact inverse image along an isomorphism preserves the uniform ctf domain and
its normalized full subcategory, and has the strict root-section comparison.
Source: equivariance Step 1 (root comparison) and Step 5 (normalization).
(blueprint: lem-pur-isomorphism-tower-pullback).

Proof:
1. The sectionwise inverse image equivalence sends a test U to the same test with
its structure map followed by g. The normalized coefficient comparison sends each
constant section to itself. On strict varying-coefficient towers this is an exact
inverse equivalence and commutes with every quotient transition.
2. At each positive quotient it preserves etale origin, constructibility, and the
same cohomological and Tor intervals. Apply the exact inverse equivalence to a flat
resolution: tensor and all coefficient quotients commute with it. The common bounds
therefore work at all levels, giving the stated uniform membership.
3. The same flat-resolution identification takes each canonical derived reduction
arrow to the reduction arrow of the inverse image. An invertible input reduction
stays invertible. Transport through the recorded section-preserving realization and
scalar coordinates gives the normalization assertion in the original tower category.
4. Pull back the strict roots-of-unity sheaf by composition of its actual sections.
The coefficient comparison and root restriction send a tensor a tensor z to the
specified restricted scalar tensor restricted root. These maps commute with powers
and quotient maps before localization and are invertible using g inverse. Transport
by the specified level identifications of w and r. This supplies Roots, including
its unit comparison. Empty schemes and the first positive coefficient level are
included; no equality of arbitrary derived maps is tested by evaluation. -/
theorem isomorphism_tower_pullback {T : AlgebraicGeometry.Scheme.{u}}
    (g : T ⟶ T) [IsIso g] :
    ∃ hp : ∀ K : SpTowerCalculus.C l E b q T,
      spConstructibleTorTowers l E T (q.abelian T)
        ((SpTowerCalculus.etalePullback l E b o q g).obj K.obj),
      (∀ K : SpTowerCalculus.C l E b q T,
        IsSpNormalizedTower l E T (q.abelian T) K.obj →
          IsSpNormalizedTower l E T (q.abelian T)
            ((SpTowerCalculus.etalePullback l E b o q g).obj K.obj)) ∧
      ∀ (w : SpChartAdmissibility.Twists l E T)
        (r : SpCoordinateAdjunction.RootLines l E T), Nonempty (Roots l E b o g w r) := by
  sorry

end AlgebraicGeometry.ProEtale.SpGeometricPurity
