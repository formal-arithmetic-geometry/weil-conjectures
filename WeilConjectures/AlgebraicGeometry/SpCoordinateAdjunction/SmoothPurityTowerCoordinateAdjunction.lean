/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateFoundations
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories

/-! # Ordered coordinate adjunctions on ordinary derived towers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-tower-coordinate-adjunction).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordered coordinate-chart adjunction on the unnormalized uniform constructible
finite-Tor subcategories of ordinary derived strict varying-coefficient towers.
Source: blueprint latest, Local pairs and Levels
(blueprint: lem-sp-tower-coordinate-adjunction).

Proof. Apply chart admissibility to all intermediate objects; their common bounds
and separate finite etale-origin witnesses place them in the P1 and open domains.
For one coordinate compose the normalized projective-line Hom bijection with the
open adjunction. Its counit is the projective trace after extension by zero.
Write ell = unit times uniformizer^e and use Base.ideals at exponent e(n+1).
The root projection p_(n+1) identifies the quotient line with the finite Kummer
line, and root restriction fixes its pullback. The equation
p_(n+2)(x)^ell = p_(n+1)(x) makes these ordinary maps strict tower maps.
Tensor reassociation, normalized on local pure tensors and K-flat representatives,
and the signed total-complex shift maps identify successive factors with (d)[2d].
Induct on the ordered coordinates, starting with the literal identity in degree
zero, using the compact-support composition isomorphism at each successor.
Compose with the canonical etale sum-extension adjunction. The composite-adjunction
counit formula gives fibre summation followed by ordered integration; its Hom
bijection determines both unit and counit and supplies the triangle identities.
Finally evaluate these actual constructions. Exact evaluation preserves each
composition and the fixed P1/open/etale adjunction formulas, giving both finite
transposes, units and counits. The finite construction applies to every finite
constructible finite-Tor object. No faithfulness of derived evaluation is used. -/
theorem tower_coordinate_adjunction
    (pchar : ℕ) [Fact pchar.Prime] (k : Type u) [Field k] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (hcal : SpTowerGluing.EtaleNormalized l E b o q k z cal.etale)
    (href : SpTowerGluing.EtaleRefinementCompatible l E b o q k z h cal)
    (w : TwistFamily l E k) :
    Construction l E k b o q z h cal w := by
  obtain ⟨model⟩ := tower_coordinate_adjunction_models l E pchar k _hl b o q z h cal hcal href w
  exact ⟨model.projective,
    model.roots,
    model.shifts,
    model.products,
    model.pulled,
    model._pulled_zero,
    model._pulled_one,
    model._pulled_product,
    model.affine,
    model.affine_source,
    model.affine_target,
    model._domains,
    model.projection,
    model.iteration,
    model.step,
    model._step_normalized,
    model._iteration_successor,
    model._affine_hom,
    model._projection_successor,
    model.zeroComparison,
    model._iteration_zero,
    model._zero,
    model.chart,
    model.projection_levels,
    model.chart_levels,
    model._projection_left_normalization,
    model._chart_left_normalization,
    model._projection_right_normalization,
    model._chart_right_normalization,
    model.chart_counit⟩


end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
