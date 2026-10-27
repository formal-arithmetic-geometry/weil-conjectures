/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData
public import Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData

/-! # Finite projection invertibility in normalized level coordinates

Source: blueprint operations proof (2a); finite-Tor site comparison (ii)
(blueprint: lem-sp-finite-level-projection-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified finite projection word is invertible on good bounded-below
levels with retained etale origins. This concerns a single finite coefficient
category, before any conservativity on derived towers is used.
Source: blueprint operations proof (2a); lem-weil-finite-compact-projection-formula;
lem-sf-comparison-tor-amplitude(ii)
(blueprint: lem-sp-finite-level-projection-criterion).

Proof: identify R_n with A_(E,e(n+1)) using b.ideals n, the identity on the
ring of integers. Exact canonical coefficient realization commutes with
cohomology and tensor. GoodLevel therefore gives bounded constructibility and
finite Tor amplitude to the fixed-scalar realization of each retained origin.
Reflect the second Tor interval to the bounded-below etale antecedent by
lem-sf-comparison-tor-amplitude(ii), and reflect constructibility by the fully
faithful site comparison (Stacks 099T, 09AK). Ell is invertible because ell != p.
Apply the witnessed pro-etale finite compact-support projection formula to
these two antecedents with the supplied compactification. The equality in
StrictFiniteProjectionComparisons identifies its image under canonical
realization, conjugated by the tensor, compact-support and pullback comparison
isomorphisms, with comparisonLevelProjection. Naturality of these finite maps
transports the result through the two specified origin realization isomorphisms.
All comparison factors are invertible, so cancellation proves invertibility of
the displayed finite word. This uses no lift of maps from evaluated categories,
no compatibility between witnesses at distinct levels, and no conservativity on
towers. Empty schemes and zero inputs satisfy the same cancellation argument. -/
theorem finite_level_projection_criterion (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o) (coordinates : StrictFiniteCoordinates l E b)
    (_comparison : StrictFiniteProjectionComparisons l E b o levels coordinates)
    (k : FiniteFieldDatum.{u}) (_hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (n : ℕ) (K : DerivedCategory.Plus (S l E X.left))
    (L : DerivedCategory.Plus (S l E Y.left))
    (_wK : Origin l E b X.left n K.obj) (_wL : Origin l E b Y.left n L.obj)
    (_hK : GoodLevel l E b X.left n K.obj) (_hL : GoodLevel l E b Y.left n L.obj) :
    IsIso (comparisonLevelProjection l E b o levels c n
      ((Ev l E X.left n).obj K.obj) ((Ev l E Y.left n).obj L.obj)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
