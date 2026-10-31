/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteLevelFixedProjection
import WeilConjectures.AlgebraicGeometry.SmoothPurityFiniteLevelProjectionTransport

/-! # Finite projection invertibility in normalized level coordinates

Source: blueprint operations proof (2a); finite-Tor site comparison (ii)
(blueprint: lem-sp-finite-level-projection-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

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
      ((Ev l E X.left n).obj K.obj) ((Ev l E Y.left n).obj L.obj)) := by
  have : IsSeparated (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  apply finite_level_projection_transport_isIso l E b o levels coordinates _comparison
    f.left c n K.obj L.obj _wK _wL
  exact finite_level_fixed_realization_isIso l E b k _hlp X Y f c n
    K.obj L.obj _wK _wL _hK _hL

end AlgebraicGeometry.ProEtale.SpTowerShriek
