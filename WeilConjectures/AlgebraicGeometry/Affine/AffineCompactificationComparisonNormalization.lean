/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedCompactificationScalarSquare

/-! # Restricting the ordered ambient compactification comparison to D+

Source: blueprint Charts, ordered compactification comparison; the bounded/unbounded
proper/open comparison equations (blueprint: lem-sp-affine-compactification-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The ambient recursive comparison restricts to the same bounded-below comparison.
Source: blueprint Charts, ordered compactification scalar square, steps 3 and 7
(blueprint: lem-sp-affine-compactification-normalization).

Proof: Induct on the coordinate number. At zero both comparisons are inverse identity
normalization followed by the pairwise comparison from the identity candidate to c.
The exact identity open functor and proper identity functor give the same normalization
under the bounded-below inclusion. At a successor expand both recursive tower maps.
The bounded/unbounded pairwise comparison equation identifies the standard line
comparison; inclusion naturality moves the preceding tower comparison through it.
Apply the induction hypothesis to the chosen preceding compactification. The
bounded/unbounded composition equation identifies the binary compositor, after the
pairwise conjugations describing the chosen compatible triangle. Finally pairwise
comparison transitivity identifies the composite compactification with c. The
coherent triangle equations make this independent of the auxiliary triangle.
Every intermediate input is bounded below since compact support preserves D+;
this assertion involves no scalar extension or coefficient Tor assumption. -/
theorem affineCompactificationComparison_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app M.obj =
      (orderedCompactificationComparison A k S d c M).hom := by
  sorry

end AlgebraicGeometry.Etale
