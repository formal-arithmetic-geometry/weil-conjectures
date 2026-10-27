module

public import Sheaf.Paper.FilteredCondensedRepresentingPairData

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The original projection mates restrict to the bounded constructible scalar comparisons.
Source: blueprint/latest, sec-smooth-purity/sk-thm-sp-qbar, coefficient compatibility;
lem-pur-compact-support-condensed-realization, finite and closure projections.
(blueprint: lem-pur-filtered-condensed-canonical-comparisons).

Proof: for each finite inclusion and each inclusion into the closure, take the original
proper/open projection mate. When the coefficient and scheme universes differ, first
lift the finite coefficient field to the scheme universe and transport the coefficient
categories and projection mate along the resulting ring equivalence. Apply
finiteProjection_isIso and omegaProjection_isIso there, then transport invertibility
back. Thus the original components on bounded constructible objects are invertible.
Conjugate through the
recorded inclusion compatibility isomorphisms, then lift the resulting transformation
through the fully faithful constructible inclusion. Naturality follows from that of
the projection. Lift its inverse in the same way. Faithfulness proves the inverse
identities and the displayed normalization equations. This uses the finite-valued
closure ring throughout, including for an empty source scheme. -/
theorem canonical_scalar_comparisons :
    ∃ s : ScalarComparisons l k c, s.IsCanonical l k c := by sorry

end WeilConjectures.FilteredCondensedRepresentingPair
