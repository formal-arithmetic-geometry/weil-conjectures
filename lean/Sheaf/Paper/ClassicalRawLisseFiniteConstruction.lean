/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.ClassicalRawLissePointFibres
public import Sheaf.Paper.LissePointNormalization
public import Sheaf.Paper.LissePullbackNormalization

/-! # Finite classical realization and its point normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Construct the finite classical realization with its normalized point comparisons.
Source: Bhatt--Scholze, 6.8.4(1),(4), 6.8.11(3), 6.8.14(2), Remark 6.8.15
(blueprint: lem-zl-classical-raw-lisse-finite-construction).

Proof: Transport the reduction equivalence of completed_system_comparison along its
residue-normalized coefficient isomorphism to the specified completed coefficient ring.
Its inverse is the actual limit of the pulled-back finite levels; transport its quotient
cokernels, limit cone, unit and counit projections. The inverse limit is locally finite
free, so its degree-zero complex satisfies the one-stratum integral stratified-perfect
criterion, including the etale-origin witnesses. Apply the actual degree-zero functor
and scalar localization on compatible-family maps to define the raw heart functor.
The rational realization formulas identify this with ordinary localization of the
lattice, on objects and every fraction. Full faithfulness follows from the completed
system comparison. Use the identity-induced coefficient equivalence and continuous
realization to obtain the PBC comparison; full faithfulness lifts a specified module
isomorphism and its inverse, giving its prescribed lift equation.
On a common pro-etale trivializing cover the normalized system is finite free.
Completed pullback to a geometric point therefore computes the inverse limit of its
finite stalks. Localize this comparison; its maps are fixed by the cone projections.
Use the normalized completed-pullback gamma inverse,
the exact-functor H0 comparisons and identity-on-sections coefficient transport to
construct the intrinsic fibre bridge. The point and pullback normalizations of a
identify its composite with the same limit-of-stalks comparison. Precomposition of
pointed etale neighbourhoods commutes with the cone projections, proving transport
for every point automorphism. All these constructions allow rank zero and empty bases. -/
theorem classical_raw_lisse_finite_construction
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (hp : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Nonempty (LisseRealization.PointNormalized D l hl E
        (a.realization E (LisseRealization.point D l hl)) (a.point E)))
    (hr : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
      Nonempty (LisseRealization.PullNormalized D l hl E f
        (a.realization E X) (a.realization E Y) (a.along E f))) :
    ∃ s : Family D l hl a b,
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W : PerAdic.Base D.k), Nonempty (PointComparison D l hl E W a b s) := by
  sorry

end WeilConjectures.ClassicalRawLisse
