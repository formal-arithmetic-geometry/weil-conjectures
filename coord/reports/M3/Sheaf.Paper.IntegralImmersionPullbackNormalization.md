## What changed

Replaced the main theorem's hole with assembly from the published immersion and
integral/strict-tower comparisons. The proof constructs gamma from the natural
integral comparison, the coefficient round trip, and the strict/reflector iso.
It constructs c from the actual completion unit and proves its finite projection
and transition equations by mapping the existing compatibility equations.

The proof also establishes the three Noetherian and quasi-separated assertions,
quasi-compactness of the open immersion, the specified finite free quotient
resolutions, stalk invertibility of the coefficient prime, preservation of
constructibility, and preservation of every reduction interval. For an empty
interval it applies the immersion lemma to the two disjoint singleton intervals
[0,0] and [1,1], forcing the image support to be empty.

Exactness and linearity of the other two functors are transported through the
constructed isomorphisms. Two smaller compatibility statements isolate the
coefficient/scalar and signed-shift steps that the existing interfaces do not
expose directly. Both have source citations, complete proof plans and DAG nodes.

The existing data declarations moved verbatim to
Sheaf.Paper.IntegralImmersionPullbackNormalizationData. The original module
publicly reexports them, preserving all names, types, definitions and inherited
scalar/shift conventions. No consumer requires adaptation. The change record is
coord/changes/M3-integral-immersion-normalization-data.md.

Validation: all four modules compiled on the project server through lcompile.py.
The data module took 37.6 s, coefficient compatibility 42.0 s, shift compatibility
41.6 s, and the final assembly 10.4 s. Every module is below the 60-second limit.
The final assembly compile had no warnings. Lean lines are at most 100 characters.

## Proved and sorry left

Closed the sole original hole:
WeilConjectures.IntegralImmersionNormalization.integralImmersionPullbackNormalization
(lem-sf-integral-immersion-pullback-normalization).

Added exactly two holes, each the whole body of a public theorem in its own module:

- WeilConjectures.IntegralImmersionNormalization.immersion_coefficient_linearity
  (lem-sf-integral-immersion-coefficient-linearity), in
  Sheaf.Paper.IntegralImmersionCoefficientLinearity.
- WeilConjectures.IntegralImmersionNormalization.immersion_comparison_shifts
  (lem-sf-integral-immersion-shift-compatibility), in
  Sheaf.Paper.IntegralImmersionShiftCompatibility.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
net -1 holes closed. It is not an axiom-free proof of the full result. The main
module and data module have zero holes. All newly added private helpers are proved.
No definition obtains arbitrary data from either new theorem.

## No longer needed

No module is withdrawn. The finite-extension DVR theorem is used inside the
existing standard-quotients theorem, rather than separately in the assembly.
The finite strict-tower comparison is already used by the existing integral
comparison and is not repeated. The product and signed-Roos dependencies remain
needed by the shift compatibility lemma; they are not claimed pruned.

No public import or declaration is discarded. The former proof imports move with
or are replaced by the data and compatibility modules as appropriate. The following former private proof imports are removed from the data module:

- Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect (used only by the assembly).
- Mathlib.AlgebraicGeometry.Noetherian (used only by the assembly).
- Mathlib.AlgebraicGeometry.Morphisms.Proper (used only by the assembly).
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated (used only by the assembly).
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr.
- Sheaf.Paper.FinitePullbackStrictTowerComparison.
- Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation.
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact.
- Sheaf.Paper.ExactProductFunctorStrictLimit.
- Sheaf.CategoryTheory.NormalizedRoosShiftComparison.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor (imported by the assembly).

The underlying mathematical results remain available where needed through the
published comparison theorems or the two compatibility lemmas. They are not
claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The immersion theorem's interval clause requires a <= b, while the assigned
normalization includes empty intervals. Two disjoint singleton intervals repair
this gap without strengthening the assigned hypotheses.

The legacy completeness predicate quantifies over a universe-zero finite-field
datum, rather than the universe of the given geometric datum. A proved infinite-
primes lemma supplies an auxiliary prime different from l and its universe-zero
finite-field datum. The Roos/legacy equivalence then proves exactly the same
completeness proposition. No coefficient object, functor or public signature is
changed by this proof-only witness.

The existing immersion and integral comparisons do not directly state
constant-section linearity of the normalized ordinary presentation or joint
compatibility of the two prescribed maps with one completed shift. These are
separate genuine parts of the original argument, not copies of its conclusion.
The remainder, including construction and naturality of both isomorphisms and
transport of their properties, is written in Lean.

The newest blueprint localization proof was read. This delivery preserves the
unit route and the assigned target statements; the latest proof has a unified
exact-module argument rather than the old separate integral/rational paragraphs
mentioned by the legacy docstring.

## New nodes

lem-sf-integral-immersion-coefficient-linearity isolates constant, quotient and
scalar compatibility. It asserts no comparison isomorphism, shift compatibility,
exactness or preservation of constructibility. Checked on the identity immersion,
empty source and general coefficient reduction: it uses precisely the canonical
constant coefficient maps and their quotient projections.

lem-sf-integral-immersion-shift-compatibility assumes the already constructed
natural isomorphisms, their precise normalization, the published comparison C
and completeness. It asserts only one shared shift with two commuting squares.
It does not assert their existence or any geometric, quotient-resolution,
linearity, exactness or constructibility conclusion. The augmentation (0,x) is
unchanged by the signed Roos shift, including r=0 and negative shifts.

def-sf-integral-immersion-pullback-normalization-data owns the existing data now
publicly reexported from the original module. It asserts no existence theorem
and introduces no new choice or coefficient model.

All three nodes inherit the original chapter and unit. Blueprint searches for
integral immersion pullback and Roos shift found no duplicate blueprint node.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
