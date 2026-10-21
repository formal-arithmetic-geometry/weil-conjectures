## What changed

Repair the return of `9df0da84a6b`: refresh the change record's consumer audit
against current `sheaf-dag`, adding `Sheaf.Paper.LocalizedFlagProduct`,
`Sheaf.Paper.LocalizedTopChern`, and `Sheaf.Paper.VectorBundleThomClass` to
`## Users`. Inspect their textual matches and record why their statements retain
their meaning without adaptations. The retained Lean proofs and node changes
are unchanged from the reviewed packet. The delivery tool rebases the packet
onto the fetched `sheaf-dag` and reruns compilation and preflight before pushing.
The repair-session `lcompile.py --all` passed for all six modules; individual
compile times were 21.1--34.9 seconds, within the 60-second file limit. The
original theorem signature also matches the current library source verbatim.

Prove `WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation`
without changing its statement. Relocate its canonical public helper definitions
to `Sheaf.Paper.PurityRankOneLocalData`, publicly reexported by the item, to let
its proof modules depend on the definitions without an import cycle. Add the
standard additive and finite-limit-preserving instances for curried evaluation. The explicit
short-complex presentation and named adjacent-degree proof preserve the same
objects, maps and boundary sign; see `coord/changes/rank-one-local-data.md`.

The ordinary finite-coefficient calculation, coordinate monomial formula, and
classical support/comparison argument have separate modules. The main proof
uses the snake sequence to obtain the degree-two boundary isomorphisms and all
other support vanishings. It transports ordinary cohomology to the pro-etale
site through the canonical comparison. It constructs the support comparison
from these boundaries, proves the square, and proves normalized linear
uniqueness. Polynomial valuations and the decomposition of punctured-line units
use proved Mathlib and adopted source-library lemmas.

## Proved and sorry left

The item originally had one hole,
`WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation`.
Closed 1 of 1 original holes: `rankOne_local_calculation`. Added 0 holes and
left 0 holes in every delivered module; the four new theorem modules are proved,
not retained decompositions. All six modules have compiled individually through the server; the delivery
command verifies the final packet including the unused-hypothesis warning cleanup. `#print axioms` for the main
theorem includes `sorryAx` inherited from existing imported dependencies, so this
is a stage-3 proof from library declarations, not a claim that the full target
import closure is axiom-clean. The helper axiom checks show `finite_kummer_cohomology` and `kummer_monomial`
use only `propext`, `Classical.choice`, and `Quot.sound`.
`classical_support_comparison` inherits `sorryAx` from its existing library
comparison dependencies. No axiom is declared in the packet.

The new public theorems are `finite_kummer_generator`,
`finite_kummer_cohomology`, `kummer_monomial`, and
`classical_support_comparison`, all in namespace
`WeilConjectures.PurityFiniteSetting.RankOne`. Each has its node listed below.

## No longer needed

Remove the item's original private imports of
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`,
`Sheaf.Paper.RingedTopoiDerivedTensorPullback`,
`Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra`,
`Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`,
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
`WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`,
`WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`,
`WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`,
`WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder`,
`WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`,
`Sheaf.AlgebraicGeometry.KummerAffineLine`,
`Sheaf.AlgebraicGeometry.SupportComparisonBoundary`, and
`Sheaf.AlgebraicGeometry.SupportSiteComparison`.
The Kummer sequence import moves with its definitions. Source modules imported
by the new proofs can already include some of these dependencies transitively;
this report asserts that the item needs no direct use, not their global deletion.
The ordinary calculation uses arbitrary finite abelian coefficients rather than
the planned finite-free coefficient statement. The comparison uses evaluation
of the derived unit and the actual section-complex snake sequence, and does not
need separate support pullback/coherence lemmas. The unit decomposition uses
the already proved source theorem directly.

Removed proof dependencies from the original node:

- `def-sc-mu-trivialization`
- `def-weil-size-convention`
- `lem-asd-etale-finite-twist-pullback`
- `lem-pur-support-comparison-boundary`
- `lem-pur-support-site-comparison`
- `lem-sc-kummer-exact`
- `lem-sc-primitive-root`
- `lem-weil-pbc-comparison-global-cohomology`
- `lem-weil-pbc-constant-sheaf-sections-connected`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-site-sheaves-enough-injectives`
- `thm-pur-kummer-affine-line`
- `thm-pur-with-support-exactness`

Removed obsolete tool approvals (no replacement or reordering):

- `lem-weil-pbc-constant-sheaf-sections-connected`
- `lem-asd-etale-finite-twist-pullback`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-comparison-global-cohomology`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-site-sheaves-enough-injectives`

No source-library declaration or module is removed, no module is withdrawn,
and no target signature is changed.

## Where the brief, the DAG or earlier work was wrong

The previous change record incorrectly reported no downstream modules and
omitted three textual users required by the landing check. The refreshed audit
finds 55 downstream modules and explicitly records every textual user of the
relocated rank-one interfaces, including those three conservative matches.

No mathematical statement is disputed. The original plan did not directly expose
the ordinary evaluation calculation and its coefficient normalization. The
adopted source library already proves the finite-abelian Kummer calculation,
which handles the present finite coefficient ring without a freeness assumption.
The packet records that shorter route and keeps the unit's ordinary-Kummer,
support-boundary, and site-comparison argument.

## New nodes

`def-pur-rank-one-local-data` attaches the relocated canonical interfaces to
`Sheaf.Paper.PurityRankOneLocalData`; these are genuine constructions, not
objects chosen from mere existence.

`lem-pur-rank-one-finite-kummer-generator` attaches the coordinate generator
calculation to `Sheaf.Paper.RankOneKummerGenerator`.

`lem-pur-rank-one-finite-kummer-cohomology` attaches ordinary vanishing and
zeroth restriction, together with that normalized generator, to
`Sheaf.Paper.RankOneFiniteKummerCohomology`.

`lem-pur-rank-one-kummer-monomial` attaches the formula for a constant unit
times an integral coordinate power to `Sheaf.Paper.RankOneKummerMonomial`.

`lem-pur-rank-one-classical-support-comparison` attaches existence of the
actual normalized boundaries and the canonical ordinary comparison to
`Sheaf.Paper.RankOneClassicalSupportComparison`.

Change record: `coord/changes/rank-one-local-data.md`.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
