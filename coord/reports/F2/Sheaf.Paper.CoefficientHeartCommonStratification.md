## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification` with its original
signature by assembling its three clauses. The ordered-refinement proof uses Noetherian
induction on closed subsets, selecting a nonempty irreducible relative open and recursively
stratifying its closed complement. Finite intersections refine all input partitions, and
vanishing-ideal subschemes realize the pieces. This gives connected domains and open prefixes.

The lisse proof pulls back finite-free covers, converts finite constant models into local finite
presentations, and applies the existing immersion-range local-finite-presentation theorem to raw
inverse images, then normalizes the coefficient comparison again. The existing finite-subfield and algebraic-closure local-triviality lemmas then
give lisse restrictions on the actual refined scheme structures. Exactness follows from exact
pullback, underlying-sheaf comparison, finite-stratum zero detection, cancellation for mono/epi,
and the kernel-to-cokernel criterion for exactness.

The independent geometric and lisse clauses are proved in
`Sheaf.Paper.CoefficientHeartOrderedRefinement` and
`Sheaf.Paper.CoefficientHeartLisseRestriction`. The three original definitions moved verbatim to
`Sheaf.Paper.CoefficientHeartStratificationDefs`, publicly re-exported by the original module to
avoid an import cycle. Their names, universes, bodies and visibility are unchanged. Consumer
statements and all target statements are unchanged.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification`.

The three clause theorems and every private helper have complete Lean proofs:

- `AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification_refinement`, node
  `new-det-lem-coefficient-heart-common-stratification-refinement`.
- `AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification_lisse`, node
  `new-det-lem-coefficient-heart-common-stratification-lisse`.
- `AlgebraicGeometry.ProEtale.coefficientHeart_commonStratification_exactness`, node
  `new-det-lem-coefficient-heart-common-stratification-exactness`.

No `sorry` remains in any delivered Lean file and none is added. This closes one original hole,
with zero split-off holes. Existing imported declarations retain their own proof dependencies;
no claim is made that the full targets are axiom-free. Empty schemes, zero input stratifications,
empty intersections, arbitrary refined scheme structures, and rank zero are covered.

## No longer needed

Removed these original proof-only imports from the assigned module:

- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.Topology.NoetherianSpace`
- `Mathlib.Topology.Connected.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `Sheaf.Paper.CondensedSurjectiveClosedEquivalence`
- `Sheaf.Paper.CartesianCoefficients`

The reduced-induced subscheme module is used by the new refinement module. The lisse module
uses the existing `FiniteEtaleLocallyFreeModels`, `CondensedConstructibleSerre`, and
`ProEtaleModuleLfpImmersionTransport` interfaces, rather than directly importing the
cover-refinement and surjective-closed equivalence modules. Those ingredients remain inside
the imported immersion-range transfer theorem and are not claimed globally pruned.

Noetherian induction replaces the original finite-atom and connected-component graph argument.
Consequently the refinement clause does not separately use
`lemma-constructible-common-refinement`, `lem-weil-pbc-proper-fp-permanence`, or
`lem-weil-pbc-noetherian-open-subscheme-noetherian`.
The exactness proof does not separately use `sk-prop-sfb-cartesian-coefficients`:
the required exactness instances and coefficient comparison already belong to the source library.
All original public imports remain. No existing module is claimed globally unreachable, and no
unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report predated the completed refinement and lisse proofs and incorrectly listed
them as two remaining holes. It has been replaced with the actual hole census.

Containment of stratum images does not give a scheme factorization; the lisse proof correctly
uses the existing raw inverse-image immersion-range theorem, whose proof uses a fibre
product and reflection through a surjective closed immersion. The Noetherian ordered refinement can be built directly with irreducible
pieces, giving a shorter implementation of the blueprint's Noetherian-induction argument.
The exactness proof uses the existing kernel-to-cokernel criterion instead of constructing a
homology quotient. No mathematical statement is disputed or weakened.

The retained identity scalar-extension proof caused a deterministic kernel timeout. The
finished proof avoids that comparison by using the existing raw inverse-image transfer
interface. Generic private helpers isolate the normalized comparison and the conversion
from a raw finite-free cover; all helpers are proved, and no compile limit was changed.
The resumed dry run compiled all four delivered modules and passed preflight.
The independent-review class is CODEX because this delivery adds nodes and relocates definitions.
The consumer record was refreshed against all 23 current direct importers and every
module mentioning the relocated declarations, including transitive users; no consumer
is modified, and all three relocated definitions were checked byte-for-byte against the originals.

The two auxiliary coefficient modules are used as tools for their already-proved local-freeness
and finite-presentation helpers. No separate statement in this unit supplies that interface.
They introduce no alternative unit-level proof route.

The resumed dry run (`dry-run-0645.log`) passed compilation and preflight at commit
`05a98a40e8`. Both subsequent submissions (`delivery-0657.log` and
`delivery-retry-0730.log`) failed before the push: the delivery wrapper raised
`subprocess.TimeoutExpired` after `tools/preflight_delivery.py` exceeded its
900-second timeout. This is a delivery-tool failure, rather than a Lean file exceeding
its compile limit. The completed proof remains in this sandbox; neither submission
was pushed.

The 2026-10-19 continuation verified all four Lean files contain zero `sorry` tokens,
all lines meet the 100-character limit, and the relocated definitions are byte-for-byte
identical to the current originals. The consumer table was refreshed to include
`Sheaf.Paper.ConstructibleCompactness`. No Lean proof or statement needed adjustment.

The three new node statements are written as self-contained mathematical statements;
their exact Lean signatures remain in `lean.statement`. Their source locations now
identify clauses (1), (2), and (3) explicitly.

Fresh `lcompile.py --all` verification succeeded for all four modules with exit code 0
and no diagnostics (definitions: 0.1 s; lisse: 1.4 s; refinement: 0.1 s; assembly: 1.2 s).

The assembly theorem docstring now describes the actual completed three-clause proof
in place of the superseded seven-step plan. Its signature and proof term are unchanged.

The latest continuation dry run (`scratchpad/dry-run-current-continuation.log`) passed at
`c43596f6eb` against current sources: all four modules compile and server preflight passes.
The compile service did not answer three axiom probes; the delivery tool explicitly leaves
those probes for the maintainer to rerun. The current 23 direct importers and all textual
consumers are covered by the change record. All three moved definitions were rechecked
byte-for-byte against current sources, and all four files have zero holes and no long lines.

The final resumed dry run (`scratchpad/dry-run-resumed-final.log`) passed with exit code 0
at `830ac5495a`: all four modules compile and server preflight accepts the delivery.
The assembly module's axiom probe received no response within 208 seconds; the delivery
tool records that the maintainer reruns it. The other three probes reported no failure.
The final source audit again found zero holes, no lines over 100 characters, identical
relocated definitions and original theorem signature, all 23 direct importers and all
textual consumers covered by the change record, matching proof-dependency unions, and
no cycle among the 785 DAG nodes reachable from the updated item.

## New nodes


`new-det-lem-coefficient-heart-common-stratification-refinement` records the proved ordered,
connected common refinement in its own module. Its proof and dependencies follow the actual
Noetherian closed-subset induction, with its source and recorded searches.

`new-det-lem-coefficient-heart-common-stratification-lisse` records the proved lisse clause in its
own module. Its proof records pullback of free covers, preservation of finite presentations,
immersion-range local-finite-presentation transfer, and the two existing coefficient
local-triviality results.

`new-det-lem-coefficient-heart-common-stratification-exactness` records the proved exactness
clause in the assigned module and its actual zero-detection and kernel-to-cokernel argument.

The existing main node records assembly of these three proved clauses. The existing
`def-sfb-lisse-coefficient-module` node points to the shared definitions module. The relocation
and direct-consumer checks are recorded in
`coord/changes/f2-coefficient-heart-shared-definitions.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
