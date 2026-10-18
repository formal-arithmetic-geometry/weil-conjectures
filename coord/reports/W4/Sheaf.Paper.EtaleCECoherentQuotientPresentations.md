## What changed

Proved `AlgebraicGeometry.Etale.exists_etaleCE_coherent_quotient_presentations`
with its statement unchanged. Choose the existing supported CE resolutions, then
apply the existing normalized representative-cohomology construction. The private
helper `quotient_coherence_of_normalized` transports its normalized successor
comparisons to the quotient-coherence interface. For the first-page equation,
test the supplied component on source row cycles and the corresponding target
row cycles. Diagonal inclusion naturality supplies the premise, and cancellation
of the isomorphic row-cycle comparison and epic boundary quotient proves the
map equation. No filtered-map hypothesis or map on another bidegree is used.

Added proof imports for `CartanEilenbergAllLowerBounds`,
`FilteredComplexSuccessorCyclesCover`, `EtaleCENormalizedRepresentativeCohomology`,
`EtaleCECanonicalRowComparison`, and `EtaleCERowCyclesNaturality` (the last with
`import all` to use the already proved private diagonal inclusion calculation).
Updated the item's proof steps, proof dependencies and proof origin to this
route. No existing declaration signature or public import changed. No other
module is adapted. The proof uses a local irreducibility attribute on the CE
comparison definitions so elaboration uses their equations instead of expanding
the chosen witnesses; this does not change any exported definition.

Validation: the final delivery dry run passed compilation, the axiom probe
and stage-3 preflight (`OK`, review class CODEX).

Sources read: Stacks Derived Categories Tags 015I, 015J and 015K, and Homology
Tag 012K, including the actual cycle/boundary and first-page formulas. The unit
record `sk-prop-h2` has no realized statement or proof-step attachment to this
node; the same CE first-spectral-sequence construction is retained.
The successor-cycle cover is used as a generic abelian-category quotient tool,
not as a replacement for any statement or proof step of another unit.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.exists_etaleCE_coherent_quotient_presentations`
(node `lem-weil-pbc-ce-coherent-quotient-presentations`). Added zero holes.
No `sorry` remains in the delivered module, and there are no new modules or
split-off statements. The final single-file compile passed without warnings
in 58.1 seconds before the final elaboration optimizations. The private coherence helper and the diagonal-inclusion API equation
`rowInclusion_eq_rowι`, and the generic epic quotient projection
`pageProjection_epi` are also proved. The two embedded arithmetic proof
certificates in the statement now use `Int.le_add_one` directly; the declaration
type is definitionally unchanged by proof irrelevance, with every binder,
hypothesis and conclusion retained.

## No longer needed

Removed these direct proof imports and their direct DAG proof dependencies:

- `Sheaf.CategoryTheory.CartanEilenbergExists`
  (`lem-sp-cartan-eilenberg-exists`): the supported all-lower-bounds resolution
  theorem supplies precisely the bounded-below augmented resolutions needed.
- `Sheaf.CategoryTheory.HypercohomologyFirstPage` (`thm-sp-if-e1`): the existing
  normalized representative-cohomology construction already supplies the
  presentation fields, ordinary comparison and local comparison equation.
- `Sheaf.CategoryTheory.FilteredComplexPageHomology`
  (`lem-sp-filtered-complex-page-homology`): use the normalized successor
  equation supplied by that construction rather than choose another homology
  isomorphism with unspecified representative behavior.
- `WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
  (`lem-weil-pbc-sheafH-ext-derived-comparison`): ordinary pullback on
  representatives is already calculated by the normalized construction.
- `Sheaf.CategoryTheory.FilteredComplexPageDifferential`
  (`lem-sp-filtered-complex-page-differential`): the differential witnesses are
  supplied with the normalized pages; its definitions remain publicly available
  through the unchanged statement imports.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
  (`def-weil-pbc-cohomology-pullback` as a direct proof dependency): cohomologyMap
  occurs in the unchanged statement, while the normalized local equation
  already computes it.

These are removals from the item's direct proof route, not claims that the
modules disappear from the complete target import closure: some remain used by
the normalized construction or by the statement imports. No module is withdrawn.
The two existing public statement imports are retained.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The earlier direct proof plan omitted the
normalization interface needed to turn an arbitrary successor homology
isomorphism into the representative-fixed one. Existing normalized CE modules
already resolve this issue, and the updated proof uses their actual signatures.
A filtration-preservation premise is unnecessary here: source row cycles have
explicit related target row cycles under the supplied diagonal-compatible map.

LeanFinder, Loogle and grep searches found no direct Mathlib theorem for this
simultaneous CE statement. Repository searches found the supported resolutions,
normalized representative equation, canonical row-cycle comparison and diagonal
inclusion naturality used above. Zero rows, zero complexes, p = 0 and empty
schemes require no exceptions: the proof uses only the stated universal
properties, isomorphisms, cycle maps and epimorphisms.

The static delivery checker requests an interface record for the two arithmetic
proof certificates and local attribute commands. See
`coord/changes/W4-ce-quotient-proof-certificates.md`; it lists all seven downstream
modules and the item's direct consumer. This is a proof-irrelevant certificate
change, with no new or removed premise and no consumer adaptation.

The unchanged direct consumer was inspected and copied only for a paired
compatibility compile. That compile stopped at the item's 60-second limit before
reaching the consumer; its temporary copy was removed and no compatibility
compile is claimed. The old/new statement certificates are definitionally equal,
so the consumer requires no code adaptation. The independent reader can check
the unchanged consumer against the delivered interface.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
