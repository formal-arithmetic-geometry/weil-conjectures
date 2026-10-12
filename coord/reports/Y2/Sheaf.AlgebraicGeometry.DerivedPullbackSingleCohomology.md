## What changed

The original theorem `AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single`
now has a complete Lean proof with its statement unchanged. It factors the morphism through an
open locus, uses derived composition, maps the concentration isomorphism by derived pullback,
and takes cohomology. Ordinary restriction and pullback composition finish the isomorphism.

A proved private helper `nonempty_derivedPullback_flat_single_iso` computes derived pullback
of any flat single object in any integer degree. It uses the existing
`AlgebraicGeometry.flatComplexDerivedPullback`; the proof explicitly verifies boundedness and
flatness of every term, transports the homotopy/localization comparisons, and identifies tensor
pullback with ordinary pullback by uniqueness of left adjoints. The tensor-closed theorem
supplies the additive monoidal structure for the zero-term flatness argument.

`Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus` isolates the first step of the original plan.
It constructs an open neighbourhood of an arbitrary set of points and describes the derived
restriction there as a flat single object. It has no arbitrary-morphism pullback conclusion.
The original and new node records describe the implemented route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single`
(node `lem-pc-derived-pullback-single-cohomology`). The private flat-single helper is proved
without a hole. The item's module has no remaining `sorry`.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_flat_single_open_locus`
in `Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus`,
node `lem-pc-derived-single-open-locus`. Its entire proof is `:= by sorry`; its docstring and
node give the union-of-opens, local vanishing, flatness, exact restriction and truncation proof.
This is a decomposition: one original hole closed, one narrower hole added, net zero holes.
The imported flat-complex and derived-composition theorems retain their existing upstream
holes; those holes are neither copied nor changed by this delivery.

The two sandbox modules compile together without warnings using `lcompile.py --all`.
Edge cases checked in the mathematical argument: the empty point set/empty image, a zero sheaf,
rank zero, varying local ranks, degree zero, and arbitrary integer degree in the flat-single
helper. No perfectness, quasi-coherence, properness, or common-rank hypothesis was added.

## No longer needed

Removed the redundant direct proof import `Sheaf.AlgebraicGeometry.DerivedCategory`; its
public interface is already provided by `DerivedPullback`. This does not remove that module
from the transitive import closure. The old proof dependency `def-pc-derived-category`
is removed from `proof_deps`; it remains a statement dependency and is exposed through
`DerivedPullback`. No entire module is pruned: the flat-complex and derived-composition steps of the original plan are both used.
The public statement imports remain unchanged. The new flat-single calculation is a proved
private helper, so it needs no separate public module or future worker item.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature repair was found. The original first proof step had no
separate interface for the open-locus concentration and flatness argument; the new node
provides exactly that interface. Mathlib's single-object concentration theorem handles the
abstract truncation calculation, but does not by itself supply local sheaf vanishing,
flatness, or the identification of chosen derived open pullback with exact restriction.

The source blueprint files are not present in this checkout. The source proof text was read
from the existing perfect-locus and assigned DAG nodes. Stacks Tags 0B9S, 06YD and 05NE were
also checked on the official site. The new node's proof is marked agent-written, as required
for this explicit generalization of the blueprint paragraph. LeanSearch returned an internal
server error; the actual failed queries and successful LeanFinder, Loogle and grep searches
are recorded in `searches.jsonl`. No absence verdict is inferred from the unavailable service.
The unit route is retained; `dag/units/sk-thm-picard-perfect.json` has no realized entries
requiring additional imports.

## New nodes

`lem-pc-derived-single-open-locus`, at
`dag/nodes/sec-picard-framework/lem-pc-derived-single-open-locus.json`, states the open-locus
concentration/flatness step only, in
`lean/Sheaf/AlgebraicGeometry/DerivedSingleOpenLocus.lean`.
Its statement applies to an arbitrary set S of points and has no pullback computation along
an arbitrary g. The proved flat-single helper and the explicit composition proof provide
that remaining part of the original argument. There are no statement changes or change records.

## Second reading by Y2

1. I compared `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology.lean` with the
repository version. The target theorem's signature and its existing declaration text are
unchanged byte for byte; the only target change is replacement of its proof. The added
module has a new declaration and does not alter an existing declaration.

2. I compiled both delivered modules with `python3 /home/ubuntu/weil-launcher/lcompile.py
--all`; both compile without warnings. The target theorem has no `sorry`, and the only
remaining `sorry` is the named public theorem `exists_flat_single_open_locus`, whose
complete source proof is recorded in its docstring and whose matching DAG node is
`lem-pc-derived-single-open-locus`. No definition contains `sorry`, and no prohibited
axiom, `unsafe`, `opaque`, `implemented_by`, or `extern` construct occurs. Explicit
`#print axioms` checks of the target and new theorem returned only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` from the remaining open statements.
The delivery tool also probes every delivered declaration, including the private helper.

3. The split-off open-locus statement is strictly narrower than the target: it has no arbitrary
morphism `g` or arbitrary-morphism pullback conclusion, supplying the local concentration,
flatness, and open restriction isomorphism needed by the target proof. Its edge cases
(empty S, empty open, zero sheaf, rank zero, and varying local ranks) are included by its
quantifiers and do not add hypotheses. Searches recorded in `searches.jsonl` and direct
searches of `lean/` found no existing declaration with this statement.

4. The target proof uses the stated route: the open-locus node, the bounded-above
flat-complex comparison, tensor-closed sheaf modules, derived pullback composition, and
ordinary pullback. The private flat-single helper is a real reduction to the existing
flat-complex comparison, rather than a restatement of the target. The direct proof-only
import of `DerivedCategory` was removed because `DerivedPullback` already exposes the
needed interface. The unit route is retained; no unit-level statement is bypassed.

5. The DAG proof, proof dependencies, and proof origin match the imports and composites
in the Lean proof. The new node records its source, proof steps, searches, Lean
statement, and split status. No statement change or change record is needed.

Second reading changed only this report and added independent searches to the search log.
I found no mathematical or signature defect requiring repair; the Lean proof and nodes
were retained.
