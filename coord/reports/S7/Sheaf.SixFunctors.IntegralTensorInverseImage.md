## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralTensorInverseImage` in
`Sheaf.SixFunctors.IntegralTensorInverseImage` from existing library declarations.
The theorem's full signature, coefficient ring, ambient uncompleted tensor,
open-extension functor and right-derived closed-image functor are unchanged.

The completion helper now uses the existing
`IntegralModelsEmbedded.completedComplete` predicate on ordinary inverse image,
with a generator of the maximal ideal. This replaces the independent raw
cone/product presentation with the canonical intrinsic completeness interface.
The mathematical equivalence (including the canonical quotient unit), exact old
and new definitions, and complete consumer audit are in
`coord/changes/S7-integral-pullback-completion-predicate.md`. This is an explicit
non-definitional definition repair requiring independent review. It adds no
completeness hypothesis to the theorem. No data is chosen from a mere unproved
existence statement.

The proof uses existing exact inverse-image preservation, the proved
constructibility-predicate comparison, and only clause (2) of `integral_models`.
It does not use that theorem's pullback or tensor preservation clauses. Tensor
closure is the existing integral-coefficient specialization of
`boundedConstructible_tensor_closure`. Open extension uses its existing
preservation theorem; closed image is assembled from exact recollement, exact
derived homology comparisons and constructible open/closed image preservation.
No source-library module was edited. Explicit local instances bridge bundled
`Over` morphisms to the scheme-over-base hypotheses without changing signatures.

The node's proof, proof_deps, proof_origin and Lean note now describe this route.
The definition requires a public import of `Sheaf.Paper.IntegralModels`; the other
new imports are private proof imports. All three finite-cone helper declarations
remain unchanged.

## Proved and sorry left

Holes closed: 1 of 1, namely
`AlgebraicGeometry.ProEtale.CondensedRing.integralTensorInverseImage`
(node `sk-lem-int-tensor`). No `sorry` remains in the delivered module.
Holes added: 0. Split off: 0. New modules: 0.

This is a complete proof from the existing statements, as required by stage 3.
It still depends on existing unfinished imported results, in particular
`AlgebraicGeometry.ProEtale.integral_models` (node `sk-lem-integral-models`);
closing the local hole is not a claim of eliminating every transitive sorry or
of completing any Challenge target.

The candidate compiled without errors or warnings through `lcompile.py` in
34.6 seconds before the final documentation/import cleanup; final compile and
mandatory delivery checks are run on the submitted packet. The source searches
and complete declaration reads confirmed all applied signatures. Zero complexes,
empty schemes, identity morphisms, integral torsion cohomology and the first
positive reduction require no extra hypothesis. Tensor remains uncompleted.

## No longer needed

Removed private imports of `Sheaf.Paper.IntegralTensorProduct`,
`Sheaf.Paper.IntegralTensorPullback`, and `Sheaf.Paper.IntegralTensorShriek`.
Their nodes `det-lem-int-tensor-product`, `det-lem-int-tensor-pullback`, and
`det-lem-int-tensor-shriek` are no longer direct proof dependencies of this item.
Existing declared preservation theorems avoid transport between the arbitrary
finite-extension coefficient model and this module's embedded coefficient model.
Some of these modules remain transitively imported or have other consumers; this
packet does not withdraw them or claim they are globally unnecessary.

Removed the now-unused explicit public import
`Mathlib.CategoryTheory.Limits.Shapes.Products`. The finite-cone helper API is
retained. No Lean module or DAG node is deleted.

The unit's preservation assertions and its integral local-model/devissage route
remain: the tensor theorem used here is the one explicitly cited at the end of
the current unit proof, and the inverse-image and open-extension theorems are
also explicit citations there. The intrinsic-completeness clause is obtained
from the same integral-models criterion used by the inverse-image dependency.
The remaining earlier DAG route below this unit is not an obligation to duplicate
existing declarations.

## Where the brief, the DAG or earlier work was wrong

The planned dependency interfaces do not apply verbatim: the shriek and tensor
files use a general finite extension and a spectral continuous coefficient model,
while this item uses an embedded finite intermediate field. The pullback file
uses a strict finite-quotient/Roos unit and `constantModelBoundedConstructible`,
where this item originally independently encoded a cone-product triangle and
uses upstream `boundedConstructible`. These are interface mismatches, not false
mathematical assertions. The existing predicate-comparison theorem resolves the
constructibility mismatch. Reusing intrinsic completeness resolves the duplicate
completion interface; the change record exposes the semantic equivalence for
independent review rather than silently weakening a conclusion.

Searches run before writing the proof are recorded in `searches.jsonl`:
LeanFinder on derived-complete inverse image, Loogle on mapping-cone triangles,
and grep on derived completion/completed pullback. No direct Mathlib result was
found; repository searches found the exact preservation statements used here.
The latest blueprint's companion proof was read, not an older snapshot.

Requested generic tool uses for the maintainer's independent review are
`sk-lem-integral-models` (only clause (2)),
`lem-sfb-adic-constructibility-predicate-comparison`,
`lem-weil-pbc-condensed-open-closed-recollement`, and
`lem-weil-pbc-condensed-constructible-open-closed-images`.
The latter two are precisely the exactness/constructibility argument of the
unit's first paragraph. The remaining applied preservation declarations are
`lem-sfb-dc-upper-star-preserves`, `lem-sfb-dc-tensor-preserves`, and
`lem-sfb-dc-open-lower-shriek-preserves`, all explicit citations of the unit.
No maintainer tool_uses approval was added or edited by this worker.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
