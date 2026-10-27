## What changed

Replaced the original hole in
`AlgebraicGeometry.closedRestriction_signed_refinements` by a complete Lean assembly
from two smaller construction statements. The parent constructs every total map by
termwise `NatTrans.mapHomologicalComplex`, horizontal-first flip, and Mathlib's total
functor. `HomologicalComplex₂.ιTotal_map` proves the required formula on every diagonal
summand. Evaluating the row augmentation equation at degree zero and cancelling the
single-object isomorphism gives the ordinary augmentation equation; this and the
summand formula prove preservation of total augmentation for all unbounded complexes.

The two obligations are individual signed augmented row existence and signed refinement
maps between an already supplied collection of rows. The first constructs no maps
between distinct families. The second constructs no rows or total maps, and applies to
any supplied rows satisfying the original unit and component specifications. Neither
is the target theorem under another name or with a repackaged hypothesis.

Relocated `SignedClosedFamily` and `SignedClosedRow` verbatim into
`Sheaf.AlgebraicGeometry.ClosedRestrictionSignedData`, publicly re-exported by the
assigned module. All four original public signatures and all three original structure
bodies are unchanged. No adopted-source module is changed. No definition selects data
from an unproved existence statement: witnesses are assembled only within the proof of
the existential target. The new data module imports the existing shared finite-row
constructions, not the cover-existence theorem.

Validation: `lcompile.py --all` compiled all four modules without errors or warnings:
data 9.0 s, row maps 7.2 s, rows 4.8 s, assigned module 9.7 s. There are no existing
direct Lean importers of the assigned module to adapt or compile. Exact signature and
structure-body comparisons, node attachment checks, and dependency-cycle checks passed.

Change record: `coord/changes/C4-signed-closed-row-data-relocation.md`.

## Proved and sorry left

Original holes: 1. Closed in the assigned module:
`AlgebraicGeometry.closedRestriction_signed_refinements`
(`lem-sfb-closed-restriction-signed-refinements`). No holes remain in that module.
The private total-map construction, its summand equation, the degree-zero augmentation
compatibility lemma, and the total augmentation compatibility lemma are fully proved.

Added holes: 2, both whole proofs of public named theorems in new modules:

- `AlgebraicGeometry.signedClosedRow_exists`, node
  `lem-sfb-signed-closed-row-exists`, in
  `Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRows`.
- `AlgebraicGeometry.signedClosedRow_maps`, node
  `lem-sfb-signed-closed-row-maps`, in
  `Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRowMaps`.

The data module has zero holes. This is a decomposition, not a complete proof of the
mathematical construction or a net hole reduction: one upper hole is replaced by two
strictly smaller obligations (delivery-local net -1). Each new theorem has a source,
complete proof in words, node, and exact Lean attachment.

## No longer needed

Removed the parent's proof imports of
`Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`WeilConjectures.Combinatorics.SignedFacePermutation`, and
`Mathlib.CategoryTheory.Adjunction.Mates`. The original unit, additivity and sign
arguments remain needed by the lower obligations and are recorded in their proof
plans; none is claimed mathematically obsolete. The new sorry-only modules import
only what their statements require.

The parent's direct public import of `Mathlib.Algebra.Homology.Single` is supplied
through the publicly imported data module, preserving the old public import closure.
The public `FiniteClosedCoverResolution` import remains necessary for the existing
`finiteClosedRefinementMap` formula in the system specification and row-map statement;
the cover-existence theorem is not applied. No existing finiteClosed construction is
redefined or removed.

The parent's old direct proof dependencies are now carried by the two lower statements
where their corresponding arguments remain. The parent needs row existence, row maps,
and the existing total-complex conventions. No node, unit step or existing module is
withdrawn or claimed globally prunable. Zero current Lean importers is not used as a
reason to withdraw the assigned item; its DAG parents continue to need its statement.

## Where the brief, the DAG or earlier work was wrong

No statement defect or target change was found. The original plan groups a substantial
closed-unit/signed-row construction with a separate ordered-refinement argument. The
stated generic unit and deleted-face lemmas do not themselves assert either complete
construction. These two portions are now explicit lower obligations, while their
termwise totalization and preservation of augmentation are formalized in the parent.

The unit route is unchanged. The latest blueprint's direct-image paragraph (3), Stacks
proetale.tex lemma-ses-associated-to-open, and the ordered alternating-cochain formulas
in cohomology.tex were read. The closed-refinement identities remain explicitly marked
as agent deductions, not quotations of Tag 09AH. Small cases checked for the new
statements include a singleton family, empty intersections, zero terms beyond the
family length, empty closed members, repeated refinements, characteristic two, and
negative input degrees; no cover or boundedness hypothesis is used.

## New nodes

`def-sfb-signed-closed-row-data` attaches the two relocated family and row structures;
it adds no new mathematical notion or existence claim beyond the existing fields.
The data are shared to avoid an import cycle. Its Lean attachment lists both unchanged
structures.

`lem-sfb-signed-closed-row-exists` is the individual-family construction: normalized
restriction maps and their compositions, signed row differential and its square,
support, single-complex augmentation, and its termwise total augmentation. It is steps
1--3 and 7 plus the row-augmentation part of step 8 of the original proof. It makes no
refinement or covering assertion.

`lem-sfb-signed-closed-row-maps` is steps 2 and 4--7 for arbitrary already supplied rows:
construct mixed restrictions, prove the chain equation by deleted-face signs and
repeated-pair cancellation, and prove augmentation, identity and composition. It
constructs neither the rows nor their total maps. Three kinds of Mathlib search,
source-library searches and the imported-blueprint duplicate search are recorded.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
