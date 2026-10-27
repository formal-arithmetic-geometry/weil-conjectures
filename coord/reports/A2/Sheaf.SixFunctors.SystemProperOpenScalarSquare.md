## What changed

Extracted all already proved scalar constructions into the new module
Sheaf.SixFunctors.SystemProperOpenScalarData. Their public names, signatures,
instances and definition bodies are unchanged, and the original item publicly
reexports them. Retained its private model_limits_of_flat API as a proved wrapper
for its import-all consumer.

Replaced the main scalar-square hole with an explicit application of
exchangeMate_cube, explicit composition and identity mate calculations, and
shift proofs from exact-derived comparison and adjunction APIs. The two geometric
coherence obligations are stated in separate new modules, with complete proof
plans and DAG nodes. This is a decomposition, not a claim that the full theorem
has become independent of sorry.

Change record: coord/changes/A2-system-proper-open-scalar-data.md.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar.systemProperOpenScalarSquare
by reduction. The delivery adds exactly two holes:

- AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar.scalarIntrinsicAlphaCube
  (lem-sf-scalar-intrinsic-alpha-cube): coefficient naturality of the intrinsic
  inverse-image alpha word, before taking proper mates.
- AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar.scalarInverseImageCoherence
  (lem-sf-scalar-inverse-image-coherence): composition and identity equations for
  the specified inverse-image/tensor comparison ell.

The data extraction adds no holes. All auxiliary theorems are proved. This is
one original hole closed and two smaller holes added, a net increase of one.

Remote compilation passed for SystemProperOpenScalarData (51.8 s),
ScalarIntrinsicAlphaCube (33.7 s), ScalarInverseImageCoherence (27.1 s), and
SystemProperOpenScalarSquare (10.1 s). Both unchanged direct consumers,
EtaleSystemScalarMateCoherence and ExceptionalRefinementMates, also compiled
against the delivered item and data; the compiler accepted every requested file
under its 60-second run-time check. Reported consumer elapsed totals include
artifact/cache waits. Their unchanged sandbox copies were removed after testing.

## No longer needed

No module is withdrawn and no public import is removed from the reexported API.
The original construction imports remain explicit public imports of the item
and also occur unchanged in the data module, preserving the existing API. The
coefficient exactness and open comparison parts of the original DAG proof now
belong to the construction node; the intrinsic cube and inverse-image coherence
parts belong to the two new lemma nodes. Their dependencies are retained there.
No claim of whole-library pruning is made.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. Preflight identified an overlong
lean.statement metadata entry for the new data node (it included the definition
body); this was corrected to the exact declaration signature. The remaining geometric naturality and
inverse-image coherence were described in words but had no separate Lean
statements. The new obligations state those steps on the existing canonical
maps. They cover identity maps, zero systems, empty opens or complements and
unbounded complexes, and add no properness or finiteness hypotheses beyond those
already required to state the constructions. The unit route is unchanged.

## New nodes

- def-sf-system-finite-free-scalar-data owns the verbatim extracted construction
  data, independently of the final coherence theorem.
- lem-sf-scalar-intrinsic-alpha-cube is the inverse-image geometric cube from
  original steps 2--4; the actual proper-mate calculation is proved in the item.
- lem-sf-scalar-inverse-image-coherence is the inverse-image composition and
  identity calculation in original step 6; the direct-image mate equations are
  proved in the item from it.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
