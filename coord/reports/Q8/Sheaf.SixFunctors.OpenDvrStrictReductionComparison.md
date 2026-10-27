## What changed

Replaced the hole in `WeilConjectures.openDvrStrictReductionComparison` with a
construction from normalized completion-unit models. The comparison on flat-term
K-flat resolutions constructs the natural derived tower comparison, and the
normalized Hom formula proves the total derived-limit identity by cancelling the
exact restriction and ordinary limit comparisons. No target or existing public
signature changes. The sequence-site size instance is pinned locally to its
actual object universe; no shared instance is changed.

Added `Sheaf.SixFunctors.OpenDvrOrdinaryTensorTransport`, containing one ordinary
tensor transport statement. Added `Sheaf.SixFunctors.OpenDvrScalarUnitFormula`,
containing the explicit ordinary adjunct `openScalarComplexAugmentation` and the
proved total-limit identity `openDvrScalarUnitFormula`. That remaining statement concerns ordinary module
functors and cochain towers, independently of S and all derived reduction/limit
comparisons. K-flat transport is proved using the existing ring-isomorphism tensor
transport theorem, rather than included in the remaining statement.

Profiling identified repeated elaboration of the derived-category and right-derived
functor implementations. Local irreducibility attributes and an explicit ordinary
model construction reduce this cost. The proved scalar unit calculation and the natural tower comparison on resolutions
are then compiled separately; no shared definition or instance is modified.

Validation: all four modules compile without warnings through `lcompile.py --all`: 
`OpenDvrDerivedTowerComparison` 50.9 s, `OpenDvrScalarUnitFormula` 33.5 s,
`OpenDvrOrdinaryTensorTransport` 13.6 s, and the item 40.2 s.
The original structure and theorem signature are unchanged.

## Proved and sorry left

Closed: `WeilConjectures.openDvrStrictReductionComparison` (the item's only hole).
Added: `WeilConjectures.openDvrOrdinaryTensorTransport`, node
`lem-sf-open-dvr-ordinary-tensor-transport`. No other sorry remains in the delivery.
`WeilConjectures.openDvrScalarUnitFormula` and
`WeilConjectures.openDvrDerivedTowerComparison` are fully proved.
This is a decomposition: one upper hole closed and one strictly smaller ordinary
transport hole added. The derived comparison and total-limit assembly are complete
Lean proofs, conditional on that ordinary transport statement.

## No longer needed

No original import was removed: the original public import supplies the statement.
The item no longer directly uses `lem-sf-sequence-tensor-augmentation-unit`
(`Sheaf.CategoryTheory.SequenceTensorAugmentationUnit`). The already proved
ordinary adjunction and fixed-calculus comparison give the whole-system normalized Hom formula,
so there is no need to obtain a second existential sequence-projection calculus or
compare its normalization with S. The proof never uses finite derived-limit
projections to detect equality. The ring-isomorphism tensor transport and
comparison-on-resolutions imports now occur in the new proved
`OpenDvrDerivedTowerComparison` module; their mathematics remains needed.

`lem-pur-ring-iso-quotient-system-transport` remains relevant to the new ordinary
transport obligation. It is not globally pruned. Its public statement transports
its own strict semilinear reduction functors; it does not directly identify the
completed-adic internal tensor tower with the scalar-restricted ordinary tensor
model M required here. The new statement records that ordinary identification and
its augmentation, without repeating the derived comparison of the assigned item.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's derived sequence augmentation construction
can be replaced by the existing fully proved `CompletionUnit.ordinaryModel_exists`
and `fixedDerivedComparison`, together with the canonical limit comparisons.
The existing ring-isomorphism tensor transport theorem also already proves the
K-flatness preservation needed by the comparison on resolutions.

The ordinary transport statement has been checked on zero complexes and the empty
site. It assumes no flatness of the quotient rings, boundedness or exact countable
products. Its natural-language proof specifies the ordinary sheaf tensor maps and
their inverses. No data definition uses an unproved existence choice.

## New nodes

`lem-sf-open-dvr-ordinary-tensor-transport`, in
`dag/nodes/sec-six-functors/lem-sf-open-dvr-ordinary-tensor-transport.json`, realizes
the ordinary tensor-identification part of steps 1 and 2 of the assigned node.
It has no derived calculus parameter S, derived reduction comparison, or derived
limit equation. Its source is the sheafified tensor universal property, Stacks
03EK, applied to C's canonical coefficient projection and transition squares.
Searches used LeanFinder, Loogle, LeanSearch and Mathlib grep; none supplies this
normalized strict sheaf quotient-tower comparison. No blueprint duplicate was
found by `blueprint_refs.py search 'quotient tensor transport'`.

`lem-sf-open-dvr-scalar-unit-formula`, in
`dag/nodes/sec-six-functors/lem-sf-open-dvr-scalar-unit-formula.json`, is fully proved.
It isolates the ordinary constant/limit adjunct and derives the total-limit unit
equation from the normalized Hom formula, without assuming invertibility or
flatness. Its canonical normalization is proved by cancelling localization
factors. The separate module avoids repeated elaboration of large derived
functor implementations in the parent. No additional hole is introduced. A whole-blueprint search for
"constant limit adjunct" found no existing node for this formula.

`lem-sf-open-dvr-derived-tower-comparison`, in
`dag/nodes/sec-six-functors/lem-sf-open-dvr-derived-tower-comparison.json`, is fully
proved. It compares two derived functors using their counits on a resolving class
and proves the exact counit square. Its hypotheses are only an ordinary tensor
comparison and a natural comparison invertible on flat-term K-flat complexes; it
constructs neither an augmentation nor a total-limit identity. This separate
module reduces the large proof term checked in the parent, with no new hole.
A whole-blueprint search for "comparison on resolutions" found no duplicate.
The proof explicitly imports `TensorColimitsIndependentCoefficients` for the
comparison between the two sheaf tensor APIs used in the flatness hypothesis.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
