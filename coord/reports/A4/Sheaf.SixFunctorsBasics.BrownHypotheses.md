## What changed

Reworked `Sheaf.SixFunctorsBasics.BrownHypotheses` against the restored dependencies.
Its original source now compiles against the published build; the historical cluster-restore
failure was not reproduced. The mathematical obstruction is still present, so this is a
partial proof delivery and diagnostic, not a claim that the arbitrary-field theorem is proved.

Added `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness`, proving
`CategoryTheory.brownHypothesesFiniteFieldCompactness`: the supported geometric finite-field
compactness assertion now holds inside the actual localizing full subcategory, with an
explicit coproduct witness. The proof uses the existing ambient canonical Hom-map theorem,
the full inclusion's preservation of coproducts, and the existing fully faithful comparison.
The `import all` of the dependency is private and reuses its already-proved comparison helper.

In the item, proved the private specialization
`CategoryTheory.brownHypotheses_finiteIntermediateField`: the complete original Brown bundle
for `continuousMapRingObj F`, with `F` any finite intermediate extension of the p-adic
rationals, over the chosen algebraic closure in a `FiniteFieldDatum`. It constructs an
actual small skeleton from essential smallness, proves the skeletal condition using the
fully faithful skeleton functor, transfers compactness along representative isomorphisms,
and invokes the existing formal assembly. Its auxiliary `compact_of_iso` is proved directly.
No definition, original theorem signature, or public import changed. No source-library
file was edited.

Both delivered modules compile cleanly through `lcompile.py --all` (7.6 s and 8.8 s).
A separate axiom probe verifies that the two new proofs inherit `sorryAx` from existing
proof dependencies, together with `propext`, `Classical.choice`, and `Quot.sound`.
No new proof hole or axiom was introduced. This is proof from declared dependencies,
as required by stage 3, rather than a claim of transitive axiom closure.
The compactness comparison covers empty coproduct index types; membership witnesses
are propositions, so choosing them does not change the objects or the assertion.
The skeleton premise excludes an empty representative family whenever Dctf contains zero.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.

The original sole remaining hole is `CategoryTheory.brownHypotheses`
(node `sk-lem-brown-hypotheses`), unchanged and still `STATEMENT-DISPUTED`.
The new public theorem `CategoryTheory.brownHypothesesFiniteFieldCompactness`
(node `a4-brown-finite-field-internal-compactness`) is completely proved from the existing
named dependencies. The private finite-intermediate-field Brown specialization and
isomorphism transport helper also have complete proofs and no `sorry`.
This is a supported specialization of the original argument, not a decomposition that
moves its hole elsewhere, and it does not close the original arbitrary-field hole.

## No longer needed

Removed the unused direct proof import `Sheaf.SixFunctors.BrownHypothesesAmbient`;
the already-proved coefficient-independent `BrownHypothesesStructural` supplies the
ambient structures used by the specialization. The original node's direct ambient
proof dependency was replaced by `h1-brown-hypotheses-structural`.

Replaced the item's direct proof import of `Sheaf.Paper.BrownHypothesesGeneration`
with `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness`. The generation
module is still needed transitively by the proved internal compactness theorem;
it is not withdrawn or counted as a globally pruned module.

No module or declaration is withdrawn. In particular, zero live downstream modules
does not justify withdrawing this item: quarantined parents and their DAG routes
still need the Brown theorem. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof step applies `brownHypothesesGeneration` to an arbitrary
positive-characteristic field, but its actual Lean declaration assumes a
`FiniteFieldDatum` and a scheme over `D.k`, the chosen algebraic closure of a finite
field. There is no datum of that form obtainable from the arbitrary field in the
original theorem. The existing disputed comment already records the missing
cohomological finiteness issue. This delivery keeps that comment and makes the
actual supported setting precise; it does not weaken the theorem or manufacture
the missing datum.

There is also a distinct coefficient-interface mismatch: the original admissibility
predicate includes both the all-continuous-map and finite-subextension-valued
algebraic-closure rings, whereas the current smallness and generation dependencies
only cover the latter algebraic-closure ring. No isomorphism between these rings
is asserted here. Thus importing the stated dependencies is not enough to prove
the original signature. The original natural-language proof remains a plan subject
to these two gaps; the node proof now records the supported specialization and the
remaining obstruction explicitly.

Consumer audit: `tools/downstream.py` finds no live downstream module. The preserved
quarantine nevertheless contains `ExceptionalInverseImageExistence`,
`BrownExceptionalAdjoint`, `LocalizingExceptionalAdjoint`, and `MateOpenRestriction`
importing the item. `LocalizingExceptionalAdjoint` still invokes the original theorem
twice under arbitrary-field assumptions. All original statements, definitions and
public imports remain identical, so those consumers need no adaptation from this packet.
The preserved quarantine source and its dependencies were not deleted or replaced.

## New nodes

`a4-brown-finite-field-internal-compactness` records the fully proved internal
compactness theorem, its exact Lean statement, geometric finite-field and coefficient
hypotheses, source, searches and proof dependencies. It is strictly the compactness
part of the Brown argument; generation and thickness are separate existing inputs.
The item node records the corresponding diagnostic route and retains its statement
and Lean attachment. No definition or existing statement changed, so no interface
change record or forced consumer adaptation is required.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
