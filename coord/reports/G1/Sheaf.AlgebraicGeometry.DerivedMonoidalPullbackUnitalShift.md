## What changed

The statement of `AlgebraicGeometry.exists_derivedMonoidalPullback_unitalShift` is
unchanged. Its proof now imports
`Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne` and
`Sheaf.Algebra.Homology.KFlatResolution` privately. Four compatibility squares are
extended from K-flat representatives by naturality along replacement isomorphisms,
then from translation by one to every integer by addition coherence, cancellation
of isomorphisms, and faithfulness of shift. The latter extension includes negative
integers and does not cancel any tensor morphism or unitor component.

Four private helpers are proved: `core_of_add`, `shift_of_one`,
`core_of_iso_representatives`, and `exists_kFlat_derived_iso`. Their generic arguments
follow the existing proved helpers in `DerivedPullbackTensorShift`; those helpers
are private there and cannot be imported. The new module contains one public
representative-construction theorem. No definitions, signatures, visibility, or
public imports of the existing module changed.

Validation: both delivered modules compile cleanly through `lcompile.py --all`.
The unit `sk-thm-picard-duality` has empty realized lists; its statement and route
were not changed. This delivery keeps the parent's tensor/pullback construction,
and formalizes the previously implicit localization and integer-shift extensions.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_derivedMonoidalPullback_unitalShift`
(node `lem-sc-derived-monoidal-pullback-unital-shift`). No sorry remains in its module.

Added and left: `AlgebraicGeometry.derivedMonoidalPullback_unitalShift_kFlat_one`
(node `lem-sc-derived-monoidal-pullback-unital-shift-kflat-one`). Its entire proof is
`by sorry`. It asserts coherent exact shifts and only four degree-one squares at
K-flat representatives. The naturality transport to arbitrary derived objects and
the integer-shift extension are proved in the original module.

This is a decomposition: one upper hole closed and one lower hole added, net zero
holes. The geometric construction remains open. It is not a complete geometric
proof and does not claim independence from sorryAx.

## No longer needed

No original import was removed, and no existing node or module is pruned.
`DerivedPullbackTensorShift` and `DerivedPullbackTensorShiftKFlatOne` were inspected
but not imported: they lack the base tensor-morphism and right-unitor clauses, so
their witnesses cannot supply all the simultaneous coherences needed here.
`DerivedCategory.Monoidal.ShiftUnitor` was inspected but not imported: its
right-unitor lemma concerns the unit object with canonical shifts, rather than
all objects for the jointly chosen shifts.

The parent no longer treats its definition nodes as proof-step results: its
proof dependencies are the new representative theorem and `lem-pc-kflat-resolution`.
Its statement dependencies are unchanged; none of those definitions is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The original DAG's two
steps omitted the explicit naturality and negative-integer arguments; these are
now recorded and formalized. The three cited Stacks places do not explicitly state
transport for an arbitrary supplied strong monoidal structure. The new node marks
this part as the existing parent plan's agent expansion rather than attributing it
to a verbatim Stacks theorem. The geometric construction, including that transport,
is still the remaining theorem, not asserted as proved by this delivery.

Sources read online because the untracked literature is not regenerated in this
clone: [08EU](https://stacks.math.columbia.edu/tag/08EU),
[0A9U](https://stacks.math.columbia.edu/tag/0A9U), and
[0A9S](https://stacks.math.columbia.edu/tag/0A9S).
Searches used LeanFinder, Loogle, Mathlib grep and local library/blueprint search;
LeanSearch returned an Internal Server Error. The recorded queries and findings
are in the new node. No exact pre-existing simultaneous representative theorem
was found.

## New nodes

`lem-sc-derived-monoidal-pullback-unital-shift-kflat-one` in
`dag/nodes/sec-picard-framework/` records the representative construction and its
four squares at translation by one, in the new module
`Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne`.
It inherits the parent's chapter, unit, and blueprint ancestor. The four squares
are strictly less than CommShift on all derived objects and all integers; the
missing extension is a complete Lean proof in the original module. Edge cases
zero factors and empty schemes are retained, and zero and negative shifts are
covered by the proved extension. No change record is required: no existing
interface changed.

## Second reading by G1

1. Compared both delivered modules with the repository versions. The existing
   target declaration is unchanged byte for byte; the added module is new, and
   only private proof helpers and proof-only imports were added to the target
   module. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; compilation is clean. The
   only remaining `sorry` is the named representative theorem, and it has the
   matching split node. No forbidden declarations or hollow definitions occur.
   Verdict: pass.
3. Checked the split statement against the parent target and its edge cases.
   It is strictly narrower (K-flat representatives and shift one), is used by
   the parent proof, and is not a restatement of the parent target. Searches did
   not find an existing equivalent declaration. Verdict: pass.
4. The proof transports each degree-one square along K-flat replacement
   isomorphisms, then extends it to all integer shifts by cancellation and
   induction. Imports are minimal for these steps, and no old proof dependency
   is removed without being recorded. Verdict: pass.
5. The parent node's proof, proof dependencies, and origin match the Lean proof;
   the new node records the split theorem and its source, route, and Lean
   declaration. The unit route and realized data are unchanged. Verdict: pass.

Changed after reading: no code or DAG changes were needed; this second-reading
record was appended to document the checks.
