## What changed

The existing declaration `CategoryTheory.Functor.exists_rightDerivedFunctor_truncated_bottom_unit`
keeps its signature byte for byte. Its proof now uses a specified double-truncation comparison,
then transports a canonical-cycle formula to arbitrary left homology data by kernel uniqueness
and `LeftHomologyData.π_comp_homologyIso_inv`.

Added `Sheaf.CategoryTheory.Abelian.DerivedBottomComparison`, with the concrete definition
`CategoryTheory.Functor.rightDerivedFunctorTruncatedBottomIso`. Its body is the actual composite
already constructed in the proved `rightDerivedFunctor_truncated_bottom` proof, ending with the
inverse degree-zero unit and inverse homology of the lower-truncation projection. All data are
constructed; no witness is selected from a mere existence theorem.

Repaired `Sheaf.CategoryTheory.Abelian.DerivedBottomUnitNormalizationFormula`: its remaining
statement concerns only the canonical cycle lift and quotient, for this specified comparison.
Its docstring gives the complete smart-truncation, unit-naturality, shift and degree-zero argument.
The closed single-object unit comparison is imported privately for this proof dependency.
The construction imports are public because their definitions occur in the new public data;
the item's new formula import is private. Redundant imports were removed from both new modules.

## Proved and sorry left

Hole closed: `CategoryTheory.Functor.exists_rightDerivedFunctor_truncated_bottom_unit`
(node `lem-pc-derived-bottom-unit-normalization`), conditional on the lower canonical calculation.
The construction `CategoryTheory.Functor.rightDerivedFunctorTruncatedBottomIso`
(node `new-def-pc-derived-bottom-comparison`) has no holes and its axiom check lists only
`propext`, `Classical.choice`, `Quot.sound`.

Hole added: `CategoryTheory.Functor.normalized_bottom_unit_formula`
(node `new-lem-pc-derived-bottom-unit-normalization-formula`), the sole named `sorry` in the
three delivered modules. It contains no existential comparison and no arbitrary T, U or k.
The construction and the transport from arbitrary data to canonical cycles are completed;
the explicit canonical cycle computation remains open.

This is a decomposition: one original hole closed, one lower hole added, net zero.
The item is not claimed to be axiom-clean: both the item and the formula have `sorryAx`
from that listed remaining statement, in addition to the three permitted axioms.
No holes were added to definitions. All three modules compile without warnings.

## No longer needed

Removed the item's private import `Sheaf.Paper.DerivedSectionsLeftExactBottom`.
Its node `new-qcoh-sections-left-exact-bottom` is no longer a proof dependency: the
particular comparison must be constructed explicitly, so the mere Nonempty statement
is insufficient. Its proved construction is reused as code in the new data definition.
This prunes that wrapper from this item's imports; other library users may still need it.

The original direct dependencies `lem-sp-derived-functor-single-identification` and
`src-right-derived-functor-plus-compatibility` move under the explicit construction;
they remain used transitively and their modules are retained. The parent's direct
proof dependencies are now precisely the concrete construction and canonical formula.
No unit statement or realized proof step is removed or bypassed. The relevant
`dag/units/sk-thm-picard-semicon.json` has empty realized statement and step arrays;
its unit and chapter route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous worker treated `Classical.choice (S.rightDerivedFunctor_truncated_bottom n)`
as a canonical isomorphism. The theorem's Nonempty conclusion does not determine a
particular isomorphism: composing with a natural automorphism gives another witness.
Already for the identity functor on vector spaces, negating an isomorphism illustrates
why the normalization is additional information. The earlier formula had no reason to
hold for the unspecified witness, its docstring merely referred back to the parent,
and the parent's node still described the old proof. Those faults are repaired.

## New nodes

`new-def-pc-derived-bottom-comparison`, in
`dag/nodes/sec-picard-framework/new-def-pc-derived-bottom-comparison.json`, exposes the
actual double-truncation composite. Its proof follows the existing proved bottom
comparison construction and uses the same negative-vanishing, triangulated,
single-object and Plus compatibility results. It selects no arbitrary data.

`new-lem-pc-derived-bottom-unit-normalization-formula`, in
`dag/nodes/sec-picard-framework/new-lem-pc-derived-bottom-unit-normalization-formula.json`,
is repaired to state only the canonical-cycle calculation for that specific composite.
Its proof dependencies include the already proved single-object unit comparison.
The cycle lift is Mathlib's real `ShortComplex.liftCycles`; no new cycle notion is defined.
There are no statement-change records: no existing statement or definition was changed.

## Second reading by K2

1. Compared the delivered item with the repository using diff. Its existing signature,
   universes, assumptions, visibility, options and docstrings are unchanged byte for byte.
   Only the private proof import and theorem proof change. The other two modules are new.
   Verdict: no accidental interface or target change.
2. Compiled every delivered module in import order through lcompile.py, then compiled
   scratch copies with `#print axioms` for all three declarations. The concrete data use
   exactly the three permitted axioms. The canonical formula and parent also use sorryAx,
   exactly as reported. Searched the sources for forbidden declarations and escapes;
   the only sorry is the named formula theorem. Verdict: valid conditional Lean proof,
   not a completed axiom-clean proof.
3. Rejected and repaired the arbitrary-witness formula. The replacement separates two
   completed parts (construction and arbitrary-data transport) from the canonical-cycle
   computation. It is a strictly lower part of the parent's argument. Checked zero K and
   zero S, where the displayed maps are zero; for single complexes at n = 0 the formula
   is the degree-zero unit followed by its inverse. Positive and negative n use matching
   shift identifications, with no natural-number bound added. The arbitrary-data transport
   makes no epimorphism-preservation assumption on S. Read the Stacks pages 05TC, 08D4,
   0AVW and the upstream double-truncation and unit comparisons. Independently searched
   Mathlib with leanfinder, loogle and grep through msearch.py and searched both Lean roots.
   Leansearch was unavailable and is recorded without an absence verdict. Mathlib has
   the kernel, quotient and degree-zero identities, but no whole canonical formula;
   the existing single-object unit comparison is reused. Verdict: the remaining statement
   is mathematically justified, sourced and documented; it still requires formal proof.
4. Used the existing bottom-comparison proof for the data and Mathlib's kernel uniqueness
   and homology-data identities for the transport. Pruned the obsolete existence-wrapper
   import and redundant imports in the new modules. Checked the unit realized record and
   retained its route. Verdict: the shortest available construction was reused and all
   abandoned original direct dependencies are accounted for above.
5. Updated the parent's proof, proof_deps and proof_origin to the actual reduction; the
   two new nodes record the actual construction and remaining canonical formula, with
   verbatim Lean signatures and real searches. Their dependency lists are the unions
   of proof-step uses. The formula no longer has a dependency on the parent being proved.
   Verdict: nodes agree with Lean and the split introduces no circular argument.

Second reading changed the unspecified-witness construction into explicit data,
restricted the remaining formula to canonical cycles, proved arbitrary-homology-data
transport, expanded the hole's proof docstring, corrected nodes and searches, pruned
imports, and corrected the report's claim of progress to a net-zero decomposition.
