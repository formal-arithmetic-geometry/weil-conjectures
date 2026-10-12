## What changed

The original theorem `HomologicalComplex₂.verticalCutoff_column_quasiIso` has its
unchanged signature and a proof by the genuine integer-order split a<b or a=b.
The strict case is stated in `VerticalCutoffColumnQuasiIsoCore.lean`; the equal
case is stated and proved in its own `VerticalCutoffColumnQuasiIsoEqual.lean`.
Both endpoint modules are imported privately, because only the proof needs them.
No existing definition, signature, visibility or public import changes.

## Proved and sorry left

Original hole closed syntactically:
`HomologicalComplex₂.verticalCutoff_column_quasiIso`, using the endpoint split.
New hole added and still open:
`HomologicalComplex₂.verticalCutoff_column_quasiIso_strict`, node
`lem-sp-vertical-cutoff-column-quasiiso-strict`.
The new `HomologicalComplex₂.verticalCutoff_column_quasiIso_equal`, node
`lem-sp-vertical-cutoff-column-quasiiso-equal`, is proved without new holes.
The equal proof uses only propext, Classical.choice and Quot.sound. The main
and strict declarations still depend on sorryAx through the strict theorem.
This is a decomposition, not a completed proof of the original theorem:
one original hole closed, one new hole added, net zero. Relative to the first
worker's proposal the second reading closes the equal-case hole.

## No longer needed

Removed the redundant direct proof import
`Sheaf.Algebra.Homology.DoubleComplexVerticalWindow`; it is still publicly
available through `DoubleComplexVerticalTowerMaps` and is needed for the types.
The old direct proof dependencies `def-sp-double-complex-vertical-window` and
`lem-sp-double-complex-vertical-tower-maps` are replaced in the main node by the
two endpoint nodes; both old nodes remain required by those endpoint proofs.
No module or node is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The first worker's strict-case docstring incorrectly claimed distinct cutoffs
coincide and have zero quotient. The quotient usually has the original cohomology
in the interval, so that argument is false. Its replacement explains the
contractible image kernel, including adjacent endpoints and nonpositive bounds.
Both new nodes formerly had generic proof steps and incomplete docstrings.
Their statements, proof records and source information now describe their actual
cases. The listed local Stacks source is absent on this machine; the referenced
canonical truncations were checked at https://stacks.math.columbia.edu/tag/0118.
The nested-cutoff argument is explicitly identified as an agent specialization.

## New nodes

`lem-sp-vertical-cutoff-column-quasiiso-strict`: the strict a<b case, with a complete
kernel-and-short-exact-sequence proof in words; the formal theorem remains open.
Searches by support, quotient and homology terminology found existing truncation
APIs but no direct theorem for this nested quotient.

`lem-sp-vertical-cutoff-column-quasiiso-equal`: the a=b case, proved by monicity,
Mathlib's zero cokernel of an epimorphism, strict support of smart truncations,
and the fact that maps between zero objects are isomorphisms. Each new node
has fresh recorded grep, Loogle and Lean Finder searches and an exact Lean
signature. LeanSearch was attempted and returned Internal Server Error; its
unavailability is recorded without a mathematical verdict. No change record is needed: no pre-existing interface changes.

## Second reading by V3

1. Compared the item with the read-only repository using diff. Verdict: its
   entire existing theorem signature is byte-for-byte unchanged; only its proof
   and private imports change. The two helper modules and nodes are new.
2. Compiled all three modules locally in import order. Verdict: no errors or
   warnings, one named theorem with exactly `by sorry`, no forbidden declaration
   forms and no holed definitions. Scratch copies with `#print axioms` confirm
   only standard axioms for the equal case, and standard axioms plus sorryAx for
   the main and strict case. The equal case constructs no arbitrary witness.
3. Read both new statements and searched Mathlib, the upstream source and the
   project with different terminology. Verdict: the equal case is fully proved;
   the remaining strict case is a strict subcase with a complete sourced proof
   in words, not an unchanged restatement under another name. Tested zero
   complexes, a=b, b<=0, a<0<b, a=0<b and b=a+1. In the adjacent case q maps cycles
   to homology with image-boundary kernel; it need not be an isomorphism on terms.
4. Checked shortest routes and imports. Verdict: the equal proof uses existing
   Mathlib APIs directly. No unused imports remain. The main case split uses
   both endpoint lemmas, and the redundant direct window import is reported.
   The assigned unit `sk-prop-av-pqf-finite` has empty realized entries; none is
   bypassed or changed. No chapter or unit route changes.
5. Compared all three nodes with their Lean statements and proofs. Verdict:
   the main node names exactly the two endpoint dependencies; new nodes carry
   exact signatures, sources, searches, creation records and complete proof
   descriptions. Existing node changes are limited to permitted stage-3 fields.

Changed during second reading: proved the equal case, placed it in its own
module, fixed the unused-argument warning, replaced the incorrect strict-case
explanation and incomplete proof records, refreshed actual search records,
and corrected the report's hole accounting and dependency-pruning description.
