## What changed

Replaced the original hole in `CategoryTheory.Functor.rightDerivedFunctorPlusUnit_single_degree`
by a real reduction. The new, proved module
`Sheaf.CategoryTheory.SupportedComplexSingleRealization` constructs a complex morphism
representing the normalized derived morphism and proves its coefficient identity.
The new module `Sheaf.CategoryTheory.RightDerivedCanonicalSingleUnit` isolates only the
unit calculation on the literal single complex. The parent uses unit naturality,
quotient homology naturality, homology projection naturality, and the supplied cycle
inclusion equation to transport that calculation.

Removed the first worker's auxiliary module and node from the sandbox: its Lean
statement was exactly the parent statement, despite its node describing cancellation
of the final comparison. Existing statements and definitions are unchanged. Both new
modules are imported privately by the parent; no change record is needed. Unchanged
snapshots of RightDerivedSingleDegreeComparison and RightDerivedSingleUnitHomologyComparison
were removed from the delivery set.

## Proved and sorry left

Closed the original hole by name:
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit_single_degree`
(node `lem-pc-right-derived-unit-single-degree`). Its proof still depends on the new
hole below, so this is a decomposition, not a completed proof of the mathematical item.

Also proved `DerivedCategory.Plus.supported_complex_single_realization`
(node `lem-pc-supported-complex-single-realization`) without any `sorry` dependency.
Its printed axioms are exactly propext, Classical.choice, and Quot.sound.

Added exactly one hole:
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit_canonical_single`
(node `lem-pc-right-derived-canonical-single-unit`). This named public theorem has
its source and complete natural-language proof in its docstring; its entire proof
is `by sorry`. Its printed axioms, and those of the parent, contain only the three
standard axioms and sorryAx. No hole occurs in any definition.

Accounting: one old hole closed, one new hole added; net zero. The rejected
`rightDerivedFunctorPlusUnit_single_degree_aux` is not delivered.

## No longer needed

Removed the parent's direct proof imports
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`.
Both remain in the import closure through the two new modules and the comparison
module. No library module is claimed pruned.

The three old direct proof dependencies
`def-pc-right-derived-single-degree-comparison`,
`lem-sbc-right-derived-single-unit-homology-comparison`, and
`lem-sp-derived-functor-single-identification` now belong to the canonical-single
calculation's proof plan. All remain needed transitively. The parent's direct
proof_deps are the realization theorem and the canonical-single calculation.

## Where the brief, the DAG or earlier work was wrong

The first worker's report described a calculation before final cancellation, but
its auxiliary copied the original hypotheses and conclusion in full. The parent
was only `dsimp; exact` of that new hole. This was a restatement, not progress.
The auxiliary's blueprint tag was the parent's tag; its node lacked the required
creation, search, statement-dependency, proof-step, and complete Lean metadata.
The report also incorrectly said the parent still contained `sorry`.

The original plan is mathematically sound. The supported-complex realization can
be proved with existing constructions and pure-degree homology faithfulness; the
remaining literal-single calculation requires shift compatibility with the existing
comparison. LeanSearch returned HTTP 500 for both new statements; Loogle,
LeanFinder, and Mathlib/library source searches were performed and recorded.
The local blueprint source tree is absent on this machine; the full unit statement,
steps, and realization fields were read from dag/units/sk-thm-picard-rr.json.
The cited Stacks Tag 015J was read at its official URL. The explicit normalization
is an agent-written elaboration using the library comparisons, not a verbatim
statement of that tag.

## New nodes

`lem-pc-supported-complex-single-realization`: a proved realization lemma with no
coefficient functor, left-exactness, or Grothendieck hypothesis. It constructs its
witness explicitly with mkHomToSingle. No data definition chooses an arbitrary
witness from an unproved existence theorem.

`lem-pc-right-derived-canonical-single-unit`: the remaining calculation for a
literal single complex, with canonical e and sole coefficient X. It has no arbitrary
supported L, normalized f, or lift a, and is strictly a part of the original argument.
It keeps the original shift-to-zero and classical degree-zero unit comparison route.

## Second reading by G2

1. Compared every delivered existing module against the repository. The parent
signature is byte-for-byte identical, including all hypotheses and let-bindings.
No existing definition changed. The other two delivered modules are new.

2. All three modules compile in import order through lcompile.py without errors or
warnings. Checked forbidden declarations and holes. Printed axioms for all three
theorems: the realization has only the three standard axioms; the parent and
canonical-single theorem additionally have sorryAx from the one reported hole.

3. Rejected the identical auxiliary, repaired the split, and closed the realization
lemma. Reviewed n=0, n>0 (including the incoming degree -1 when n=0), zero coefficient,
zero complex, identity functor, and exact-functor cases. Neither new statement adds
a hypothesis to the parent. The remaining lemma is the literal-single shift
calculation. Three kinds of search were recorded for each new node; existing
constructors, comparisons, and homology faithfulness are reused, not restated.

4. The parent now proves the transport from the top down; the literal-single
calculation follows the original shift-to-zero plan. Imports used only in proofs
are private. Every old direct proof dependency is accounted for above and remains
needed transitively. The unit's realization fields and its route are unchanged;
no unit is bypassed and no module is claimed pruned.

5. Updated the parent node's proof, proof_deps, and proof_origin to the actual
reduction. Both new nodes have complete statements, source, stepwise proofs,
matching dependency unions, provenance, recorded searches, creation/blueprint
metadata, chapter/unit, and verbatim Lean signatures. No statement field of an
existing node changed.

Second reading changed: removed the restated auxiliary, proved the concrete-map
realization, wrote the naturality reduction, isolated the literal-single shift hole,
repaired the nodes and accounting, and minimized the delivery imports.
