## What changed

The existing declaration `AlgebraicGeometry.selfExt_tor_resolution_local` keeps its
signature byte for byte. Its proof now establishes K-injectivity of the local
restriction from `openImmersion_restriction_derived_properties` and
`isKInjective_restrict_localized`, proving the zero-morphism preservation parameter
sectionwise. The finite-free zero-model conjunct is supplied by the strictly smaller
tensor-only statement `AlgebraicGeometry.local_tensor_has_finite_free_zero_model`,
now in the new module `Sheaf.AlgebraicGeometry.LocalTensorFiniteFreeZeroModel`.
No definition or existing public import changed. New proof imports are ordinary
`import`, and the new module publicly imports only its signature dependencies.

## Proved and sorry left

Closed the old hole in `AlgebraicGeometry.selfExt_tor_resolution_local`
(node `new-j3-self-ext-tor-local`) by combining a proved restriction branch with a
tensor-only component. Added one hole:
`AlgebraicGeometry.local_tensor_has_finite_free_zero_model`
(node `split-local-tensor-finite-free`). Its source and complete mathematical proof
are in its docstring. This is a decomposition: one old hole closed, one new hole
added, net zero; the target is not axiom-free. The actual restriction branch adds
no hole. No sorry remains in the item's module.

The predecessor's `local_restrict_kinjective` hole and its proposed node
`split-local-restrict-kinjective` were removed before delivery. They were never
library declarations and are not counted as baseline holes closed.

## No longer needed

Removed direct imports of `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`,
`Sheaf.RingTheory.KoszulProjectiveResolution`, and
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen` from the item's module.
The first two now belong to the tensor component's planned proof and remain imported
there; their nodes `lem-sc-affine-quotient-resolution-sheafification` and
`new-j3-koszul-projective-resolution` move from the item's direct `proof_deps` to
that component's `proof_deps`. The item's old direct dependency
`lem-sc-derived-k-injective-restrict-open` is replaced by the existing open-immersion
and localized-site preservation declarations. It remains a transitive dependency
of the open-immersion result. No old dependency module is globally pruned by this
delivery. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The predecessor split a restriction assertion already obtainable from existing
library declarations, left both split docstrings without complete proof arguments,
recorded new nodes with empty statement dependencies and unrealistically terse
proofs, and did not update the item's DAG proof. Its report called the target
compiling without explaining that two new holes replaced one old hole.
The second reading repairs these points. The published Stacks tags were checked:
0BQY gives the quotient Koszul computation, 068C supplies the finite-free Koszul
resolution argument, and 08BS gives K-injectivity of open restriction. The
scheme-local tensor comparison is the derived-resolution comparison explained in
the new docstring, not a verbatim theorem in those sources.

## New nodes

`split-local-tensor-finite-free` isolates only the finite-free zero-model conjunct:
there is no J, b, resolution of J, or K-injectivity conclusion. It includes the
same K-flat resolution and termwise flatness assumptions on P and the same regular
affine chart hypothesis as the original theorem. Its node now gives a self-contained
statement, signature verbatim, proof steps, source, actual searches with different
queries, and the existing Koszul/sheafification dependencies. No change record is
needed because no existing statement or definition was altered.

## Second reading by J4

1. Compared the delivered module with the repository using `diff`; separately
   checked byte equality of the full existing theorem signature. The existing
   declaration, docstring, definitions, and public imports are unchanged. Verdict:
   no accidental interface change.
2. Compiled both delivered modules in import order with `lcompile.py`. The item's
   theorem contains no sorry, the new module has exactly its named theorem's sorry,
   and there are no axioms, unsafe/opaque declarations, foreign implementations,
   or definitions with sorry. Checked `#print axioms` on scratch copies. Verdict:
   kernel-checked reduction, with allowed upstream/new `sorryAx` dependencies;
   not a fully proved target.
3. Read the split statement against the original tensor conjunct, K-flatness and
   tensor pullback definitions, and the finite-free model definition. Checked the
   empty sequence (degree zero rank one), zero quotient, empty chart, and arbitrary
   V cases; no nonempty/proper-ideal assumption is needed. It is strictly one part
   of the original conjunction and carries no K-injectivity conclusion. Searched
   with LeanSearch (service unavailable, not evidence of absence), leanfinder,
   loogle, and grep under concept queries different from the first
   worker's proposed names, and searched the repository's tensor/Koszul APIs.
   No existing scheme-local zero-model declaration was found. Verdict: a true,
   needed, strictly smaller component, with its formal proof still open.
4. Took the shorter restriction route through the existing open-immersion and
   localized-site results, removed the duplicate split and unused direct proof
   imports, and documented every old proof dependency's disposition above. Read
   `dag/units/sk-thm-picard-duality.json`: this helper is below the unit's realization
   boundary, and no recorded unit realization or step is bypassed or changed.
   Verdict: route preserved; no claim of global pruning or net hole reduction.
5. Updated the existing node's proof/proof_deps/proof_origin to the Lean proof,
   and rebuilt the surviving new node's statement, metadata, search evidence,
   source and proof plan. Checked its signature against the new module. Verdict:
   DAG and Lean agree.

Changes made by this second reader: closed and inlined the restriction branch;
removed its duplicate helper/node; moved the remaining tensor statement into its
own module; supplied its source and full mathematical proof docstring; repaired
both DAG records, imports, searches, and the progress report.
