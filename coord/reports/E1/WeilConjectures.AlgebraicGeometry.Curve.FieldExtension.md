## What changed

Replaced the algebraically closed theorem's sorry by the existing
`IsCurve.bijective_cohomologyMap_of_forall_isReduced` reduction and one smaller
split theorem, `IsCurve.algebraicallyClosedCohomologyInvariant`, for reduced proper
curves and constructible prime-field coefficients. Both new proof imports are plain
`import`. The original signatures, definitions, docstrings and public imports are preserved.
The duplicate separably closed passage split module and its node were removed from
this sandbox; the original named passage theorem remains open.

## Proved and sorry left

Two of the three item declarations have proof bodies without sorry:
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` (newly closed locally)
and `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed` (already assembled).
These are conditional proofs resting on sorry-bearing dependencies, not axiom-free results.
The original `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`
still has its named sorry, with its existing node
`lemma-weil-pbc-curve-separably-closed-passage` and unchanged proof docstring.
The one new sorry is `AlgebraicGeometry.IsCurve.algebraicallyClosedCohomologyInvariant`,
node `e1-algebraically-closed-cohomology-invariant`. It now assumes reducedness and
constructible prime-field coefficients; it is exactly the hypothesis of the existing reduction.
The imported reduction itself remains an open theorem in the library.

## No longer needed

No library module or unit route is globally pruned. The discarded
`Sheaf.AlgebraicGeometry.Curve.SeparablyClosedPassageInvariant` was only an undelivered
duplicate, and its proof import is removed. The original public imports are retained as
existing API exports; no added proof-only import is public.
The original algebraically closed node now directly uses only
`lem-weil-pbc-curve-constructible-reduction` and the new reduced prime-coefficient node.
Every old direct proof dependency other than the existing reduction is listed below.
These dependencies move into the smaller core or the existing reduction; this list does
not claim they are globally unnecessary:

- `lem-weil-pbc-torsion-sheaf-characterizations`
- `def-weil-pbc-curve-setting`
- `def-weil-pbc-extension-pullback`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-C7`
- `def-weil-pbc-eight-curve-assertions`
- `lem-weil-pbc-zero-dimensional-cohomology`
- `lem-weil-pbc-zero-dimensional-field-extension`
- `def-sbc-smooth-morphisms`
- `def-sc-curves`
- `def-weil-pbc-extension-by-zero`
- `lemma-weil-pbc-eight-curve-devissage`
- `lem-weil-pbc-curve-assertions-finite-pushforward`
- `thm-sc-main`
- `def-sc-constant-sheaves`
- `def-weil-pbc-constructible-torsion`
- `lem-weil-pbc-curve-assertions-dense-open`
- `lem-weil-pbc-reduced-curve-normalization`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-finite-pushforward-constructible-noetherian`
- `lemma-weil-pbc-curve-locally-constant-reduction`
- `def-weil-pbc-primary-torsion`
- `lem-weil-pbc-curve-assertions-retract`
- `thm-pqf-zmt-factorization`
- `lemma-weil-pbc-finite-pushforward-extension-zero`
- `def-weil-pbc-finite-open-comparison`
- `lem-weil-pbc-curve-dense-open-localization`
- `lem-weil-pbc-constructible-torsion-modules-agree`

## Where the brief, the DAG or earlier work was wrong

The first worker's two split statements were restatements of the item's open theorems.
Moving their sorries to new modules did not advance the proof. Their node records also
lacked chapter, unit and recorded searches; their lean.statement fields were prose rather
than verbatim signatures, and proof_deps did not match the steps' uses. The original
item node was not updated to describe the new proof. The second reading repaired these
faults rather than delivering the relocation as progress. Neither remaining proof core
was closed outright in this review.

## New nodes

`e1-algebraically-closed-cohomology-invariant` is the reduced constructible prime-coefficient
case after the first two paragraphs of Stacks 03SC. Its remaining route is normalization,
finite locally constant reduction with trace, finite pushforward, extension by zero,
and dense-open localization. The proof steps come from the original ten-step node,
restricted to the remaining case; its docstring spells out the argument. No existing
statement or definition changed, so no statement change record is required.

## Earlier second reading (a previous round; superseded)

1. Compared the item module with the repository using diff and declaration parsing.
   All three existing theorem signatures are byte for byte unchanged up to the body
   delimiter; no hypothesis, conclusion, definition, existing docstring or attribute changed.
2. Compiled both delivered files locally in import order. No errors, non-sorry warnings,
   forbidden declarations or hollow definitions. A scratch axiom check of all three item
   declarations and the new split theorem shows only propext, Classical.choice,
   Quot.sound and sorryAx; the report identifies the open statements.
3. Rejected both restatement splits. The retained split is now precisely the reduced
   constructible prime-coefficient hypothesis of the existing reduction. Checked empty
   curves, dimension-zero curves, zero sheaves, degree zero, and r equal to the characteristic:
   no exclusion or invertibility assumption is needed. Checked Stacks 03SC, 03SD and 0A3Q,
   searched Mathlib with LeanFinder, Loogle and grep (LeanSearch was unavailable), and
   searched the upstream and Sheaf curve modules. No duplicate exact statement was found.
4. The proof starts at the item theorem and applies the existing constructible/reduced
   reduction. Both added imports are proof-only. The new module imports declarations
   needed by its signature. Original public exports are preserved. The complete old direct
   dependency accounting is above. `dag/units/sk-thm-p1.json` realizes both the algebraically
   closed and separably closed nodes in its curve-calculation step; these stay on the route.
5. Updated the original algebraically closed node's proof, proof_deps, proof_origin and
   lean note to match the new proof; its sorry_free flag remains false because
   the axiom check still contains sorryAx. Rebuilt the new node with a verbatim Lean signature,
   source, complete proof steps, exact union of uses, chapter, unit, creation record and
   genuine search records. Other existing node statements and records are unchanged.

Changes by the second reader: replaced the two duplicate splits by one smaller reduced
prime-coefficient obligation; restored the original passage sorry; applied the existing
reduction; repaired imports, documentation, node metadata, dependency accounting and this report.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. Existing declaration
signatures, definitions, docstrings and public imports are unchanged; only proof-only imports
and the algebraically closed proof body were added. The new split module has a distinct,
strictly smaller reduced constructible prime-coefficient statement.

2. Compiled both modules in import order with `lcompile.py --all`; compilation succeeds. The
only new `sorry` is the named split theorem
`AlgebraicGeometry.IsCurve.algebraicallyClosedCohomologyInvariant`, recorded by node
`e1-algebraically-closed-cohomology-invariant`; no forbidden declarations or hollow definitions
were introduced. The item also retains
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`,
with its named sorry and node `lemma-weil-pbc-curve-separably-closed-passage`.

3. Checked the split statement against the reduction's exact hypotheses and edge cases
(empty and zero-dimensional curves, zero sheaf, and all prime characteristics). Searched
Mathlib and the project for duplicates; none was found. The statement is true and no stronger
than the reduction requires.

4. The item proof applies the existing reduced/constructible reduction and then the new split
core. Added imports are plain proof-only imports; original public exports remain. The updated
item node's proof, dependencies and origin match this route, and the unit route remains intact.

5. The new node has complete source, proof steps, dependency union, search records, chapter,
unit, creation and verbatim Lean declaration metadata. No statement or definition change record
is needed.

Changed in this reading: added this required review record and corrected the delivered DAG and
report metadata; no Lean proof changes were necessary.

## Second reading by E1

1. Compared the delivered item module with the repository version. Existing theorem signatures, definitions, docstrings, and public imports are unchanged; only two proof-only imports and the algebraically closed proof body differ. The new module is an additional declaration.

2. Compiled both modules with `lcompile.py --all`; compilation succeeds without errors. The only remaining item sorry is the named separably closed passage theorem, and the only new sorry is `algebraicallyClosedCohomologyInvariant`; both are documented and have DAG nodes. No forbidden declarations or hollow definitions were introduced.

3. Checked the new split statement against the reduction's exact reduced, constructible prime-coefficient hypotheses and edge cases (empty and zero-dimensional curves, zero sheaf, and all prime characteristics). Searched Mathlib and the project for duplicate results; none was found. The statement is true and strictly smaller than the item theorem.

4. The item proof applies the existing reduction and the new split core. Added imports are plain proof-only imports, while the original public exports remain. The item node's proof, dependencies, and origin match the Lean route; the unit route remains intact.

5. The new node has a verbatim Lean signature, source, complete proof steps, exact dependency union, chapter, unit, creation record, and search records. No statement or definition changed, so no change record is required.

I repaired the report metadata by adding this complete second-reading section; no Lean proof changes were needed.
