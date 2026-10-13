## What changed
Replaced the body of `HomologicalComplex₂.finiteStripGradedMap_isIso` with the
abelian-category implication from mono and epi, using Mathlib
`CategoryTheory.isIso_of_mono_of_epi`. Added proof-only imports of
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi` and
`Sheaf.Algebra.Homology.FiniteStripConeGradedMapMono`, which state the two
strictly weaker cancellation properties. Existing signatures and definitions
are unchanged. The target node now records these two proof dependencies.

## Proved and sorry left
Closed the local hole in `HomologicalComplex₂.finiteStripGradedMap_isIso` (one of
one original holes). Added two named open theorems:
`HomologicalComplex₂.finiteStripGradedMap_epi`
(node `lem-sc-finite-strip-cone-graded-map-epi`) and
`HomologicalComplex₂.finiteStripGradedMap_mono`
(node `lem-sc-finite-strip-cone-graded-map-mono`). Each has exactly `by sorry` as
its proof. This is a decomposition, not a completed mathematical proof: one
hole closed, two added, local net -1. The upper theorem still depends on
`sorryAx` through those two halves. No lower hole was closed by the second reader.

## No longer needed
No modules or imports were removed or pruned. The original direct proof edge
`def-sc-finite-strip-cone-graded-map` is replaced at the upper node by the mono
and epi nodes; it remains a statement dependency and is used by both new nodes,
so its module remains necessary in the import closure.

## Where the brief, the DAG or earlier work was wrong
The first submission described the decomposition as a proof without accounting
for its two new holes. Its mono docstring incorrectly said epic and repeated the
epi explanation, its new node Lean statements were placeholders rather than
verbatim signatures, and the upper node did not record the new reduction.
These issues were repaired. There is no statement or definition change.

## New nodes
`lem-sc-finite-strip-cone-graded-map-epi`: right-cancellation follows by testing
on the current tail's source and diagonal generators; all non-surviving
generators factor through the next tail. It is strictly weaker than invertibility.

`lem-sc-finite-strip-cone-graded-map-mono`: left-cancellation follows by projecting
to the surviving row, descending this projection through the quotient, and
checking that it is a left inverse. It is strictly weaker than invertibility.
Both nodes include self-contained statements, exact Lean signatures, source,
complete informal arguments and new searches. No change record is required.

## Second reading by R4
1. Compared the target module against the repository version with `diff` and
checked its complete declaration signature: byte-for-byte unchanged. Only its
proof and two plain proof-only imports change. The other two modules are new.
No definition or public import in an existing module changed. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`, without
errors or warnings after replacing the two `letI` bindings with `have`.
Inspected every delivered file: precisely the two listed named theorem holes,
no forbidden declaration forms and no holed definitions. A scratch copy with
`#print axioms` for all three declarations returned only `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`. Verdict: valid conditional
reduction, still open below.
3. Read the actual row inclusion and graded-map construction. The source single
object survives exactly when n=p-1; a target summand survives exactly when its
vertical index is p. At r=0, at horizontal indices outside the strip, and at
degrees off the source single, the corresponding summands are zero. The mono
argument uses only a left inverse; the epi argument uses only cancellation on
the generators of the quotient. Neither adds an augmentation or differential
hypothesis. Both are true and strictly weaker parts of the original argument.
Repeated searches with different words through `msearch.py` (leanfinder,
qualified loogle and grep; LeanSearch was also attempted but returned an
Internal Server Error, recorded without a verdict) and searched project homology modules with `rg`.
Generic biproduct cokernel isomorphisms require the tail identifications still
missing here; module-specific projection results do not cover arbitrary abelian
C. Found no duplicate or direct shortcut. Verdict: acceptable decomposition.
4. The shortest final categorical step is Mathlib's mono/epi criterion. Both
proof imports are used; the public graded-map import is needed by the statement.
The diagonal quotient construction remains the route, and no unit-level step
is bypassed. Read `dag/units/sk-thm-picard-duality.json`; its `realized` entries
are empty and are unchanged. No old dependency module is pruned. Verdict: pass.
5. Checked the new node fields and exact Lean signatures, repaired their proof
texts and origins, and added the upper node with proof/proof_deps/proof_origin
matching the written categorical reduction. The new node statements are
self-contained and cite the map definition. Verdict: pass.

Second reading changed: corrected and expanded both new docstring proofs and
blueprint IDs, completed both new node signatures and statements, replaced
copied searches with fresh results, updated the upper node's proof route,
removed two linter warnings, and corrected the report's hole accounting.
