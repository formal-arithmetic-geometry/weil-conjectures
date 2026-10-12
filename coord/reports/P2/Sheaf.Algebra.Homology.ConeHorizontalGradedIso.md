## What changed

Replaced the earlier `ConeHorizontalGradedIsoComponents` split, which simply
repackaged the entire complex isomorphism as compatible component isomorphisms.
That module and its proposed node are not delivered.

Added `Sheaf.Algebra.Homology.ConeHorizontalProjection` with actual constructions
`HomologicalComplex₂.horizontalTotalProjection`,
`HomologicalComplex₂.horizontalExtendedProjection`, and
`HomologicalComplex₂.coneHorizontalProjection`. These use `totalDesc`, extension
isomorphisms, the cone biproduct decomposition, and a source scalar `(-1)^p`.
No data is obtained from an unproved theorem.

Added `Sheaf.Algebra.Homology.ConeHorizontalQuotientIso` and
`Sheaf.Algebra.Homology.ConeHorizontalProjectionDifferential`, separating the
objectwise quotient calculation from the restricted projection's differential
calculation. The target combines them by epi cancellation and
`HomologicalComplex.Hom.isoOfComponents`. The quotient-composite equation
uniquely determines each component map, so the choice in the proof does not
select an arbitrary witness of existence.

The original target signature, docstring, visibility, and three public imports
are unchanged. The two added imports in its module are private proof imports.
New modules use public imports for the definitions appearing in their signatures
or exposed definition bodies. The parent DAG proof now records the actual route.

## Proved and sorry left

Hole closed: `HomologicalComplex₂.coneHorizontal_graded_iso`
(node `lem-sp-cone-horizontal-graded-iso`). Its module contains no `sorry`.

Holes added and left open:

- `HomologicalComplex₂.coneHorizontal_quotient_iso`
  (node `lem-sp-cone-horizontal-quotient-iso`): the unique degreewise quotient
  map induced by the explicit signed projection is invertible.
- `HomologicalComplex₂.coneHorizontal_projection_differential`
  (node `lem-sp-cone-horizontal-projection-differential`): the explicit signed
  projection restricted to the tail commutes with the differential.

This is a decomposition, not a completed proof: one upper hole is closed and
two strictly smaller holes are added, giving net -1 by the hole count.
Neither lower theorem asserts the target complex isomorphism. Both contain
complete natural-language proofs, sources, and matching nodes. No definition
contains a hole. The three new constructions have only `propext`,
`Classical.choice`, and `Quot.sound`; the two lower theorems and the target
also depend on `sorryAx`, exactly as expected.

## No longer needed

No existing import or reachable module is pruned. The old direct proof dependency
`lem-sp-cone-horizontal-step-stable` is replaced in the parent proof plan by the
two new calculation nodes; its module stays imported because the unchanged hF
hypothesis uses its explicit tail definition. The old dependency
`def-sp-filtered-complex-subquotients` remains used for the quotient projection
and its epimorphism instance.

The earlier proposed `ConeHorizontalGradedIsoComponents` module and
`lem-sp-cone-horizontal-graded-iso-components` node were removed from the sandbox;
they were never part of the repository baseline.

## Where the brief, the DAG or earlier work was wrong

The earlier worker's split was equivalent to the entire target: Mathlib's
`HomologicalComplex.Hom.isoOfComponents` assembles exactly its asserted data,
and a complex isomorphism supplies that data conversely. This is not a strict
part of the argument. Its short docstring also omitted the full proof, and the
parent DAG was not updated to refer to it.

The replacement follows the original plan's two mathematical steps, using an
explicit projection rather than an existential family of unspecified isomorphisms.
The Stacks source was checked at https://stacks.math.columbia.edu/tag/012X:
the first-filtration formula and Lemma 12.25.1(1) give the tail and vertical sign;
the column-cone refinement is the elementary block calculation described in the
original target node and the new docstrings.

Searches through msearch.py found Mathlib's `totalDesc`, total differential
inclusion formulas, shift differential formulas, and
`cokernelBiproductFromSubtypeIso`. These are tools for the calculations, rather
than statements identifying the specific image-supremum tails or proving the
restricted signed projection equation. LeanSearch returned Internal Server
Error, recorded as unavailable. Loogle, LeanFinder, Mathlib grep, and repository
rg searches found no duplicate of either lower theorem.

## New nodes

`def-sp-cone-horizontal-projection` records the explicit signed projection and
its two construction helpers, in `ConeHorizontalProjection`.

`lem-sp-cone-horizontal-quotient-iso` records the objectwise quotient assertion
and its complete biproduct/cokernel proof, in `ConeHorizontalQuotientIso`.

`lem-sp-cone-horizontal-projection-differential` records the independent
restricted-projection differential assertion and its generator/block proof,
in `ConeHorizontalProjectionDifferential`.

No interface-change record is needed: no existing declaration or public import
changes. The new nodes retain the parent's chapter and unit. The unit's realized
statement and steps are empty; none is bypassed or changed.

## Second reading by P2

1. Compared the delivered target module with the repository version by diff.
   Its existing declaration signature is byte for byte unchanged; no hypothesis,
   conclusion, definition, visibility, or original docstring changes. Verdict: pass.
2. Compiled all four delivered modules locally through lcompile.py in import
   order, without errors or warnings. A scratch module checked all six declarations
   with #print axioms: the three explicit definitions have only the permitted
   axioms; the target and the two listed open assertions additionally use sorryAx.
   Only the two named public theorem proofs contain sorry. No forbidden axiom,
   unsafe, opaque, implemented_by, extern, or hollow definition occurs. Verdict: pass
   for a decomposition, not for a completed proof.
3. Rejected the original split as a restatement and replaced it with two strictly
   separate assertions about a constructed map. Checked p=0, odd/even p, n=p-1,
   n<p-1, the zero bicomplex, and a bicomplex supported in just one column:
   the source survives at n=p-1, negative vertical degrees vanish, horizontal
   terms are killed on the p-tail, and (-1)^p squared is one. Scratch compilation
   verifies the extended projection is zero below p, retains the selected diagonal
   summand, and the quotient-composite equation determines a map uniquely by epi
   cancellation. Repeated searches with different queries as recorded above;
   lower statements have full proof docstrings and nodes. Verdict: pass.
4. The target now makes a real reduction by explicit quotient-composite equations,
   the restricted differential equation, naturality, and epi cancellation. Mathlib
   supplies the final component-isomorphism assembly. Public imports in the target
   are needed for its unchanged statement; new proof imports are private. Nothing
   realized in dag/units/sk-prop-av-pqf-finite.json is bypassed. No reachable module
   is claimed pruned; unused old proof dependency is explained above. Verdict: pass.
5. Updated the parent node's proof, proof_deps, and proof_origin to the compiled
   proof. Added three complete nodes, with the actual Lean signatures, source,
   search records, creation fields, chapter/unit, and proof dependency unions.
   Existing statement and stmt_deps are preserved. Verdict: pass.

Second reading changed: removed the equivalent component-data restatement;
constructed the signed projection without holes; split quotient invertibility
from differential compatibility; wrote the actual target reduction; corrected
DAG dependencies and hole accounting. Two lower calculations remain open.
