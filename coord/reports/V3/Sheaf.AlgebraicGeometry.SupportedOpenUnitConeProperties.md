## What changed

Proved `AlgebraicGeometry.supported_open_unit_cone_properties` with its existing
signature byte for byte unchanged. The proof obtains the second vertex's supported
quasi-coherent property, applies the existing `supported_qcoh_isTriangulated`, and
transports the resulting cone property along an isomorphism. Exact restriction maps
the triangle to a distinguished triangle; invertibility of its first arrow implies
its third vertex is zero by Mathlib's `Triangle.isZero₃_of_isIso₁`.

Added `SupportedOpenUnitImageProperties.lean` for the second-vertex interface, and
`DerivedOpenUnitRestrictionIso.lean` for the restricted-unit theorem. The latter is
proved by localizing the exact extension-by-zero adjunction, deriving the existing
extension/restriction composition isomorphism, and applying Mathlib's adjoint-triple
full-faithfulness equivalence. All additional imports are plain proof imports;
the original public imports and all existing declarations and definitions are unchanged.

Removed the first worker's two undelivered component modules and nodes. They split
conclusions about C instead of isolating the earlier facts used by the argument.
No changes outside the sandbox, and no forced adaptations or interface change records.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.supported_open_unit_cone_properties`
(node `lem-pc-supported-open-unit-cone-properties`), one of one original holes.

New theorem proved: `AlgebraicGeometry.derived_open_unit_restriction_isIso`
(node `lem-pc-derived-open-unit-restriction-iso`); this module contains no sorry.

New hole added: `AlgebraicGeometry.supported_open_unit_image_properties`
(node `lem-pc-supported-open-unit-image-properties`). Its proof is exactly `by sorry`,
with source and a complete mathematical proof in its docstring. It asserts properties
of R(L(K)), has no C, g, h, or triangle, and does not restate a cone conclusion.

The earlier proposed holes `supported_open_unit_cone_qcoh` and
`supported_open_unit_cone_support` are removed, not counted as closed library holes.
Relative to the repository this is a decomposition: one original hole closed, one
new hole added, net zero. The target still depends on the remaining image theorem;
it is not claimed axiom-free. No hole is introduced into a definition.

## No longer needed

Removed the item's direct proof imports `OpenRestrictionSupportTriangle`,
`DerivedDirectImageOpenRestriction`, and `SupportedDerivedRestrictionZero`.
The last two remain imported by the image interface, where their arguments belong.
The canonical `OpenRestrictionSupportTriangle` module is not imported anywhere in
this delivery. No claim is made that it becomes globally unreachable.

All four old direct proof dependencies are replaced in the item's DAG proof:
`lem-sc-open-restriction-support-triangle`, `lem-sf-triangle-morphism-iso`,
`lem-pc-restrict-derived-direct-image-open`, and
`lem-pc-supported-derived-restriction-zero`. The first two are unnecessary for the
new reduction. The last two are retained as proof dependencies of the image lemma.
The new direct dependencies are the image lemma, the restricted-unit lemma, and
`lem-pc-supported-qcoh-triangulated`. Both old undelivered component interfaces are
also unnecessary and removed. The unit record is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes depended on the very item they were supposed to prove,
creating circular proof plans, and their sorry docstrings had no proof in words.
The existing item node was not updated to match its conjunction proof. The report
also called that composition proved without explaining the increase from one hole
to two. The original DAG cone-comparison route can be shortened: the existing
supported triangulated-closure theorem handles both cone properties, and exact
restriction plus the adjoint triple handles vanishing. No mathematical error in the
original theorem or in the unit is asserted.

## New nodes

`lem-pc-supported-open-unit-image-properties` is stated in
`lean/Sheaf/AlgebraicGeometry/SupportedOpenUnitImageProperties.lean`. It isolates
quasi-coherence and closed support of the second vertex, independently of any triangle.
It uses open restriction quasi-coherence, qcqs derived direct image, supported
restriction vanishing, and open base change; it does not cite the cone theorem.

`lem-pc-derived-open-unit-restriction-iso` is stated and proved in
`lean/Sheaf/AlgebraicGeometry/DerivedOpenUnitRestrictionIso.lean`. It applies to every
complex on every scheme and open, without compactness or support assumptions.
Its DAG records exact extension by zero and its restriction composition isomorphism.
The proof uses these existing declarations, not a new derived direct-image hole.

Sources were read locally in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`:
`perfect.tex`, lemma-quasi-coherence-direct-image (08D5) and
lemma-orthogonal-koszul-complex (09IR); `cohomology.tex`,
lemma-restrict-K-injective-to-open (08BS) and lemma-restrict-direct-image-open (08FE).
Independent LeanFinder, Loogle, and Mathlib source searches were run with msearch.py
and recorded in searches.jsonl. The underived restriction counit and generic
adjoint-triple facts found there are used; they do not directly assert the new
statements. Existing affine `derived_open_unit_cone_properties` requires an affine
scheme and concerns C; supported_open_pushforward requires T contained in U and has
a different canonical direct-image interface. Neither supplies the remaining lemma.

## Second reading by V3

1. Compared every delivered existing module against the read-only repository version.
   The original theorem signature is byte-identical, and its public imports,
   definitions, and visibility are unchanged. Only its proof and plain proof imports
   change. The other two modules are new declarations with new nodes. Verdict: pass.
2. Compiled all three delivered modules locally through lcompile.py, in import order,
   without errors or warnings. Scanned for forbidden declarations and escapes: none.
   Only the named image theorem has a source-level sorry; no definition has one.
   Scratch-copy #print axioms on each of the three public theorems showed only
   propext, Classical.choice, Quot.sound, and sorryAx. The restricted-unit theorem
   contains no local hole but also inherits sorryAx from upstream dependencies.
   No theorem is misreported as axiom-free. Verdict: pass as a decomposition.
3. Read the remaining image statement independently, its source, its full docstring
   proof, and the declarations in its planned dependencies. Checked empty U, empty
   T, T = X, U = X, zero K, and unbounded K. Closedness of T supplies the open
   complement; compact U and quasi-separated X supply a qcqs open immersion.
   Right-adjoint uniqueness allows arbitrary supplied R. Searches by restriction
   counit, adjoint triple, supported direct image, and triangulated closure found
   reusable facts but no exact image theorem. The new hole concerns the second
   vertex, with no cone or triangle assumptions or conclusions. Verdict: pass.
4. Shortened the route using the existing supported triangulated-closure theorem
   and Mathlib's zero-cone criterion, and proved the restricted-unit assertion via
   the exact extension/restriction adjoint triple. Reviewed all imports against
   signatures, the actual proof, or the remaining hole's named proof dependencies.
   No longer needed lists all four replaced old direct proof dependencies, including
   the two now delegated to the image theorem. The unit realized record is unchanged;
   this item is below the unit level and realizes no unit statement or step.
   Verdict: pass; one-to-one decomposition, not net hole reduction.
5. Read and updated the original node and both new nodes together with the Lean.
   The original proof steps now record the actual triangle-closure and vanishing
   reduction; the new nodes have self-contained statements, exact Lean signatures,
   source, written proof steps, search results, provenance, and created records.
   proof_deps is the union of step uses throughout; no new node depends on the item.
   Verdict: pass.

Second reading changed: replaced the circular component split with second-vertex
and restricted-unit interfaces, proved the latter using existing extension by zero,
rewrote the target proof using supported triangulated closure and exact restriction,
removed the canonical triangle import, supplied full proof docstrings and corrected
DAG records, and corrected the report's hole and pruning accounting.

The first preflight requested the distinct LeanSearch entry required by the node
schema. LeanSearch was run and returned Internal Server Error; this is recorded
as unavailable, with no no-match verdict. LeanFinder, Loogle and grep supplied the
independent search results used above.
