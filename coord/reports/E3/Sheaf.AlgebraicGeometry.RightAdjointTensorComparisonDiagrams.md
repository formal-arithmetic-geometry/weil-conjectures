## What changed

Decomposed `AlgebraicGeometry.rightAdjointTensorComparison_diagrams` into its
shift-square and distinguished-triangle conjuncts. The original signature is
byte for byte unchanged. Its proof uses conjunction introduction and the two
new theorems. The new modules are imported privately, for this proof only.
No definition, existing public import, or other existing declaration changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.rightAdjointTensorComparison_diagrams`, node
`lem-sc-right-adjoint-tensor-comparison-diagrams`.

Holes added and left:

- `AlgebraicGeometry.rightAdjointTensorComparison_shift`, node
  `lem-sc-right-adjoint-tensor-comparison-shift`.
- `AlgebraicGeometry.rightAdjointTensorComparison_triangle`, node
  `lem-sc-right-adjoint-tensor-comparison-triangle`.

This is a decomposition, not a completed proof or a net hole reduction:
one parent hole closed, two smaller holes added, net minus one. Each new
statement is one proper conjunct of the original conclusion with unchanged
hypotheses. Neither claims invertibility of the comparison. Axiom checks for
all three declarations show only `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`. The parent still depends on the two open obligations and on
unproved facts of the imported library.

## No longer needed

No module or import is pruned. The parent's old direct proof dependencies
`def-pc-derived-direct-image`, `def-pc-derived-pullback`,
`def-pc-scheme-derived-tensor-structure`, and
`lem-sc-right-adjoint-tensor-comparison-natural` are replaced by the shift
and triangle nodes. All four remain dependencies of the split proof plans;
the first three also provide definitions in the unchanged signatures.
No claim is made that they leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes cited the parent as a proof dependency, creating
a circular plan, used placeholders for their mathematical and Lean statements,
and recorded no searches. Their docstrings had no complete proof explanation;
their files also had overlong lines, empty lines inside declarations, and
placeholder copyright headers. The parent node had not been updated to match
its proof. All these faults were repaired in the sandbox.

The geometric shift compatibility of the pinned mate, and the exact structures
needed for the triangle construction, are still genuine proof obligations.
Mathlib's `NatTrans.CommShift` describes compatibility rather than proving it
for this transformation. `Adjunction.isTriangulated_rightAdjoint` assumes the
appropriate exact and shift structures. Upstream derived tensor exactness is
available in `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`,
but does not establish the comparison's mate compatibility. No short direct
closure was found. LeanSearch was unavailable; LeanFinder, Loogle and local
grep were inspected. The source was checked at
https://stacks.math.columbia.edu/tag/0A9U: the comparison diagrams expand the
triangulated-subcategory argument, not the perfect-morphism isomorphism claim.

## New nodes

`lem-sc-right-adjoint-tensor-comparison-shift` records just the shift-square
conclusion. Its statement is self-contained, its Lean signature is recorded
verbatim, and its proof describes exact source and target shift comparisons,
the pinned mate computation, and transport along B.obj ≅ A.obj[n].

`lem-sc-right-adjoint-tensor-comparison-triangle` records just the triangle
conclusion. Its statement is self-contained, its Lean signature is recorded
verbatim, and its proof describes the same coherent exact comparisons and
transport of a distinguished triangle and its comparison morphism. The
existential shift-square statement alone is not treated as a black box giving
coherent comparisons: this proof explicitly constructs those comparisons.
Neither node uses the parent theorem. No change record is required.

## Second reading by E3

1. Compared the delivered parent with the repository using `diff` and checked
   the signature substring byte for byte. Pass: only two proof-only imports
   and the proof body changed. No existing statement or definition changed.
2. Compiled the three modules locally. Fixed the new modules' style warnings.
   Exactly two whole-proof named public theorem sorries remain; no definitions
   or forbidden implementation mechanisms were added. Scratch `#print axioms`
   checks of all three declarations show only the three standard axioms and
   `sorryAx`. Pass as a decomposition, not as an axiom-free proof.
3. Read both split signatures against the two original conjuncts. Checked
   zero objects, n = 0, negative shifts, arbitrary vertex isomorphisms, zero
   triangles, and noninvertible components: the exact-functor and mate argument
   requires no extra hypothesis in these cases. Each conclusion is strictly
   part of the parent. Expanded each docstring into a proof in words and ran
   LeanFinder, Loogle, LeanSearch and grep with new queries; no duplicate theorem
   found in Mathlib, upstream or lean/Sheaf. Pass with the two stated holes.
4. Read the imported definitions and inspected upstream tensor exactness and
   Mathlib's triangulated adjunction and shift APIs. They do not by themselves
   prove the pinned comparison compatibility. Existing imports provide types
   used by the signatures; added imports are proof-only. Listed every replaced
   old proof dependency above. The unit sk-thm-picard-duality has empty realized
   entries; no unit statement, realization or route is changed. Pass.
5. Repaired the parent proof plan and proof_deps to the two applied nodes.
   Repaired the new nodes' circular dependencies, self-contained statements,
   verbatim Lean signatures, proof plans and search records. Each proof_deps
   equals the union of its proof steps' uses. Sources and proof_origin identify
   the expanded Stacks comparison argument. Pass.

Second reading changed metadata, proof documentation, new-file headers and
style only. The existing signature and the conjunction proof remain unchanged.
