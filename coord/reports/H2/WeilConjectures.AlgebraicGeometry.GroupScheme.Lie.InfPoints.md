## What changed

Replaced the sole sorry in `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPoints`
with a complete Lean proof from the geometric first-order diagonal restriction lemma.
Added the proof-only import `Sheaf.AlgebraicGeometry.DualNumbersDiagonal`.
All existing signatures, definitions, public imports, and docstrings are unchanged.
The two products of infinitesimal points agree along both axes by the unit laws;
restricting along the diagonal then gives their equality.
Both sandbox modules compile without warnings. The import-direction check permits
this import and reports no cycle.

## Proved and sorry left

Proved `AlgebraicGeometry.GrpObj.isMulCommutative_infPoints` from the new geometric
lemma; node `lem-ag-inf-points-commutative`. No sorry remains in the item's module.
One sorry is split off:
`AlgebraicGeometry.Scheme.dualNumbers_diagonal_comp_eq_of_axes`, node
`lem-ag-dual-numbers-diagonal`, in `Sheaf.AlgebraicGeometry.DualNumbersDiagonal`.
Its statement concerns arbitrary scheme morphisms and has no group object, kernel,
Lie algebra, or commutativity in it. It is a genuine geometric part of the argument,
not the original theorem renamed or repackaged. Its docstring and node contain the
complete local-coordinate proof. Edge cases include empty bases, zero rings,
nonreduced bases and rings with zero divisors: the free four-term expansion makes
the ideal-intersection computation valid in all cases.

## No longer needed

None of the original imports can be removed: they supply the group structure,
dual-number schemes, or the Lie objects in the definitions of this module.
No existing dependency node or module is pruned. The proof does not import
`InfPointsEquiv`, `PointOfDerivation`, `TangentVectorsVectorSpace`,
`DualNumberSchemePushout`, or `MixedCommutatorTangent`; these were investigated
alternatives, not prior proof dependencies. The first two would cause import
cycles, and the latter geometric statements only cover field bases.

## Where the brief, the DAG or earlier work was wrong

No node has this module as its principal `lean.module`. The only occurrence of
the open commutativity theorem is the audit list in `lem-sc-pic-tangent-space`,
where its `nodes` list is empty. Thus there was no numbered DAG plan for this
specific sorry to translate. The declaration's blueprint tag points to
`sk-d-tangent`. Added a node for the original theorem and a node for its actual
geometric proof dependency, both within that unit; the unit has no realized
proof steps to bypass. No existing statement is disputed or changed.

Stacks Tag 0B2B explicitly gives the square-zero pushout calculation over a
residue field. The arbitrary-base version needed here is the local ring
calculation written out in the helper's proof, not an assertion that the tag
already states the arbitrary-base theorem. LeanSearch was attempted but the
service returned Internal Server Error; this is recorded as unavailable,
without claiming a search verdict.

## New nodes

`lem-ag-dual-numbers-diagonal`: maps from the product of two dual-number
thickenings agreeing on the axes agree on the diagonal. New module
`lean/Sheaf/AlgebraicGeometry/DualNumbersDiagonal.lean`; one named sorry.
Source is the square-zero calculation in Stacks Tag 0B2B, with its local
arbitrary-ring extension explained. LeanFinder, Loogle, and grep found no match;
LeanSearch was unavailable.

`lem-ag-inf-points-commutative`: records the existing theorem and its new proof
route, with sole non-elementary proof dependency `lem-ag-dual-numbers-diagonal`.
No additional Lean declaration or sorry. No change record is needed.

## Second reading by H2

1. **Interface: pass.** Read both delivered modules and diffed InfPoints against the
   repository. The sole existing proof change is the body of
   `GrpObj.isMulCommutative_infPoints`; every existing signature, definition and
   docstring is byte-for-byte preserved. The helper import is plain `import`,
   because only the proof uses it. No change record is required.
2. **Lean and axioms: pass as a partial reduction.** Both modules compile cleanly
   with lcompile in import order. A scratch copy with explicit `#print axioms`
   checks all named declarations of InfPoints and the helper. Only the allowed
   three axioms occur, with `sorryAx` additionally in the commutativity theorem
   and its one reported helper. Thus commutativity is reduced, not yet closed
   under the final axiom criterion. No forbidden declarations or hollow
   definitions were added; the only delivered sorry is the whole proof of the
   named helper theorem.
3. **Split-off statement: pass.** Read Stacks Tag 0B2B: it uses the three-term
   square-zero algebra over a residue field. The report correctly distinguishes
   its arbitrary-base extension. Checked the helper's two axis hypotheses and
   diagonal conclusion against its node. On an affine base the product ring has
   free coefficients `(a,b,c,d)`: the two axis restrictions detect `(a,b)` and
   `(a,c)`, while diagonal restriction detects `(a,b+c)`. Equality on both axes
   therefore suffices, including characteristic two, zero rings, zero divisors,
   and nonreduced rings. Nilpotence identifies all underlying spaces with the
   base, so a common affine target neighborhood exists locally even for a
   nonseparated target. This is a geometric part of the argument, with no group
   hypotheses or commutativity conclusion, rather than a renamed item. Its
   source, complete local proof docstring, and node are present. Fresh LeanFinder
   and Loogle queries plus rg searches found no exact duplicate.
4. **Route and pruning: pass.** Checked both unit-law restrictions in the Lean
   proof: the first uses membership of w in the kernel, the second that of v;
   diagonal restriction gives the two opposite products. The proved
   `lieEquiv_mul` is downstream of this module and cannot supply an independent
   shortcut. The existing scheme pushout statement assumes a field. Closing the
   arbitrary-base helper would require substantial product/affine-local
   infrastructure, not a few-minute repair. Original imports support the group,
   thickening and Lie definitions. There was no existing principal node or old
   proof_deps list to prune. Read `dag/units/sk-d-tangent.json`: both realized
   lists and its steps list are empty; the route is preserved.
5. **DAG: pass after metadata repairs.** The commutativity node records exactly
   the axis unit laws followed by the helper and subtype extensionality; its sole
   proof dependency is the helper. The helper node records the affine
   four-coefficient calculation and gluing, with no unreported Lean dependency.
   Both new nodes have the required stage-3 fields and matching Lean signatures.

Second reading changed only node metadata and this report: wrote the two new
node statements in TeX without changing their meaning, explicitly marked the
failed LeanSearch as unavailable, and recorded the fresh searches. The Lean
proofs and helper statement needed no repair. Pruned none.
