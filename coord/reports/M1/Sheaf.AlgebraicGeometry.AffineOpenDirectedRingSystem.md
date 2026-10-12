## What changed

Proved `AlgebraicGeometry.exists_affineOpen_directedRingSystem` in
`Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem`, without changing its signature or
existing docstrings. Added the proof-only import `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
The upper-tail functor into the over category is initial. Its affine-open limit cone
provides the coordinate-ring diagram via global sections, whose colimit comparison supplies
the requested spectrum presentation with the specified coprojection square.
Updated the existing node's proof and dependencies to match this Lean argument.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.exists_affineOpen_directedRingSystem`
(node `lem-weil-pbc-affine-open-directed-ring-system`). No holes added or split off;
no `sorry` remains in the delivery. The theorem compiles without warnings using lcompile.py.
The construction works for empty affine opens, singleton directed preorders, and
preorders with equivalent distinct indices: no points, antisymmetry, or nontrivial rings
are assumed. The dry run also checks the permitted axioms.

## No longer needed

No existing imports removed. The trial import `Mathlib.CategoryTheory.Filtered.Final`
was removed because the required API is already available through AffineTransitionLimit.
The proof no longer needs `lem-weil-pbc-spec-colimit-limit`: rather than applying Spec
preservation to the ring colimit, it uses Mathlib's `preservesColimit_Γ` for affine schemes.
That node is a Mathlib leaf, so no Sheaf or WeilConjectures module is pruned.
All other original proof-dependency nodes are retained. No realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned limit comparison can be shortened using the
already-proved global-sections preservation theorem. The over category needs only an
initial functor from the upper tail, not an explicit equivalence. No changes to definitions,
statements, or target signatures were needed.

## Second reading by M1

1. Interfaces: PASS. Diffed the sole delivered module against the repository and
   compared the theorem signature byte for byte through `:=`. The signature,
   existing docstrings, public imports, and definitions are unchanged. The added
   AffineTransitionLimit import is proof-only. No change record is required.
2. Proof: PASS. Independently compiled the delivered file with lcompile.py, without
   errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.exists_affineOpen_directedRingSystem` reports exactly
   propext, Classical.choice, and Quot.sound. No sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition occurs. Read both restriction
   equalities and the colimit comparison: their directions agree with the goal.
3. Split statements: PASS, none. No new declarations, nodes, or holes were added.
   Checked the construction for the empty open, a singleton index, and equivalent
   distinct indices in a preorder: initiality uses subsingleton homs, not
   antisymmetry, and affineness imposes no nonzero-ring or point hypothesis.
4. Route and pruning: PASS. Read the Mathlib opensDiagram/opensCone definitions,
   isLimitOpensCone, preservesColimit_Γ, and isoSpec naturality. Searched the
   upstream and Sheaf sources and independently searched Mathlib with
   coconePointUniqueUpToIso/upperTail/directedRing terminology; found no direct
   replacement for the combined theorem. All imports serve the statement or
   proof. The sole removed old dependency is lem-weil-pbc-spec-colimit-limit,
   already listed above; it is a Mathlib leaf, so no module is pruned. Read
   dag/units/sk-thm-p1.json: neither this item nor the removed leaf realizes a
   unit statement or step, and the unit route is preserved.
5. Nodes: PASS. Only proof, proof_deps, and proof_origin changed. The two proof
   steps describe the actual construction and comparison, and their uses union
   equals proof_deps. No new-node checks are needed. The retained affine-open,
   affine-morphism, adjunction, restricted-limit, and colimit dependencies match
   the ingredients used.

Second reading changed only this report, adding the independent review and
verification evidence. No repair to the Lean proof or node was needed. The
existing theorem docstring describes the original Spec-limit plan; the updated
node and report accurately describe the implemented global-sections comparison.
