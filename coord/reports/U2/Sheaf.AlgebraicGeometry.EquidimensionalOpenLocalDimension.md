## What changed
Replaced the proposed false general-topological neighbourhood lemma with a direct proof of
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`. The proof bounds O's
dimension by its components, constructs the closed subscheme of a component through x using
Mathlib's vanishing ideal, applies the existing `dimension_locally_algebraic` theorem to its
nonempty open inverse image, and transports the local dimension along O's open inclusion.
Added proof-only imports `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
`Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic`; existing public imports are retained.
Updated the original node's proof, proof_deps and proof_origin to this route. No existing
signature, visibility, definition, statement, or unit realization was changed.

## Proved and sorry left
Closed the original hole in `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`
(node `lem-sbc-equidimensional-open-local-dimension`). One of one original holes is closed;
zero holes added, zero split off, and no sorry remains in the delivered module.
Removed the first worker's unproved and false
`AlgebraicGeometry.topologicalKrullDim_eq_of_equidimensional_open_neighborhood` and its new node
`lem-sbc-equidimensional-open-neighborhood-dimension` before delivery.
The proof still depends on the existing sorry theorem
`AlgebraicGeometry.dimension_locally_algebraic` (node `lem-sc-dimension-locally-algebraic`).
This is a reduction to an existing irreducible-scheme result, not an axiom-free completion
of the target import closure. Closure progress is for the pinned sorry ledger to determine;
no closure net or whole-library progress is claimed here.

## No longer needed
No old repository imports or old proof_deps were pruned: the sole old dependency
`lem-weil-pbc-dimension-at-point-open-subspace` is still used.
The provisional helper and node `lem-sbc-equidimensional-open-neighborhood-dimension` are removed.
The redundant explicit proof import `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` was removed;
ClosedImmersion already publicly imports it. No existing library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong
The first worker's helper stated that every nonempty open in an arbitrary equidimensional
topological space has the component dimension. This is false: on the two-point Sierpinski
space with opens empty, {generic}, and the whole space, there is one irreducible component
of dimension 1, but the open singleton has dimension 0. The helper's docstring and node
also used affine neighbourhoods without any scheme or locally finite type hypotheses and
lacked a full valid proof. It was removed rather than left as a trusted sorry.
The earlier report overlooked the existing `dimension_locally_algebraic` declaration, which
supplies precisely the nonempty-open dimension calculation after constructing a component
subscheme. The target statement itself was correct and is unchanged.

## Second reading by U2
1. Compared the entire delivered module to the read-only repository using diff and checked
   the original declaration signature byte for byte through `:= by`: identical. Only its
   proof, proof explanation and proof-only imports change. No change record is required.
2. Compiled the file with lcompile.py. No error, warning, sorry, prohibited declaration or
   hollow definition remains in the delivery. An explicit scratch #print axioms check is
   performed for the target: exactly propext, Classical.choice, Quot.sound and sorryAx,
   from the existing unproved imported theorem. No other axiom occurs.
   The component subscheme is the actual Mathlib vanishing-ideal construction. The witness
   used to prove its inverse image nonempty comes from Mathlib's proved range equality.
3. Rejected the proposed split-off statement using the two-point counterexample above and
   deleted its declaration and node. Searched independently with leanfinder for common
   dimension bounds on maximal irreducible closed subspaces, loogle for topologicalKrullDim,
   and grep/rg for dimension_locally_algebraic, component dimensions and closed subschemes.
   Reused the existing irreducible locally algebraic scheme theorem; no new statement remains.
   Edge cases: empty O has no x; empty U cannot contain x; n = 0 is handled by the same
   inequalities without a positivity assumption; no global quasi-compactness is assumed.
4. Read the proof downward and replaced the false reduction with the component argument.
   Both new imports are proof-only and used; removed the redundant Subscheme import.
   All old proof dependencies remain listed and used. The unit sk-prop-normal-form has empty
   realized.statement and realized.steps arrays, and the item's below-unit route does not
   bypass or alter any realized unit node. The unit record is unchanged.
5. Updated the existing node's proof steps and their proof_deps union to the actual Lean:
   component upper bound, vanishing-ideal closed subscheme, existing irreducible-scheme
   dimension theorem, dimension embeddings and open-subspace local-dimension transport.
   The statement and lean statement record remain unchanged. There are no new node files.
Changes by this reader: removed the false helper and its node; wrote the direct proof using
an existing lemma; removed a redundant import; updated the proof docstring, DAG and report.
