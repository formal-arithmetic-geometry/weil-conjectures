## What changed

Proved `AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_target`
in `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`,
with its signature unchanged. Minimality places each boundary point over s.
The flat composite to S transfers the given depth bound via the existing flat
local depth formula. The existing depth-support bound finishes the dimension
inequality. Added proof-only imports of `Sheaf.RingTheory.FlatLocalDepthFormula`,
`Sheaf.RingTheory.DepthLeSupportDimension`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`.

Updated the existing node's proof, proof_deps and proof_origin to record this
argument and the already proved canonical-stalk-spectrum flatness instance.
The blueprint unit's route is preserved. The declaration-local unused-variable
linter setting preserves the existing hS and hs binders, which are unnecessary
once the supplied hdepth and hmin hypotheses are available.

Source checked: [Stacks 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ), local
claim; [0337](https://stacks.math.columbia.edu/tag/0337), flat local depth formula;
[00LK](https://stacks.math.columbia.edu/tag/00LK), depth-support bound.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_target`
(node `new-stalk-normalization-boundary-dimension-two-target`).
No sorry remains in the delivered module. No holes or new declarations were added.
The proof uses the existing named depth theorems; it does not duplicate or change them.

The module compiles using lcompile.py. The static import-pruning check passes.
The empty pullback has no points to check. An empty U is handled by hmin;
no density, nonempty-cover or positive-relative-dimension assumption is introduced.

## No longer needed

Removed direct imports of
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale` and
`Mathlib.AlgebraicGeometry.Normalization`. Neither its Galois-cover interface nor
normalization is used by this local dimension estimate. A public import of
`Mathlib.RingTheory.KrullDimension.Basic` supplies the dimension expression in
its statement directly. Both original proof-dependency nodes remain necessary;
no DAG proof dependency was pruned. No claim is made that the removed modules
are absent from every other target route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG compressed several steps but its
two stated depth lemmas suffice. Composing the smooth pullback projection with
the flat canonical stalk-spectrum map gives a local flat map directly from the
stalk at s, avoiding an extra transport through the closed-point stalk of Spec.
The repository's literature checkout is absent on this machine; the cited
Stacks pages were read online. No statement or definition was changed.

Public-import pruning is recorded in
`coord/changes/stalk-normalization-boundary-dimension-two-core-imports.md`.
Both direct importers already import the removed modules explicitly; no forced
adaptation is necessary.

## Second reading by J3

1. Interface: PASS. Diffed the sole delivered Lean module against the repository
   and programmatically compared the complete existing theorem signature,
   byte for byte. No statement, definition, universe or visibility changed.
   The public-import change has its supplied change record. Checked both direct
   importers: each independently imports FiniteEtale and Normalization, so neither
   requires adaptation.
2. Proof: PASS. Compiled the module through lcompile.py with no errors or warnings.
   Compiled a scratch copy with #print axioms for
   AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_target:
   only propext, Classical.choice and Quot.sound occur, with no sorryAx.
   Static inspection found no sorry, forbidden declaration or data definition.
   Specialization, the pullback identity, locality, flatness and the Noetherian
   stalk instances supply exactly the hypotheses used by the depth argument.
3. Split statements: PASS, vacuous. No statement or hole was added or split off.
   Checked the existing depth theorem signatures and canonical-stalk flatness
   instance. Empty pullbacks make the conclusion vacuous; empty U still permits
   the hmin argument. Dimension-zero or dimension-one source stalks cannot
   satisfy hdepth, by the existing depth-support bound.
4. Route and pruning: PASS. Read dag/units/sk-prop-input-spreading.json: its
   Noetherian-base step propagates depth by flatness, exactly the route retained
   here. Its realized fields are untouched. Searched the library for flat depth
   and dimension inequalities and used msearch.py loogle with
   "ringKrullDim", "Flat" (zero hits); the existing faithfully-flat dimension
   helper is still sorry and would not improve this closed proof. No shorter
   proved substitute was found. All retained public imports supply statement
   vocabulary; all three added proof imports are non-public. Both original
   proof_deps remain used, so there is no omitted dependency to prune. The two
   removed direct imports are fully listed under No longer needed.
5. DAG: PASS. Compared the original and delivered node: only proof,
   proof_deps and proof_origin change. The three proof dependencies identify
   the actual canonical flatness instance and the two depth theorems used by
   Lean. No new nodes need validation. The node's lean.statement matches the
   unchanged theorem signature.

Second reading changed only the first DAG proof step's wording: f(y), rather
than the point of Spec O(S,s) itself, specializes to s in S. Added this review
section. The Lean proof and import choices were already correct and are unchanged.
