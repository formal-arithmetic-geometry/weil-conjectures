## What changed

Replaced the `sorry` in `AlgebraicGeometry.Scheme.bottomFreeChain_pullback_square` by a
complete assembly proof, preserving its signature. It sets V to the inverse image of W,
constructs F as tensor pullback of the restricted morphism followed by the inverse of
`Modules.overEquiv V`, and applies F termwise to A, B and α. Mathlib proves preservation
of the two zero terms, the two zero differentials and the invertible degree-a component.
The supplied point belongs to V directly by hy.

Added `Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison`, with the natural
homology comparison for those explicitly constructed termwise images. This theorem
has no bottom-degree vanishing assumptions, no component-invertibility assumption,
and no point or membership assumption. It supplies only the comparison part of the
original argument, so the item still proves the bottom-degree conditions itself.
The object's data is an explicit expression, never chosen from an unproved existence
statement. Updated the item's proof route and added the comparison node.

Both delivered modules compiled without warnings through `lcompile.py --all`.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.bottomFreeChain_pullback_square`
(node `lem-sc-bottom-free-chain-pullback-square`). No `sorry` remains in that module.

Added one hole:
`AlgebraicGeometry.Scheme.bottomFreeChain_pullback_comparison`
(node `lem-sc-bottom-free-chain-pullback-comparison`), in the new comparison module.
Its proof is exactly `:= by sorry`; its docstring gives the complete construction,
source and naturality argument. Thus this is a decomposition: one upper hole closed,
one strictly smaller comparison obligation added, net zero holes. It does not claim
an axiom-free proof of the geometric comparison.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`

Their corresponding nodes are no longer direct proof dependencies of the item:
`lem-pc-flat-complex-derived-pullback`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-pc-derived-pullback-open-restriction-universes`.
They remain imported by and needed for the new comparison theorem; no global pruning
of those modules or nodes is claimed. The original public statement imports remain.

Deleted the saved attempt's undeclared/redundant auxiliary module and probe from the
sandbox. Its `bottomFreeChain_pullback_aux_data` was unused, and its
`bottomFreeChain_pullback_naturality` duplicated the entire item behind a `True`
hypothesis. Neither declaration nor the stale auxiliary node is delivered.
Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The saved attempt was not a valid reduction: applying a theorem with the complete
original conclusion plus a vacuous `True` binder only relocated the hole. Its report
also did not describe its actual Lean, and its naturality hole had no matching node.
This delivery removes that attempt and replaces it with a comparison obligation
that omits all five bottom-degree assumptions and conclusions, together with a real
proof of those five conclusions in the item.

The original DAG route remains mathematically valid. Its unit
`sk-prop-av-cube` has no realization recorded in its unit JSON; this work changes no
unit or chapter route. The prescribed local Stacks checkout is absent on this
machine; the cited tags 06YD, 06YJ, 0D5S and 08DW were read from their official pages.
LeanSearch returned an internal server error; the successful LeanFinder and Mathlib source searches are recorded in the new node. No exact existing comparison
statement was found. Empty opens, zero ranks, arbitrary integer degrees, zero objects
and arbitrary chain maps are covered by the comparison's construction; it asserts no
invertibility without the original hα, which the assembly proof uses explicitly.

## New nodes

`lem-sc-bottom-free-chain-pullback-comparison`, in
`dag/nodes/sec-abelian-varieties/lem-sc-bottom-free-chain-pullback-comparison.json`,
states the simultaneous natural homology comparison for the fixed tensor-pullback
and site-equivalence functor on bounded-above finite-free chain complexes. It is a
strict part of the original argument: it neither assumes nor concludes any of its
five bottom-degree properties. The node records its source, complete proof in words,
three kinds of search, exact Lean signature and the original unit and chapter.
No change record or forced adaptation is needed; no existing signature is changed.

## Second reading by M2

1. I compared the delivered square module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only the
   proof and proof-only imports changed. The added comparison module and node are
   explicitly listed above, with no accidental repository edits.

2. I compiled both delivered modules with `lcompile.py`; both compile without
   errors or warnings. The sole remaining `sorry` is the named comparison theorem,
   and it has a matching node and a complete source-based docstring. No forbidden
   declarations or hollow definitions occur.

3. The comparison statement omits every bottom-degree hypothesis and conclusion
   while retaining the boundedness, finite-free, chart-square, and naturality data
   needed by the construction. It is therefore a true strict reduction of the
   original obligation, rather than a restatement. Searches recorded in its node
   found no existing library theorem with this statement.

4. The proof uses the explicit inverse-image open and tensor-pullback/equivalence
   functor, then derives the five bottom-degree facts with `map_isZero`, `map_zero`,
   and functorial preservation of isomorphisms. The three former direct proof
   imports are removed from the square module and retained as proof imports of the
   comparison module; the DAG proof dependencies match this route.

5. The unit route and chapter are unchanged. The unit has no realized-field update
   required by this proof, and no global module pruning is claimed.

I changed no Lean statements or definitions. I only verified the proof, metadata,
imports, and report, and retained the explicitly documented comparison split.

Additional independent checks: a byte comparison of the original and delivered
`bottomFreeChain_pullback_square` signatures passed. The existing node differs only
in `proof`, `proof_deps`, and `proof_origin`; the new node's verbatim Lean signature
and the union of its proof-step dependencies match. I reread the four official
Stacks tags and the three imported comparison/flatness declarations, and repeated
searches with `map_isZero`, exact equivalences, and natural homology comparisons.
The results give the elementary preservation and homology primitives, not an
existing scheme-chart square theorem. The empty-open and zero-rank cases impose
no nonemptiness condition; arbitrary integer degrees use the same homology functor.
The first complete second-reader dry run passed with review class CODEX.

The scratch-copy `#print axioms` check also passed: both
`bottomFreeChain_pullback_square` and `bottomFreeChain_pullback_comparison` use only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
from the explicitly reported comparison hole; this remains a decomposition with
net zero holes, not a completed axiom-free geometric comparison.
