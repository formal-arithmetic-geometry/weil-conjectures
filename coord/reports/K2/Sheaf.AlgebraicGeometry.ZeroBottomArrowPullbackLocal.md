## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.zeroBottomArrow_pullback_local` by a proof through an
actual affine chain representative and a natural pullback square. The original
signature, universes and public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.ZeroBottomArrowAffineChainModel` for the affine
realization step and `Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare` for
transport of an already specified chain square. The first step concludes an
isomorphism on chain homology, not the desired pulled-back isomorphism. The
second starts with a chain square and an invertible component, and concludes a
homology comparison square, not invertibility of that homology map.

The item's proof supplies both directions of the zero-differential
homology/component comparison using `ShortComplex.LeftHomologyMapData.ofZeros`.
It turns the first step's homology isomorphism into a component isomorphism,
applies the second step, turns the resulting component isomorphism back into a
homology isomorphism, and solves the comparison square by conjugation. The three
private helpers are completely proved and contain no sorry.

Updated the item's DAG proof and proof dependencies to this route. The unit
`sk-prop-av-cube` has no realized nodes in its statement or steps, and this local
reduction does not change that unit's route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.zeroBottomArrow_pullback_local`
(node `lem-sc-zero-bottom-arrow-pullback-local`).

The following new statements are strictly separate parts of its argument:

- `AlgebraicGeometry.Scheme.zeroBottomArrow_affine_chain_model`
  (node `lem-sc-zero-bottom-arrow-affine-chain-model`).
- `AlgebraicGeometry.Scheme.bottomFreeChain_pullback_square`
  (node `lem-sc-bottom-free-chain-pullback-square`).

Current delivery is a decomposition: one original hole closed and two new holes
added. There are no holes left in the item's module. Its theorem still depends
on the named unproved intermediate statements; this is not a claim of an
axiom-free proof of the original theorem.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology`
- `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`

They are still needed by the two intermediate statements and remain imported
there. None of their modules or nodes is pruned from the transitive proof route.
No previously needed module is claimed pruned. The existing degree-zero
`BottomChainModelPullbackTransport` and
`PerfectUniversalH0LocalChainModel` were inspected but not imported: the former
uses degree zero and chosen derived localizations on localized sites, and the
latter assumes perfectness and universal rank hypotheses absent here. Neither
provides this arbitrary-degree scheme-chart interface.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan appears sound. However,
`nonempty_homology_derivedOpenPullback_iso_restrict` only asserts existence of
object isomorphisms; its public statement does not supply a natural comparison
for the specified arrow. The new chart glue explicitly needs that naturality,
which must be obtained from the exact restriction comparison and left-derived
uniqueness, not inferred from unrelated object isomorphisms. Likewise the affine
representative theorem is on a localized open site, whereas the given K is on
`U.toScheme`; transporting the localization and complexes across
`Modules.overEquiv` is real glue left to the chart step.

Checked Stacks 0BDL (zero-bottom matrix chart), 08CR (second proof's local chain
representatives), and 06YJ (natural K-flat computation) directly. The two new
statements are consequences of these arguments, not verbatim Stacks statements.
The zero-rank case uses zero free modules; arbitrary negative a is permitted;
empty schemes admit no point x or y; the finite-free bounds need not be uniform
over different charts. No reducedness, flatness of g, or noetherian hypothesis
was introduced. In the transport statement only degree a-1 is required zero,
so even additional lower cohomology causes no problem for its bottom calculation.

The `blueprint_refs.py ancestor` command returns no ancestor because the existing
node's `created.item` is a module name, not a node id. The new records retain the
explicit ancestor `thm-sc-theorem-of-cube` already recorded in the item's
`blueprint.from`, with the exact chart steps specified. Blueprint searches for
`bottom chain` and `chain representative` returned no imported blueprint match.
LeanSearch returned HTTP 500, recorded as unavailable; Loogle/LeanFinder and
Mathlib grep found generic primitives but no exact chart statement.

## New nodes

`lem-sc-zero-bottom-arrow-affine-chain-model`:
`lean/Sheaf/AlgebraicGeometry/ZeroBottomArrowAffineChainModel.lean`.
Isolates restriction, identification of the single finite-free source, affine
chain realization of the fixed arrow, and preservation of its original bottom
homology isomorphism. It has no arbitrary base-change morphism or pulled-back
invertibility conclusion.

`lem-sc-bottom-free-chain-pullback-square`:
`lean/Sheaf/AlgebraicGeometry/BottomFreeChainPullbackSquare.lean`.
Isolates transport of a supplied finite-free chain square under arbitrary
scheme pullback and exact restriction. It has no original sheaf M or original
bottom-homology hypothesis, and concludes a square with invertible component.
There is no statement or definition change and no change record.

## Second reading by K2

1. Compared the delivered item module with the repository version. The public
   theorem signature is unchanged byte for byte; only proof code, private
   helpers, and proof-only imports changed. The two added modules contain the
   new split statements recorded by their DAG nodes.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no
   errors, no forbidden declarations, and no `sorry` in a definition. The only
   remaining `sorry`s are the two named public split theorems, each with a DAG
   node and a proof-source docstring. The completed item theorem's proof uses
   only the stated category-theoretic primitives and those two split results.

3. Checked the split statements against the item type and their Lean
   declarations. The affine-chain statement supplies only the local chain
   representative and homology isomorphism; the pullback-square statement
   supplies only transport of a supplied chain square. Both are strictly
   simpler than the item and retain all hypotheses needed by the subsequent
   proof. Searches of Lean, Mathlib, Loogle, and LeanFinder found no existing
   equivalent declarations.

4. Checked the proof from the target downward. The private zero-differential
   equivalence is proved using `ShortComplex.LeftHomologyMapData.ofZeros`, and
   the final comparison is solved by conjugation with the displayed endpoint
   isomorphisms. The removed direct imports are no longer used by the item;
   they remain in the split modules where their statements require them.

5. Checked the DAG records and unit route. The target and both split nodes
   have matching Lean declarations, proof steps, dependencies, origins, and
   sources. The route remains in unit `sk-prop-av-cube`; no realized unit step
   was bypassed or altered.

Changed only the item proof/imports, added the two split modules and matching
DAG nodes, and appended this review. No statement, definition, or change
record was altered.
