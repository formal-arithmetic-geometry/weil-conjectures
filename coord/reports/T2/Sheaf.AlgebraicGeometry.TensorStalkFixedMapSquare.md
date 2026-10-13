## What changed

Proved `AlgebraicGeometry.tensorStalkComparison_fixedMap_square` without changing its
signature or visibility. Added proof-only imports of
`StalkComparisonPullbackNaturality`, `BaseDerivedTensorModelQuasiIsoComparison`, and
`TensorStalkChainCoordinates`. Two fully proved private helpers normalize the
coordinate comparison and transport it between representatives. The final proof
applies homology to the chain square, transports the base-derived tensor model,
and composes the source and target isomorphisms. Updated the parent's proof plan
to match the Lean proof. All writes are sandbox files.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.tensorStalkComparison_fixedMap_square`
(node `lem-pc-tensor-stalk-fixed-map-square`). The item module contains no `sorry`.
The private helpers `coordinates_comparison_normalize` and
`coordinates_comparison_transport` are fully proved, with no added holes.

Added one lower hole:
`AlgebraicGeometry.exists_tensorStalk_chain_coordinates`, in
`Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates`, node
`lem-pc-tensor-stalk-chain-coordinates`. Its entire proof is `by sorry`; its
statement, source, complete construction and generator argument are documented.
This is a decomposition: one hole closed, one added, net zero. The remaining
statement only constructs tensor coordinates and a chain square; the model
transport, application of homology, and comparison with arbitrary d are proved
in the item. No arbitrary witness is used to define data.

## No longer needed

No baseline imports or planned dependency nodes were pruned. All six parent
proof-dependency nodes remain used. The earlier sandbox's trivial auxiliary
`tensorStalkComparison_fixedMap_square_aux` was removed; it served no proof step.
No new normalization or coordinate-transport node is needed: both helpers are
proved directly from existing declarations.

## Where the brief, the DAG or earlier work was wrong

The previous blocked diagnosis was an elaboration issue, not a tool failure.
Normalization requires the local R/A/B/C algebra instances and an explicitly
typed `DerivedCategory.Q` on sheaves over X'. Transport uses the mapped
isomorphism's inverse equation to avoid ambiguous category inference, and
`map_comp_assoc` for reassociated functor maps. These resolve the reported
pullback/stalk homology-map failures without changing any interface.

The sandbox previously had two private theorem holes and an untouched item hole;
none is retained. The repository has no local Stacks tex checkout; the cited
sources were read at https://stacks.math.columbia.edu/tag/0DJA and
https://stacks.math.columbia.edu/tag/0BYJ. They prescribe tensor transitivity via
K-flat representatives. Zero factors and zero rings require no exclusions, and
neither horizontal comparison nor scalar extension of an arbitrary
quasi-isomorphism is assumed invertible. The unit's realized route is unchanged.

## New nodes

`lem-pc-tensor-stalk-chain-coordinates` records
`AlgebraicGeometry.exists_tensorStalk_chain_coordinates` in
`lean/Sheaf/AlgebraicGeometry/TensorStalkChainCoordinates.lean`. It isolates the
chain-level tensor representative and stalk identifications. Its source and
target complexes are specified, and its chain equation is the input used by the
proved cohomology assembly. The docstring and node give construction and the
summand/pure-tensor verification, with no flatness or boundedness hypothesis.
No definition, existing signature or public import changed; no change record or
forced adaptation is needed.

## Second reading by T2

1. **Statements and interfaces.** Compared the delivered fixed-map module byte-for-byte against
`sheaf-dag`; the public theorem signature and visibility are unchanged. The added chain-coordinate
statement is a strictly smaller intermediate existence statement: it fixes one representative `P`,
one coordinate system `c`, and only the chain-level tensor equation, with no cohomology transport or
arbitrary second coordinates. Its source, edge cases (zero complexes and zero rings), and node agree.
Verdict: pass.

2. **Proof and trust.** Compiled both sandbox modules with `lcompile.py --all`; both compile without
errors or warnings. The fixed-map theorem has no `sorry`; the only remaining `sorry` is the named,
documented `exists_tensorStalk_chain_coordinates` theorem. No definitions contain `sorry`, and the
proof introduces no axiom, unsafe, opaque, extern, or implemented-by declaration. Verdict: pass.

3. **Search and novelty.** Repeated local and launcher searches for tensor-stalk comparison,
naturality, and homology-map composition found no existing declaration matching either the fixed-map
proof or the new chain-coordinate statement. The new node is therefore needed and is not a restatement
of the target. Verdict: pass.

4. **Pruning and route.** The proof uses the stated coordinate, pullback-naturality, base-derived
model-comparison, and homology declarations. The three added imports are proof-only plain imports;
all public imports are needed by signatures. No old proof dependency is unused, and the unit's
realized route remains unchanged. Verdict: pass.

5. **DAG and report consistency.** Updated proof and proof-dependency fields match the Lean route;
the new node records its statement, source, proof steps, searches, and `split` status. The report
records one hole closed and one strictly lower hole added (a decomposition), with no forced adaptation
or statement change. Verdict: pass.

Changed only the two sandbox Lean modules, the new chain-coordinate node, the fixed-map node's proof
metadata, and this report. No existing declaration or definition was changed.
