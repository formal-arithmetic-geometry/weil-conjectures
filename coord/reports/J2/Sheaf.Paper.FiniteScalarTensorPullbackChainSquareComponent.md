## What changed

Replaced the assigned component hole by mapped-coproduct extensionality and a complete
pasting calculation from the ordinary scalar tensor pullback square. The assigned
`WeilConjectures.finiteScalarTensorPullback_chain_square_component` retains its exact signature.

Six proved native summand formulas cover fixed inverse image, realization, intrinsic inverse
total, the tensor map of scalar comparisons, mapping the fixed formula through realization,
and the right composite. Four new definitions name the actual left and right chain paths and construct
a diagram of whole cochain complexes and its total and ordinary summand diagram. Every diagram field is an existing
native object or map. Five proved field equations transport the native formulas and ordinary
square into this diagram. A pure categorical calculation pastes these equations, and the
cochain-diagram proof applies it on every coproduct injection. The assigned proof
then takes degree n of the equality of the exact original native chain maps. A separate
proved theorem converts the named diagram paths to that native equality before evaluation.

The diagram and the named chain path let the kernel reuse the large native constructions.
The construction and its field identities are compiled in separate modules. Four proved
identifications project the actual native left and right maps, and one proved equality
reduces the chain diagram to those named paths. These identifications let the native-chain
theorem use equality rewriting instead of expanding all path data together. The abstract
pasting calculation uses only associativity and equality substitution. All changes are in
the assigned module, its proof-route record, and new Sheaf modules with their nodes.

## Proved and sorry left

Closed the single existing hole in
`WeilConjectures.finiteScalarTensorPullback_chain_square_component` by a complete Lean proof
from the ordinary scalar square and the proved native calculation lemmas.

Added exactly one hole:
`WeilConjectures.finiteScalarTensorPullback_ordinary_square`, node
`lem-sf-finite-scalar-tensor-pullback-ordinary-square`, in its own module. Its proof is exactly
`by sorry`. Its docstring and node give the adjunction-unit and pure-tensor proof in words.

The assigned module, nineteen new proved theorem modules, and four new data modules contain
zero holes. This is a decomposition: one upper hole closed, one strictly simpler ordinary
hole added, for a net reduction of zero. The ordinary statement concerns two sheaves;
it contains no complexes, degree indices, infinite coproducts, differentials, localization,
or flatness assumptions. The totalization argument combining it with the component theorem
is fully written in Lean.

The ordinary statement was checked on the zero ring, zero modules, empty schemes, and the
identity morphism. Its adjunction and tensor universal-property proof uses the original
finite-ring and scheme hypotheses throughout. All diagram data are actual constructions.

## No longer needed

Removed proof-only imports `Sheaf.Algebra.Homology.FlatTermKFlatFunctor` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat`.
The degreewise equality uses arbitrary complexes and the native tensor comparison formulas.
These modules continue to serve other proofs; this delivery withdraws no existing module.

Removed `def-sf-representative-tensor-ordinary-pullback-law` from the assigned node's proof
dependencies. It defines the parent equation and supplies no ordinary-compatibility premise.
Its original public import and statement dependency retain the immediate parent's public API.
All other original dependencies remain relevant, directly or through the proved summand
formulas. The blueprint unit and its proof steps retain their route.

## Where the brief, the DAG or earlier work was wrong

The existing DAG referred to “the same ordinary scalar tensor pullback square”, but its
cited declarations do not state that compatibility. In particular,
`RepresentativeTensorOrdinaryPullbackLaw` names an equation. The new ordinary node states
this missing mathematical premise explicitly; all passage to signed totals is proved here.

The component calculation needs no additional sign identity. The signed differentials
already belong to the defined total complexes, and the summand maps have the ordinary square.

The large native functor and total types make direct pasting expensive for the kernel.
The diagrams of whole complexes and their summands, named native paths, and field identities keep
the calculation within separate compilation units while preserving the actual maps.
The per-file time limit and the source-library declarations are retained.

## New nodes

The ordinary square is sourced to Stacks 00YV (`sites.tex`,
`proposition-functoriality-algebraic-structures-topoi`) and 03EL (`sites-modules.tex`,
`lemma-tensor-product-pullback`). Its proof transposes through the intrinsic inverse-image
adjunction, substitutes the normalized mate-unit equations, and identifies both maps on
pure unit tensors by tensor universality and sheafification adjunction.

All nodes lie below `fix-prop-projection-formula`, through the existing proper-projection
presentation, representative comparison, chain square, and assigned component. The current
blueprint proof and unit realization record were read. The Mathlib searches are recorded
in the new nodes and `searches.jsonl`; native total-comparison and injection APIs supply
the proved calculations.

| Node | Content |
| --- | --- |
| `lem-sf-finite-scalar-tensor-pullback-ordinary-square` | The sole new hole: ordinary scalar tensor compatibility. |
| `lem-sf-finite-scalar-tensor-realization-summand` | Proved realization injection formula. |
| `lem-sf-finite-scalar-fixed-tensor-summand` | Proved fixed inverse-image injection formula. |
| `lem-sf-finite-scalar-intrinsic-tensor-summand` | Proved inverse-total injection formula by cancellation and the defining coproduct desc. |
| `lem-sf-finite-scalar-tensor-comparison-map-summand` | Proved total tensor-map injection formula and ordinary degree components. |
| `lem-sf-finite-scalar-tensor-mapped-fixed-summand` | Proved image of the fixed formula through realization. |
| `lem-sf-finite-scalar-tensor-pullback-right-summand` | Proved right composite formula by comparison naturality and the native identities. |
| `def-sf-finite-scalar-tensor-native-right-path` | The explicit original three-factor right chain path. |
| `def-sf-finite-scalar-tensor-summand-diagram` | A record of objects and arrows, and its actual native construction. |
| `lem-sf-finite-scalar-tensor-diagram-fixed` | Proved fixed field equation. |
| `lem-sf-finite-scalar-tensor-diagram-realization` | Proved realization field equation. |
| `lem-sf-finite-scalar-tensor-diagram-map` | Proved tensor-map field equation. |
| `lem-sf-finite-scalar-tensor-diagram-ordinary` | Proved transport of the ordinary square to the diagram. |
| `lem-sf-finite-scalar-tensor-diagram-right` | Proved right field equation. |
| `lem-sf-finite-scalar-tensor-diagram-commutes` | Complete categorical pasting and its native application. |
| `def-sf-finite-scalar-tensor-native-left-paths` | The explicit tuple of the three original left chain maps. |
| `def-sf-finite-scalar-tensor-native-chain-diagram` | A record of whole complexes and the actual left and right chain maps. |
| `lem-sf-finite-scalar-tensor-native-chain-commutes` | Proved chain-map equality by degreewise mapped-coproduct extensionality. |
| `lem-sf-finite-scalar-tensor-pullback-native-chain-square` | Proved equality of the exact original native chain-map composites, before degree evaluation. |
| `lem-sf-finite-scalar-tensor-native-left-edge-1` | Proved identification of native left edge 1 with its tuple projection. |
| `lem-sf-finite-scalar-tensor-native-left-edge-2` | Proved identification of native left edge 2 with its tuple projection. |
| `lem-sf-finite-scalar-tensor-native-left-edge-3` | Proved identification of native left edge 3 with its tuple projection. |
| `lem-sf-finite-scalar-tensor-native-right-edge` | Proved identification of the right native path with its explicit composite. |
| `lem-sf-finite-scalar-tensor-native-paths-equal` | Proved equality of the named left tuple composite and right native path. |

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarFixedTensorSummand": "9d8e32b62255df0bc31dae14d92e0722f68d1288", "Sheaf.Paper.FiniteScalarIntrinsicTensorSummand": "cbdadf765dafd0198eb36f227ca99c4afb689a2f", "Sheaf.Paper.FiniteScalarTensorComparisonMapSummand": "3ccd8ea57b33a7112414950a7e7db617f29b38ff", "Sheaf.Paper.FiniteScalarTensorDiagramCommutes": "75e84135a1b0b8977c7b4b16a5b5829a5e457bcc", "Sheaf.Paper.FiniteScalarTensorDiagramFixed": "87b2dc625b7501047ef58944cb5c9f520d743946", "Sheaf.Paper.FiniteScalarTensorDiagramMap": "7717ddf49854db2064cdf91386d9d6a02f1fecaa", "Sheaf.Paper.FiniteScalarTensorDiagramOrdinary": "6ec28a1b7fb78205338fa2f8d6cc942c58bd0f86", "Sheaf.Paper.FiniteScalarTensorDiagramRealization": "fb0d6c880916beae0653c1fbf299a7aaccc81fae", "Sheaf.Paper.FiniteScalarTensorDiagramRight": "c6327f640e40f2ec4f2b3d2d0611122597577284", "Sheaf.Paper.FiniteScalarTensorMappedFixedSummand": "d3f48204d8523bbc9e4207ff0ff81ce73f12933d", "Sheaf.Paper.FiniteScalarTensorNativeChainCommutes": "da683b24dede8959255d479c929a65e6ade23b2b", "Sheaf.Paper.FiniteScalarTensorNativeChainDiagram": "692dfa8737b4cb67d89ddf50e6ccc162df7072b0", "Sheaf.Paper.FiniteScalarTensorNativeLeftEdge1": "56c8ad25ef9613f2f9167b8eca71ccb0a17554ab", "Sheaf.Paper.FiniteScalarTensorNativeLeftEdge2": "8915ece5a0c69548b49efa24dc53656e180c0158", "Sheaf.Paper.FiniteScalarTensorNativeLeftEdge3": "a67a35cadce1ca8f5d68c03a735b24822eb7ab00", "Sheaf.Paper.FiniteScalarTensorNativeLeftPaths": "2657a89bfc1e304069029f9ec176afea1261e488", "Sheaf.Paper.FiniteScalarTensorNativePathsEqual": "807b37e3aae33e98723672c7ae47b8f0b3b658c4", "Sheaf.Paper.FiniteScalarTensorNativeRightEdge": "64b3a2eb0755d1a4a524166fd7e91b1d52bf46af", "Sheaf.Paper.FiniteScalarTensorNativeRightPath": "6bc469c333804690af1ec05fe993690a546f06ca", "Sheaf.Paper.FiniteScalarTensorPullbackChainSquareComponent": "982defffa5317de2f936b31ded0f9cea2dddc134", "Sheaf.Paper.FiniteScalarTensorPullbackNativeChainSquare": "46fa4376618a5c1468ec3b289adad14aa32fd033", "Sheaf.Paper.FiniteScalarTensorPullbackOrdinarySquare": "e46709d51e59b69820fec9d78e0d91415510a47e", "Sheaf.Paper.FiniteScalarTensorPullbackRightSummand": "9a59aedd15e6ec0a9f0a0d669f40f17cf00b23d2", "Sheaf.Paper.FiniteScalarTensorRealizationSummand": "cbb8003584bba8e9228193218ac23ef1f1656032", "Sheaf.Paper.FiniteScalarTensorSummandDiagram": "62c7ce941e8ed44075b388d80a171acf195edbb2"}, "results": {"Sheaf.Paper.FiniteScalarTensorPullbackChainSquare": {"hash": "19e302b571342f2bf1f671c15d5e9b18f894aa1f", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T13:37:51+0800", "transitive": 0, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
