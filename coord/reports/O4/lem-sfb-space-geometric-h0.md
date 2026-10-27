## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGeometricH0` states
`AlgebraicGeometry.AlgebraicSpace.isIso_moduleStructureMap_of_geometricFibres_reduced_connected`.
Its sole theorem has proof `sorry`; no definitions or other theorems are introduced.
The accepted statement, proof, source, and all other mathematical node fields are unchanged.
Four already landed nodes are added to `stmt_deps` to record the interfaces used in the
signature: `def-sfb-space-morphism-properties`, `def-sfb-space-module-structure-map`,
`def-a1-space-point-topology`, and `def-sfb-space-sheaf-fibre-product`.
This uses the authorization for adding landed statement dependencies in brief-stage2 §5.

Source read: `literature/stacks-project/spaces-perfect.tex`,
`lemma-proper-flat-geom-red-connected`, Tag 0E0S, statement and proof. Also read the current
blueprint's `det-thm-sf-ctf-stability-direct-images` statement and proof (3), at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`.
This node is an auxiliary algebraic-space input, not the unit's own statement.

Clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`. The spaces X and Y over S are
  `{X Y : AlgebraicSpace S}`; the named morphism is `(f : X ⟶ Y)`.
- Properness is `(hp : MapIsProper f)`. Its existing definition is exactly
  separatedness, finite type, and universal closedness. Separatedness tests the
  relative diagonal by closed immersions; finite type is quasi-compactness and the
  local finite-type chart test; universal closedness quantifies over all space base changes.
- Flatness is `(hf : MapIsFlat f)`, the existing all-compatible-etale-charts test.
- Finite presentation is `hfp`: `MapIsLocallyOfFinitePresentation f`,
  `MapIsQuasiCompact f.hom.hom`, and
  `MapIsQuasiCompact (pullback.diagonal f.hom.hom)`. The last is quasi-separatedness.
  This is the same finite-presentation expression as the landed locality theorem.
- Every geometric point is quantified by `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`,
  `(b : Spec (CommRingCat.of Ω) ⟶ S)`, and
  `(y : yoneda.obj (Over.mk b) ⟶ Y.obj.obj)`. By Yoneda this last map is exactly a
  morphism from the representable Spec Ω over S, with no representability condition
  imposed on the map to Y. No geometric points over S are excluded.
- Its geometric fibre is the actual presheaf pullback
  `Limits.pullback f.hom.hom y`. Sheaf fibre products have this underlying presheaf,
  so this is X ×_Y Spec Ω, rather than a set of lifts or an arbitrary model.
- Reducedness is the first conjunct of `hgeom`: every
  `T : CostructuredArrow yoneda (Limits.pullback f.hom.hom y)` with `IsEtale T.hom`
  has `AlgebraicGeometry.IsReduced T.left.left`. These are all representable etale
  scheme charts, and scheme reducedness means every ring of regular functions is reduced.
  This is equivalent to the node's affine-chart formulation: reducedness is local on
  the chart scheme. A chart's map to Spec Ω is supplied by the second pullback projection.
- Connectedness including nonemptiness is the second conjunct:
  `ConnectedSpace (Point (Limits.pullback f.hom.hom y))`. The imported existing
  `pointTopologicalSpace` is the atlas topology. Mathlib's `ConnectedSpace` extends
  `PreconnectedSpace` and explicitly supplies `Nonempty`.
- The node's sentence defining “integral” is explanatory vocabulary; integrality is
  not among its assumptions. The Lean accordingly imposes neither irreducibility nor
  geometric integrality, and allows reducible connected geometric fibres.
- The original isomorphism is `IsIso (moduleStructureMap f)`. The recorded map has
  source `SheafOfModules.unit Y.structureSheaf` and target
  `(moduleDirectImage f).obj (SheafOfModules.unit X.structureSheaf)`.
  It is fixed by pullback of regular functions on every chart; it is not an arbitrary map.
- The universal clause quantifies over every `(T : AlgebraicSpace S) (g : T ⟶ Y)`.
  Its source space is the existing `enlargedFibreProduct f g`, owned by
  `def-sfb-space-sheaf-fibre-product`. Its underlying sheaf is exactly
  `Limits.pullback f.hom g.hom`. Its map to T is
  `ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)`, hence precisely f_T.
  The conclusion is `IsIso (moduleStructureMap ...)` for this projection. In particular,
  T is not restricted to schemes, etale maps, flat maps, or nonempty spaces.
- The small etale structure sheaves and `moduleDirectImage` are exactly those in the
  dependency modules. Tensor pullback is their existing left adjoint and does not occur
  in either conclusion, so no independent functor or comparison is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and its small etale site, structure sheaf and module category.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImage`, `ModuleDirectImageModel`, its chart-limit normalization,
  `moduleTensorPullback`, and `moduleTensorAdjunction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsProper`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, and their constituents.
  `MapIsQuasiCompact` is reused through this module, not redefined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`:
  `moduleStructureMap` and its unique regular-function chart characterization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`, with the existing
  `pointTopologicalSpace` final topology for all representable etale scheme maps.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `enlargedFibreProduct`,
  the existing bundled sheaf fibre product owned by `def-sfb-space-sheaf-fibre-product`.
  Read both this definition and `enlargedFibreProductFst` in full. The second projection
  in the signature has precisely `enlargedFibreProduct f g` as source.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` remains a proof dependency, imported privately.
- Mathlib: `AlgebraicGeometry.IsReduced`, `IsAlgClosed`, and `ConnectedSpace`.

The recorded proof modules `AlgebraicSpaceFlatProperFpLocality` and
`SpaceProperFieldGlobalFunctions` are imported privately, as is the fibre-product
closure theorem module. `EnlargedEtaleRingedSite` is public because its existing
`enlargedFibreProduct` definition occurs in the statement. The proof dependency
`lem-sfb-space-proper-flat-h0-criterion` has no Lean record or mathlib match in the read
repository, so there is no recorded module to import. Its theorem is not needed to type
this stage-2 statement. All three proof steps, with the dependency ids and mathematical
argument, are retained in the theorem docstring for stage 3.

Edge cases checked before writing:

- An empty geometric fibre is excluded by `ConnectedSpace.toNonempty`, as required.
  The empty target has no geometric points; the hypothesis is then vacuous, and both
  canonical maps are isomorphisms on empty spaces, including arbitrary base changes.
- Two disjoint points over an algebraically closed field fail connectedness; the false
  constants-to-product isomorphism is therefore not asserted.
- Spec of the dual numbers is connected and nonempty but not reduced, so the reduced
  chart test excludes it. Connectedness alone is not being substituted for the hypothesis.
- Reduced connected reducible proper fibres (e.g. nodal unions) are allowed; no
  irreducibility or smoothness is silently required.
- All characteristics, the identity base change, and empty or nonschematic T are included.
  All universes and variables are explicit. Fields have universe u, the same as the
  scheme test universe, rather than a smaller independent universe. This is the existing
  algebraic-space size convention and includes algebraic closures of residue fields.

Searches actually run, with their results:

- `msearch.py ... leanfinder` query “Proper flat finitely presented morphism of algebraic
  spaces with reduced connected geometric fibres has universally isomorphic structure
  sheaf pushforward”: 8 hits, including `UniversallyOpen.of_flat`, scheme `Flat`, and
  scheme flat-descent results; none is the algebraic-space statement.
- `msearch.py ... leansearch` query “proper flat algebraic spaces reduced connected
  geometric fibres structure sheaf pushforward universally isomorphic”: 8 hits on
  scheme module pushforward, scheme properness and ideal sheaves; none is this statement.
- `msearch.py ... loogle` query `AlgebraicGeometry.AlgebraicSpace, IsProper, IsIso`:
  zero hits, with unknown identifier `AlgebraicGeometry.AlgebraicSpace` in Mathlib.
- `msearch.py ... grep` query
  `geometrically.*(connected|reduced)|proper.*flat.*(sections|pushforward)` in
  `AlgebraicGeometry`: 24 hits on scheme geometric properties and group schemes, no
  algebraic-space universal-functions result.
- `rg` with `geometric.*[hH]0|geom.*[Rr]educed.*[Cc]onnected|structureMap.*[Ii]so|moduleStructureMap`
  in `lean/WeilConjectures` and `lean/Sheaf` found the existing canonical module map,
  the proper-field theorem, and the scheme-only `ProperFlatGlobalSections` theorem.
  Read their signatures: the latter quantifies over schemes and Zariski module
  adjunction units, so it does not state this theorem for algebraic spaces.
- Search for `lem-sfb-space-geometric-h0` in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`: no matches. Search for the proposed theorem name,
  `isIso_moduleStructureMap`, and `geometricH0` found no existing declaration.

No new notion, dependency repair, statement correction, or disputed statement remains.

Validation: `scompile.py O4 lem-sfb-space-geometric-h0` compiled the delivery in both
sandbox and library module modes (1.9 s and 2.0 s), with no errors or warnings.

## Second reading by O4

This is a separate rereading by the same worker; the dispatcher prohibits starting other
agents and the maintainer performs the independent review. I reopened the node, source
Tag 0E0S and final module. The named f and all three morphism properties agree. The
geometric-point binders cover every map from an algebraically closed field spectrum over
S; the repeated fibre expressions use the same y, and reducedness and nonempty
connectedness apply to that same actual fibre. No irreducibility is added. Both conclusions
name `moduleStructureMap`, and the universal one uses the second projection onto T,
with the existing `enlargedFibreProduct f g` as source. Unfolding that definition gives
exactly the sheaf pullback and its closure proof. Arbitrary T, the identity and empty cases remain
included. The signature has no hidden let, unbound variable, chosen comparison or new
definition. No mismatch or mathematical change was found in this rereading.

## Repair of returned head 3bf88cc3f734

H2/H4: the original delivery inlined the data already defined by `enlargedFibreProduct`.
Read the landed `def-sfb-space-sheaf-fibre-product` node and its existing declarations
in `EnlargedEtaleRingedSite.lean`. Replaced the theorem statement dependency
`lem-trf-space-fibre-products-etale-covers` with
`def-sfb-space-sheaf-fibre-product`. The theorem remains in `proof_deps` and
`tool_uses`, unchanged. Added public import `EnlargedEtaleRingedSite`; the direct
fibre-product theorem import is now private. The base-change arrow is the actual
`ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)` with source
`enlargedFibreProduct f g`, exactly the alternative requested in the return.
Updated the theorem docstring, the signature copied into `lean.statement`, and the
clause audit above. This changes the interface's definition ownership without changing
any mathematical hypothesis or conclusion. Re-read the final signature against the
return: there is no inline bundled pullback and no theorem statement dependency for
that definition. The current main node still has no Lean record; its non-Lean fields
are retained, with only the four authorized landed statement dependencies added.
The delivery wrapper refreshes its base to current main when creating the commit.

Repair validation: `scompile.py O4 lem-sfb-space-geometric-h0` compiled the repaired
file in sandbox mode (1.9 s) and library mode (1.8 s), with no errors or warnings.
Checked exact equality of `lean.statement` with the file signature, the swapped
statement dependency, retained proof/tool dependencies, and 100-character Lean lines.
