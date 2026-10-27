## Worker report

States `AlgebraicGeometry.AlgebraicSpace.isClosedMap_mapPoint_constructible` in
`Sheaf.AlgebraicGeometry.SpaceQuasiCompactConstructibleClosed`. Its only theorem proof is
`sorry`; its docstring reproduces the accepted five-step affine-chart proof, including
closed-subset compactness, the Hausdorff separation argument, and the point-lifting image
identity. No definition, additional theorem, or mathematical statement correction is made.

Hypothesis and clause correspondence:

- The arbitrary scheme base is `{S : Scheme.{u}}`. `universe u` is explicit, and
  `set_option autoImplicit false` rules out accidental implicit binders. Schemes and
  field representatives are in the existing site's universe u; `Point` has universe u+1,
  exactly as in the recorded point construction. There is no assumption on the base.
- `X Y : AlgebraicSpace S` are exactly the existing full subcategory of fppf sheaves with
  representable diagonal and a surjective representable etale scheme atlas. Their
  morphism is `f : X ⟶ Y`; `f.hom.hom` is its underlying natural transformation.
- The atlas point topology is the existing `pointTopologicalSpace`, inherited in the
  existing compactness predicates; no new topology or point type is introduced.
- The node's open-cover meaning of quasi-compact point space is Mathlib's `CompactSpace`,
  which does not impose Hausdorffness. `hf : MapIsQuasiCompact f.hom.hom` unfolds to all
  affine tests `(T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj)` with conclusion
  `CompactSpace (Point (Limits.pullback f.hom.hom a))`. This is exactly the sheaf
  fibre-product point-space definition in the node, including arbitrary tests.
- `hX : IsAbsolutelyQuasiSeparated X` and `hY : IsAbsolutelyQuasiSeparated Y` use the
  already recorded affine-pair criterion for the absolute diagonal. The definition's
  node explicitly identifies it with quasi-compactness of the diagonal over Spec Z
  (Stacks Tag 0AHR), so it does not assume relative quasi-separatedness of the given base.
- `pointConstructibleTopology X.obj.obj` and the analogous topology for Y are the final
  topologies of all representable etale affine scheme charts, with the existing compact-
  open/complement constructible topology on each affine chart. This exactly renders
  the node's scheme-local and algebraic-space constructible-topology conventions.
- The conclusion is `@IsClosedMap (Point X.obj.obj) (Point Y.obj.obj)` with those two
  explicit topologies and function `mapPoint f.hom.hom`. By the Mathlib definition this
  says, for every subset F, closedness in the source constructible topology implies
  closedness of its image in the target constructible topology. It imposes no continuity
  or surjectivity requirement as an additional conclusion.
- There are no finite-type, finite-presentation, properness, surjectivity, global
  quasi-compactness, representability-of-f, or extra separation assumptions.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and the
  recorded `IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`, `IsEtale`,
  `IsSurjective` interfaces. These are publicly available through the fibre-product module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  The quasi-compactness predicate uses their actual underlying presheaf pullbacks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `PointRepresentative.map`, `pointImage`; its point-class dependency supplies `Point`
  and `schemePointMap` with their residue-field representatives.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `mapPoint`, `MapIsQuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.SpaceConstructibleTopology`: `pointConstructibleTopology`.
- The size-convention dependency is metatheoretic, as its record says: explicit Lean
  universe parameters render it, with no object or declaration to import.

The last three owning definition nodes already landed and are added to `stmt_deps`, as
per brief-stage2 section 5 (STMT_DEPS MAY GAIN LANDED NODES):
`def-sfb-proper-curve-moduli`, `def-sfb-space-absolute-quasi-separated`, and
`def-sfb-space-constructible-point-topology`. They supply exactly the notions stated
inline by the original item. The natural-language statement and accepted proof stay
unchanged. No new node or dependency repair module is needed.

Proof-only imports cover all recorded proof dependencies having a Lean or Mathlib
interface: `AlgebraicSpacePointOpenCalculus.point_open_calculus` (namespace
`AlgebraicGeometry.AlgebraicSpace`), the five declarations in
`SpaceConstructibleTopologyComparison`, scheme affine compactness and quasi-separatedness
in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, scheme spectral parent instances
in `Mathlib.AlgebraicGeometry.Properties`, `isCompact_range` in
`Mathlib.Topology.Compactness.Compact`, `compactSpace_withConstructibleTopology` in
`Mathlib.Topology.Spectral.ConstructibleTopology`, and `t2Space_constructibleTopology` in
`Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff`. The affine-atlas proof node
`lem-sfb-qc-space-affine-etale-atlas` has no recorded module yet in the read clone, so
there is no module to import for it. It is only a proof dependency and supplies no part
of this signature. The maintainer can add that proof import when it lands.

Edge cases checked before writing: F empty, F the whole space, an empty source, and an
empty target (a morphism then forces the source point set empty). No inhabitedness is
assumed anywhere. Empty affine tests are admitted; the finite-subcover convention permits
an empty subcover. X and Y need not be globally quasi-compact. The base need not be
quasi-separated; both space hypotheses are absolute. None of these cases requires a
statement correction. No STATEMENT-DISPUTED issue was found.

Searches made (2026-10-24):

- `msearch.py ... leanfinder`: "A quasi compact morphism of quasi separated algebraic
  spaces is a closed map for the constructible topologies". Eight hits: scheme Chevalley
  `Scheme.Hom.isConstructible_image` requires local finite presentation; ordinary scheme
  closedness and scheme quasi-compactness results do not state this conclusion.
- `msearch.py ... leansearch`: "Quasi compact morphisms of quasi separated algebraic
  spaces are closed for their constructible topology". Eight hits, all scheme
  quasi-compactness/permanence or locally constructible-set results; no match.
- `msearch.py ... loogle`: `IsClosedMap, QuasiCompact`. Zero hits; the service reports
  unknown unqualified identifier `QuasiCompact`. The successful semantic searches and
  direct source searches provide the check independently.
- `msearch.py ... grep`:
  `IsClosedMap.*constructible|constructible.*IsClosedMap|pointConstructibleTopology`.
  Zero Mathlib matches.
- `rg` through `lean/WeilConjectures` for `constructible|Constructible`, and through
  `lean/Sheaf` for constructible topology, quasi-compactness, absolute quasi-separatedness,
  and the candidate declaration name. Found the existing definitions reused above and
  the related continuity/comparison node, but no theorem with this statement.
- The literal node-id search in `lean/WeilConjectures` gives no hit. The candidate full
  declaration name also has no hit in `dag/lean_names_upstream.json` or either library root.

Source checked: Rydh's author PDF,
https://davidrydh.se/papers/submersion20100305.pdf, Proposition (1.2)(ii), p.4, and
Remark (1.8), pp.6--7. The standing quasi-separatedness convention is on p.4. These
agree with this node. Read the current blueprint unit and direct-images proof under
`literature/blueprint/latest/` (main-20261024), preserving the item's recorded provenance.

Validation: prescribed `scompile.py NB lem-sfb-space-quasicompact-constructible-closed`
compiled the sandbox and final module names successfully (8.4 s and 1.4 s). No compiler
errors or unexpected warnings. No local build or direct shared-repository write was run.

## Second reading by NB

Reread the completed signature against the original node, independently of the proof
outline, and unfolded each of its three hypotheses and the two topology arguments in
the source. No hypothesis or conclusion mismatch found. In particular, the topology
arguments are explicitly constructible, absolute quasi-separatedness does not become a
relative diagonal condition, and `MapIsQuasiCompact` has exactly the required affine-test
point compactness. The only node changes are `lean` and the three existing owner-node
statement dependencies described above. The docstring contains all five accepted proof
steps and their dependencies. This is a single-worker rereading, not a claimed separate
agent review: the dispatcher explicitly forbids starting other agents, and the maintainer's
independent delivery review remains the independent review required by this assignment.
