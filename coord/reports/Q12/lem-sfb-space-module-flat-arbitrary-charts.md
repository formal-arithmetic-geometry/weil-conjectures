## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleFlatArbitraryCharts` states
`AlgebraicGeometry.AlgebraicSpace.module_flat_some_iff_every_chart`, with its proof
postponed by `sorry`. There are no new definitions or extra theorem obligations.
I read Stacks `spaces-morphisms.tex`, `lemma-flat-at-point` (Tag 05VU), including
its proof: that proof compares each arbitrary compatible chart with a fixed
geometric stalk. This gives exactly the node's some-versus-every formulation.
There is no statement correction or STATEMENT-DISPUTED flag.

Hypothesis and conclusion correspondence:

- The scheme S is `{S : Scheme.{u}}`. The arbitrary algebraic spaces over S are
  `{X Y : AlgebraicSpace S}`; the morphism is `(f : X ⟶ Y)`.
- The quasi-coherent small-etale structure-module is `(M : X.QCoh)`.
  Its underlying module is `M.obj`; QCoh is the existing full subcategory for
  `SheafOfModules.IsQuasicoherent`, with no finite-presentation restriction.
- The fixed point is `(x : Point X.obj.obj)`, the recorded field-valued point
  quotient, with the recorded final topology available from PointTopology.
- An arbitrary representable etale scheme chart a is `(U : X.EtaleSite)`.
  Its scheme over S is `U.obj.left` and its presheaf map is `U.obj.hom`.
  The object's property is precisely `IsEtale U.obj.hom`, including
  representability. Likewise `(V : Y.EtaleSite)` encodes b with its etaleness.
  Every diagram in the node gives these objects, and conversely; neither type
  includes a surjectivity condition.
- `(h : U.obj.left ⟶ V.obj.left)` is a morphism of schemes over S. The square
  `fa = bh` is `U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom`.
- The chart point is `(u : X.etaleForget.obj U)`. Its image condition is
  `schemePointMap U.obj.hom u = x`, using the existing residue-field point map.
- The Zariski module F corresponding to a^*M is
  `((X.schemeRestriction U).obj M.obj)`. This is the existing canonical
  restriction to open subschemes: on an open W in U it evaluates M on
  `W.toScheme → U → X`, with the canonical regular-function scalar comparison.
  Etale pullback is restriction to the localized etale site, and the inverse
  of the recorded Zariski/etale quasi-coherent equivalence is restriction to
  opens. Consequently their composite is exactly this functor; no arbitrary
  isomorphism, chosen module, or surrogate pullback is assumed.
- The ordinary Zariski stalk F_u is the object of
  `RingedSpace.moduleStalkFunctor (X.etaleForget.obj U).toRingedSpace u`.
  This wrapper has the same Mathlib underlying abelian-group stalk and germ
  scalar action as the recorded `PresheafOfModules.moduleStalkFunctor`.
- The base local ring is `V.obj.left.left.presheaf.stalk (h.left u)`, exactly
  O_{V,h(u)}. `ModuleCat.restrictScalars (h.left.stalkMap u).hom` restricts
  the ordinary O_{U,u}-action along the actual stalk homomorphism of h.
  `Module.Flat` of this restricted module is the exact tensor-flatness
  predicate, not flatness of h or of the ring map itself.
- The left side of `↔` existentially quantifies U, V, h, u and conjoins the
  square, image and flatness conditions. The right side universally quantifies
  those same data, with square and image as antecedents and flatness as the
  conclusion. No global relative-flatness condition is substituted for the
  assertion at the specified point.
- The arbitrary universe u is shared with the established algebraic-space
  site convention: all test schemes are Scheme.{u}, points have Type (u+1).
  There is no universe equality imposed on a second site, and no finiteness,
  separation, Noetherian, flatness, or chart-surjectivity assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom` (inherited through the public space import).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `etaleForget`, `Modules`, and `etalePullback`. These give the
  actual fppf-sheaf space, representable chart maps, and small-etale modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace`; its imported `AlgebraicSpacePointClasses` provides
  `Point` and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`,
  `zariskiEtaleModuleRestriction`, and `ZariskiEtaleModuleContext.restriction`.
  Restriction to opens is the specified inverse direction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorAdjunction`; their canonical etale
  specialization is restriction, as explained above. The statement uses the
  composite restriction functor rather than choosing a left adjoint again.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`:
  `schemeRestriction`, `schemeOpens`, `schemeOpensRingHom`. The already landed
  node `def-trf-space-module-scheme-restriction` was added to stmt_deps to cite
  this precise existing construction. Its node and module are not changed.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj` (ordinary Mathlib stalks).
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` supplies the equivalent
  existing `RingedSpace.moduleStalkFunctor` wrapper used in the signature.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `Module.Flat`; the latter
  is the predicate used for module flatness, as this dependency's node states.

The modules of recorded proof dependencies are also imported:
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (`AlgebraicClosure`,
`IsAlgClosed`); `Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness`
(`strictLocalChartComparison`, `geometricStalk_flat_iff`);
`WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat`
(`Scheme.strictHenselization_faithfullyFlat`);
`Sheaf.RingTheory.FlatnessFaithfullyFlatExtension`
(`Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension`); and
`Sheaf.RingTheory.StrictHenselizationModuleFlatness`
(`Module.flat_iff_strictHenselization`). The three proof-only nodes
`lem-sfb-unramified-etale-compatible-charts`,
`lem-sfb-etale-geometric-point-specified-lift`, and
`lem-sfb-space-quasicoherent-geometric-stalk-tensor` have no recorded declaration
in the read repository; their imports are therefore omitted under the rule
requiring imports for proof dependencies that are stated. Their future proof
interfaces are not needed to type this statement. The docstring retains each
of the node's four proof steps, including their references and the scalar-action
compatibility in the tensor comparison.

Edge cases checked mathematically before writing:

- Empty X admits no x. An empty U, or a chart missing x, has no point satisfying
  the antecedent and contributes no false existence assertion.
- Charts are not assumed surjective; for any x there nevertheless is a
  compatible pair of atlases and a point over x. This existence is needed in
  the universal-to-existential implication and is explained in proof step 1.
- The zero module is flat over every indicated ring, on both sides.
- With f the identity and identity charts of a scheme, the condition reduces
  to ordinary flatness of M_x over O_{X,x}.
- A closed point included in affine one-space with its residue-field module
  gives a nonflat stalk over the base DVR. Both quantified conditions are
  false; no accidental assumption makes all modules flat or requires h flat.
- Arbitrary non-Noetherian local rings and quasi-coherent modules with infinite
  presentations remain permitted. The strict-henselization argument uses no
  finite-generation or Nakayama hypothesis.

Searches actually run:

- `msearch.py ... leanfinder` query: `Relative flatness of a quasi-coherent
  module on an algebraic space is independent of compatible etale source and
  target scheme charts at a fixed point`. Eight results:
  `Flat.stalkMap`, `Flat.instHasRingHomPropertyFlat`,
  `Flat.isStableUnderBaseChange`, `flat_iff`, `Flat.iff_flat_stalkMap`,
  `Flat.of_stalkMap`, `Flat`, `Flat.instIsMultiplicativeScheme`.
  All concern scheme morphism flatness; none states this module/chart result.
- `msearch.py ... loogle 'Module.Flat, AlgebraicGeometry.Etale'`: zero hits.
- `msearch.py ... grep 'flat.*(chart|etale)|((chart|etale).*flat)'
  AlgebraicGeometry`: eleven hits in WeaklyEtale, LocalFlatDescent, and Etale;
  all concern scheme/ring morphisms, with no exact result.
- `rg` of `lean/WeilConjectures` for this node id: no hits.
- `rg` of `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures` for
  flat/chart combinations: existing scheme-chart results, global
  `ModuleIsFlatOver`, and `SpaceStrictLocalFlatness.flatAt_iff_chart_stalk`
  concern other statements (global flatness or flatness of the morphism).
  Neither duplicates the present module-at-a-point equivalence.
- Searches for chart restriction found `AlgebraicSpace.schemeRestriction`,
  already carried by `def-trf-space-module-scheme-restriction`; it was reused.
  Sibling nodes `lem-sfb-space-module-flat-point-chart-independence` and
  `lem-sfb-space-module-flat-chart-test` have scheme targets and no Lean record;
  they do not cover this algebraic-space-target statement.

Validation: scompile.py compiled the single delivered file in its sandbox and
library forms against the live server build, both clean (1.9 seconds each).
The only changes to the node are its Lean record and addition of the already
landed canonical scheme-restriction dependency. No live source was edited.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
