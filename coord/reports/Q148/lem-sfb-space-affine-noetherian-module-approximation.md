## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineNoetherianModuleApproximation` states
`AlgebraicGeometry.AlgebraicSpace.exists_finitePresentation_filtered_colimit_of_affine_noetherian`.
It has exactly one postponed theorem and no definitions or additional proof obligations.
The source is Stacks, Cohomology of Algebraic Spaces, Tag 07UW,
`lemma-direct-colimit-finite-presentation`, read in `literature/stacks-project/spaces-cohomology.tex`
at the lemma and its full proof. The docstring expands the nine steps of the accepted DAG proof,
including eventual equality in directedness and the colimit argument in all module sheaves.
No mathematical statement correction is needed.

Hypotheses and clauses, in order:

- The base scheme is `{S : Scheme.{u}}`; both spaces are `{X Y : AlgebraicSpace S}`;
  `(f : X ⟶ Y)` is their natural transformation. These are the recorded scheme and
  algebraic-space definitions, with the existing small etale structure sheaf.
- Affineness is `(ha : MapIsAffine f)`. Its definition quantifies over every affine
  `T : Over S` and every `yoneda.obj T ⟶ Y.obj.obj` and gives an affine scheme
  representing the full pullback square. It adds no finite-type assumption and
  requires no extra, separate representability hypothesis.
- Quasi-compactness of the target point topology is
  `(hqc : CompactSpace (Point Y.obj.obj))`, using the recorded final etale point topology.
- Quasi-compactness of the absolute diagonal on affine tests is
  `(hqs : IsAbsolutelyQuasiSeparated Y)`. The existing predicate is exactly the node's
  test: both charts affine, and the point space of their presheaf fibre product compact.
- Existence of a locally Noetherian atlas is `hln`: there exist `V : Over S` and
  `a : yoneda.obj V ⟶ Y.obj.obj` with `IsEtale a ∧ IsSurjective a ∧
  IsLocallyNoetherian V.left`. Both representability requirements are part of the
  existing `IsEtale` and `IsSurjective` predicates. No all-charts Noetherian hypothesis
  is substituted for existence of the one atlas.
- The given module is `(M : X.Modules) [M.IsQuasicoherent]`, using the dependency's
  actual module category and Mathlib local-presentation predicate.
- A small filtered category is `∃ (J : Type u) (_ : SmallCategory J)
  (_ : IsFiltered J)`. The chosen index bound agrees with the source's size convention
  and the landed consumer `exists_finitePresentation_filtered_colimit`.
  `IsFiltered` includes nonemptiness; it is not `IsFilteredOrEmpty`.
- The module diagram is `(D : J ⥤ X.Modules)`. Every term satisfies
  `(D.obj j).IsFinitePresentation ∧ (D.obj j).IsQuasicoherent`.
  Mathlib finite presentation is local cokernels of finite free modules, exactly
  the finite m,n presentation of the node. The explicit quasi-coherence conjunct
  is already implied by finite presentation but records the node's clause verbatim.
- Compatible maps into M are `ι : D ⟶ (Functor.const J).obj M`;
  naturality is precisely compatibility with all transition maps.
- Their colimit property is `Nonempty (IsColimit (Cocone.mk M ι))` in `X.Modules`.
  This asserts the universal property for all module sheaves, without replacing
  it by an arbitrary isomorphism or a colimit solely in the QCoh subcategory.
- There is no finite-type binder for f and no Noetherian binder for X.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` and its inherited `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  small-etale slice instances; the actual predicate is the same
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
  That Mathlib file's `QuasicoherentData`, `QuasicoherentData.IsFinitePresentation`,
  and `SheafOfModules.IsFinitePresentation` were read, including their docstrings.
- `Mathlib.CategoryTheory.Limits.HasLimits`: the recorded colimit interface;
  its underlying `Cocone` and `IsColimit` signatures and docstrings were read in
  `Limits/Cones.lean` and `Limits/IsLimit.lean`. `IsFiltered` was read in
  `Mathlib.CategoryTheory.Filtered.Basic`.
- `def-weil-size-convention` is the recorded metatheoretic convention with no
  declaration or import. All universes and variables are explicitly bound;
  `set_option autoImplicit false` enforces this.
- The two existing nodes added to `stmt_deps` are
  `def-sfb-space-affine-quasifinite-properties` (`MapIsAffine` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`) and
  `def-sfb-space-absolute-quasi-separated` (`IsAbsolutelyQuasiSeparated` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`). Both declarations
  and their node statements were read; neither notion is copied or redefined.

All recorded, stated proof-dependency modules are imported without `public`.
The following proof nodes have no recorded module in the read clone and therefore
supply no module import: `lem-sfb-space-affine-locality`,
`lem-sfb-qc-space-affine-etale-atlas`, `lem-sfb-space-qcoh-kernels-colimits`,
`lem-sfb-space-fp-module-hom-colimit`, `lem-weil-pbc-finite-type-over-noetherian`.
The ordinary scheme Noetherian/etale declarations needed by the last input are
already imported. The metatheoretic convention supplies no import either.
The point topology, colimit and etale definitions used in the signature or public
interfaces retain public imports.

Edge cases checked before writing:

- Empty X or Y is permitted; neither the atlas nor a scheme has a nonempty binder.
- The zero module is permitted, and finite free presentations allow ranks zero.
- A filtered category must be nonempty, including for the zero module: the singleton
  category supplies a diagram; an empty category is not silently allowed.
- Arbitrary affine maps remain covered: no finite type, finiteness, separation of S,
  Noetherianity of X, or characteristic assumption was added.
- Quasi-separatedness is absolute, not just relative to a possibly non-separated S.
- An arbitrary quasi-coherent M need not itself be finitely presented; only the
  diagram terms are. The colimit ranges over all module-sheaf test targets.

Searches for reuse:

- `msearch.py leanfinder`, query: "Every quasi coherent module on an algebraic space
  affine over a Noetherian space is a filtered colimit of finitely presented modules".
  Eight results concern `SheafOfModules.IsFinitePresentation`, local-presentation
  data, and module-sheaf colimit existence. None is the requested approximation theorem.
- `msearch.py loogle`, query: "SheafOfModules.IsFinitePresentation,
  CategoryTheory.IsFiltered". Successful search with zero hits.
- `msearch.py grep`, query: "AlgebraicSpace|[Nn]oetherian.*[Cc]olimit", subdirectory
  `AlgebraicGeometry`. Successful search with zero hits.
- `msearch.py leansearch`, query: "A quasicoherent sheaf on an algebraic space affine
  over a Noetherian space is a filtered colimit of finitely presented sheaves of modules".
  Eight hits are local-presentation predicates and their constructors/properties;
  none states the affine-Noetherian approximation.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, searching the item id and
  `affine.*noetherian.*[Aa]pprox|affine.*[Nn]oetherian.*[Cc]olimit`.
  The only item-id occurrence is the downstream proof docstring in
  `AlgebraicSpaceModuleFpDirectedApproximation.lean`; its theorem assumes qcqs X
  and uses this very item, so it cannot serve as an exact existing declaration.
- Topic searches in `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` and `Space*.lean`
  found the existing affine and absolute quasi-separated predicates and the
  finite-presentation interfaces, which are reused.
- `dag/lean_names_upstream.json` search for `ModuleFpDirectedApproximation`,
  `NoetherianModuleApproximation`, `affine_noetherian_module`: no match.

## Second reading by Q148

A separate rereading pass by this same worker (the dispatcher forbids starting
other agents) compared the source node and the complete Lean signature. It checked
the scheme/base-space binders; all three Noetherian clauses individually; the exact
MapIsAffine scheme-test definition; smallness and nonemptiness of J; finite presentation
and quasi-coherence of every term; naturality of the maps; and the all-module-sheaves
universal property. The point-space compactness applies to Y, not X. The atlas is
existential and is not required affine or finite type. No hypothesis restricts X to
being Noetherian. The colimit cocone has vertex M itself. No semantic mismatch was
found. The only record update beyond lean adds the two already landed definition
nodes needed to cite their canonical predicates; there are no new or repaired nodes.
