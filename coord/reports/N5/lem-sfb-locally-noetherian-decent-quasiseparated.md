## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyNoetherianDecentQuasiSeparated` states
`AlgebraicGeometry.AlgebraicSpace.isAbsolutelyQuasiSeparated_of_locallyNoetherian_of_decent`.
Its only theorem has proof `sorry`; no definitions or auxiliary theorems are added.

Read the node, all six original statement dependencies and their recorded source declarations,
Stacks `decent-spaces.tex:3272–3325`, Tag 0BB6, and the existing absolute quasi-separatedness
node and module. Hypotheses and clauses match as follows:

- Algebraic space over Spec Z: `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  `ULift` puts the integers in the same arbitrary universe as the schemes; it does not
  restrict them to small schemes. This uses `AlgebraicGeometry.AlgebraicSpace` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`, through the public fibre-products import,
  and `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme`.
- Every representable étale scheme mapping to X is locally Noetherian:
  `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)`.
  `EtaleSite` is exactly the full subcategory of scheme-source maps satisfying
  `IsEtale`; `etaleForget` returns the source scheme. `IsLocallyNoetherian` is the
  recorded class from `Mathlib.AlgebraicGeometry.Noetherian`, defined using all affine opens.
  Mathlib's affine-cover characterization gives the node's equivalent definition.
- Every field L and map Spec L → X: the binders `(K : Type u) [Field K]`, its base
  structure map `b`, and natural transformation `c`. `Field` is Mathlib's declaration
  (`Mathlib.Algebra.Field.Defs:180`). No algebraic closure, characteristic or finite
  extension restriction is imposed. The structure map is unique over Spec Z.
- Every affine scheme mapping to X: `U : Over ...`, `IsAffine U.left`, and arbitrary
  `a : yoneda.obj U ⟶ X.obj.obj`, without any étaleness requirement on `a`.
- Its pullback is a quasi-compact scheme: witnesses `W,p,q`, the presheaf cartesian
  square `IsPullback q (yoneda.map p) c a`, and `CompactSpace W.left`.
  The square is an actual representation of the specified sheaf fibre product, not
  an unrelated compact scheme. The algebraic-space diagonal already ensures scheme
  representability. CompactSpace is quasi-compactness without a separation condition
  (`Mathlib.Topology.Defs.Filter:283`). This is the same field-map formulation used
  in the existing `DecentSpaceFiniteFieldMap` module, whose full signature was read.
- Absolute diagonal quasi-compactness: `IsAbsolutelyQuasiSeparated X`, from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`. Its definition is
  the all-affine-pairs criterion, equivalent to the absolute diagonal criterion by
  Stacks Tag 0AHR. Added its already-landed owning node
  `def-sfb-space-absolute-quasi-separated` to stmt_deps under the stage-2 landed-node rule.
  No new definition node or second definition is needed.
- Equivalent affine étale-pair clause: the second conjunct quantifies over both
  affine schemes `U,V`, maps `a,b` and `IsEtale a`, `IsEtale b`; it gives a scheme
  `W`, projections `p,q`, the representing square
  `IsPullback (yoneda.map p) (yoneda.map q) a b`, and `CompactSpace W.left`.
- No quasi-compactness, finite-type, separatedness or finite atlas assumption on X
  occurs. Scheme fibre products are represented using the existing Yoneda/square API.

Dependency interfaces read: `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`,
`IsEtale`, `IsAlgebraicSpace`, `EtaleSite`, `etaleForget`; the three declarations
`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`; Mathlib `Spec`,
`Spec.map`, `IsLocallyNoetherian`, `Field`, `CompactSpace`; and the definition
`IsAbsolutelyQuasiSeparated` just named. All already-stated proof dependencies are
imported privately; two proof nodes currently have no declaration
(`lem-sfb-etale-affine-pairs-test-quasiseparated`,
`lem-sfb-flat-lfp-lqf-degree-superlevel-open`), so their imports await their statements.
The full seven-step DAG proof, with dependency ids and the corrected final covering
argument, is included in the theorem docstring for stage 3.

Edge cases: the empty space and empty affine tests are allowed, since CompactSpace
allows the empty space. Empty fibres have degree zero in the proof; the docstring
specifies maximum zero when U is empty, and does not identify W with a coproduct
of its locally closed strata. Infinite disjoint unions of Noetherian components
are allowed: no compactness hypothesis on X was introduced. Fields and scheme tests
share universe u, so field-map quantification is not vacuous from a smaller test
universe. All variables and the universe are explicitly bound; autoImplicit is false.

Searches actually run using `batch2/msearch.py`, with outputs logged by that wrapper:

- LeanFinder: `A locally Noetherian decent algebraic space is quasi-separated`:
  eight hits, led by the scheme-only `IsLocallyNoetherian.quasiSeparatedSpace`;
  none concerns algebraic spaces or decency.
- Loogle: `AlgebraicSpace, IsLocallyNoetherian, QuasiCompact`: zero hits,
  unknown identifier AlgebraicSpace.
- grep: `decent|Decent|AlgebraicSpace` in Mathlib/AlgebraicGeometry: zero hits.
- LeanSearch: `A locally Noetherian decent algebraic space is quasi-separated`:
  eight hits about schemes or topological spaces, none the algebraic-space theorem.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  item id, decent/Decent, absoluteQuasi/AbsoluteQuasiSeparated and locally-Noetherian
  patterns. No existing statement found; found and reused the absolute predicate,
  locally-Noetherian EtaleSite binders, and field-map pullback format.

No statement correction, disputed statement, dependency repair or new node.
The node changes only in lean and the addition of the already-landed definition to stmt_deps.
First scompile passed in sandbox and library modes (1.6 s and 1.4 s) without warnings.

## Second reading by N5

A separate second pass by the same dispatcher worker compared the node and the full
Lean signature; the assignment prohibits starting other agents, and the maintainer's
independent delivery review remains required. No claim of another worker's review is made.
I checked X's integer base, every étale test in hln, every field and affine test in
hdecent, both orientations of the cartesian squares, and both conclusion clauses.
The hypothesis uses arbitrary affine maps, whereas the second conclusion uses étale
ones, exactly as the node requires. The first conclusion reuses the existing
all-affine criterion, which gives absolute diagonal quasi-compactness over Spec Z.
The existential pullback witness does not choose arbitrary data: its square identifies
it with the uniquely specified fibre product. No mathematical mismatch was found.
The final import pass replaced an unnecessary QuasiCompact import by the recorded
CompactSpace module and removed the redundant private AlgebraicSpace import, already
publicly supplied by the fibre-products module. No theorem signature changed.
