## Worker report

The module `Sheaf.AlgebraicGeometry.ZeroDimensionalFieldSpaceComponents` states
`AlgebraicGeometry.AlgebraicSpace.zeroDimensional_fieldSpace_components`, with the sole
proof `sorry`. No definitions, auxiliary theorems, new nodes, dependency repairs, or
statement corrections are introduced. The item's node changes only in `lean`.

Sources read: Stacks `spaces-over-fields.tex`, Tag 06LZ,
`lemma-locally-finite-type-dim-zero`, the statement and proof of case (2); and
`varieties.tex`, Tag 06LH, `lemma-algebraic-scheme-dim-0`, the statement and full proof.
The source's dimension-zero assertion is used in its dimension-at-most-zero form as
already specified by the item, allowing the empty space. The docstring follows all ten
recorded proof steps, naming their dependencies, including the kernel-pair finiteness
argument that avoids imposing quasi-separatedness.

Every hypothesis and clause is rendered as follows:

- The field K is `{K : Type u} [Field K]`; its characteristic is unrestricted.
- X over Spec K is `X : AlgebraicSpace (Spec (CommRingCat.of K))`, the existing full
  subcategory of fppf sheaves, with representable diagonal and an étale surjective atlas.
- Local finite type tested on étale scheme charts is `hft`: for every `U : Over (Spec K)`
  and `p : yoneda.obj U ⟶ X.obj.obj`, `IsEtale p → LocallyOfFiniteType U.hom`.
  The recorded `IsEtale` already includes representability; no extra condition is needed.
- The supplied definition of dimension makes `dim X ≤ 0` equivalent to the bound on
  the local dimension of every point of every étale chart. This is `hdim`, ending
  `∀ v : U.left, topologicalKrullDimAt v ≤ 0`. The upstream definition of
  `topologicalKrullDimAt` is literally the infimum over open neighbourhoods of their
  topological Krull dimensions. This is not the Krull dimension of the local ring.
  Expanding the node's own dimension convention avoids inventing another dimension
  definition or assuming chart-independence as a hypothesis.
- Scheme representability, retaining the K-structure, is
  `∃ Y : Over (Spec K), Nonempty (yoneda.obj Y ≅ X.obj.obj) ∧ ...`.
  The isomorphism is of the actual functors on schemes over Spec K.
- Absolute separatedness is
  `IsClosedImmersion (prod.lift (𝟙 Y.left) (𝟙 Y.left))`, the diagonal to the
  categorical product of schemes. This is the diagonal over the terminal scheme
  Spec Z, rather than a diagonal over K. Mathlib's
  `Scheme.isSeparated_iff_isClosedImmersion_prod_lift` identifies this with
  `Y.left.IsSeparated`.
- Every quasi-compact open subscheme is affine is exactly
  `∀ V : Y.left.Opens, IsCompact (V : Set Y.left) → IsAffine V.toScheme`.
- The possibly infinite disjoint union is expressed by `I : Type u`, a family
  `A : I → CommAlgCat.{u} K`, and morphisms
  `ι : ∀ i, Spec (CommRingCat.of (A i)) ⟶ Y.left`, with
  `Nonempty (IsColimit (Cofan.mk Y.left ι))`. This is the categorical coproduct
  universal property for those very inclusions, not an unrelated abstract isomorphism.
- Each component ring is explicitly `Nontrivial (A i)`, `IsLocalRing (A i)`,
  `IsArtinianRing (A i)`, and `FiniteDimensional K (A i)`. These are the usual ring
  notions: a unique maximal ideal and the descending chain condition on ideals.
- The component K-structures are matched by
  `ι i ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K (A i)))`.
- Components are open and closed subschemes: `IsOpenImmersion (ι i)` and
  `IsClosed (Set.range (ι i))`. An open immersion with closed image is the inclusion
  of a clopen subscheme, including its induced scheme structure.
- The one-point assertion is `Subsingleton (Spec (CommRingCat.of (A i)))` together
  with the nonzero local-ring assertions, which ensure nonemptiness. Precisely the
  connected components is
  `∀ x : Y.left, ∃! i : I, Set.range (ι i) = connectedComponent x`.
  This also explicitly ensures every connected component occurs once.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, full signature and
  docstring at line 170 onwards (class at 180).
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, especially
  `AlgebraicGeometry.AlgebraicSpace`, `.IsAlgebraicSpace`, `.IsRepresentableWith`,
  `.IsRepresentable`, and `.IsEtale`. These are used directly, with no copied notion.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (signature/docstring at 39–46), and its
  imported `AlgebraicGeometry.QuasiCompact` for the proof plan.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (docstring and fields at 42–46).
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (docstring and body at 34–39).
- Existing local dimension: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt` (docstring and body at 341–345). The landed node
  `def-kun-dimension` records this declaration; no new notion is needed because
  the item's dimension convention is already explicit and is expanded inline.
- Component algebras and topology use Mathlib `CommAlgCat`, `FiniteDimensional`,
  `IsLocalRing`, `IsArtinianRing`, `connectedComponent`, and `Cofan.mk` / `IsColimit`.

Recorded proof modules are imported privately: `DimZeroFiniteOverField`,
`EtaleSchemeMapOpenImage`, `FiniteFlatAffineRelationQuotient`,
`RepresentableEtaleFppfLocalLifting`, `AlgebraicSpacePointOpenCalculus`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` and
`WeilConjectures.AlgebraicGeometry.SeparatedAffineCoverCriterion`, together with
Mathlib's Artinian, universally injective, pullback, gluing and scheme coproduct modules.
Their recorded theorem signatures were read; the point/open calculus is needed in the
representability argument rather than the final statement. The proof dependency
`lem-sfb-space-largest-schematic-open` has no recorded declaration or Mathlib match;
there is no module to import yet. It is not needed to type this statement and its
future import belongs to the maintainer's proof-import propagation.

Edge cases checked mathematically before writing:

- Empty X: the dimension/chart hypotheses are vacuous on empty charts, the representing
  scheme can be empty, and the component index I can be empty. No `Nonempty I` or
  nonempty-space assumption appears. The empty open is affine.
- Infinitely many points: no `Finite I`, quasi-compactness of X, Noetherian X, or
  quasi-separatedness hypothesis appears. The index universe equals the universe of
  chart-scheme points; the existence of an atlas ensures this is sufficient for all
  components, including an arbitrary set in the project's size convention.
- Nilpotent rings, e.g. K[ε]/(ε²), are allowed; neither reducedness nor field-valued
  component rings is imposed. Nontrivial local Artinian rings have a nonempty singleton
  prime spectrum, so the Subsingleton clause means exactly one point.
- Arbitrary residue-field extensions allowed by finite dimension are retained; K is
  neither assumed algebraically closed nor perfect, and no characteristic is excluded.
- Absolute separatedness and the coproduct assertion allow infinite covers and the
  empty cover. No finite coproduct or global affineness conclusion is imposed.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` query: "A zero dimensional algebraic space locally of
  finite type over a field is a separated scheme and a disjoint union of spectra of
  local Artinian finite dimensional algebras". Eight hits: Mathlib `IsArtinianScheme`,
  `IsLocallyArtinian`, the dimension-zero criterion, discrete topology and finiteness
  results. None is the algebraic-space representation/decomposition statement.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.IsLocallyArtinian, AlgebraicGeometry.Scheme.dim`.
  The service returned zero hits with "unknown identifier AlgebraicGeometry.Scheme.dim".
  The scheme dimension name is from upstream, not the Mathlib service index.
- `msearch.py ... grep` query `AlgebraicSpace|dimAt|localDimension` in
  `AlgebraicGeometry`: zero hits.
- `msearch.py ... grep` query `zero.*dim|dim.*zero|AlgebraicSpace` in
  `AlgebraicGeometry/Artinian.lean`: five hits including
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`; these concern schemes only.
- `rg` of project `lean/Sheaf` and `lean/WeilConjectures` for dimension/local dimension,
  the item id, and zero-dimensional-space/component patterns found no exact theorem.
  It found the existing scheme dimension-zero theorem and upstream local-dimension
  definition, which are used rather than copied. A structured scan of DAG definition
  statements found `def-kun-dimension` for the already-existing local dimension.

Validation: required `scompile.py Q96 lem-sfb-zero-dimensional-field-space-components`
compiled the file in both sandbox and final library module mode on the server, cleanly
(11.2 s and 8.1 s). No errors or warnings. The only postponed proof is the item's named
theorem. No STATEMENT-DISPUTED condition or node fault was found.

## Second reading by Q96

Worker rereading, not an independent reviewer: I reopened the completed module and matched
it to the node. Both chart hypotheses quantify over all `Over (Spec K)` objects and
all representable étale maps, without requiring the individual chart to be surjective.
The representing object is over K, and each component inclusion commutes with its
specific algebra structure map. The closed-immersion clause uses the absolute product,
not a relative product over K. The open-affineness quantifier includes the empty open.
The coproduct is unrestricted in cardinality, while all component rings are nonzero;
the final uniqueness quantifier identifies exactly all connected components. There is
no new statement hypothesis and no missing conclusion. No changes were needed after
this comparison. The maintainer's independent reading remains the delivery review,
as specified by the dispatcher brief; no other agent was started.
