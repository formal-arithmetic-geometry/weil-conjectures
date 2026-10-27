## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_dense_scheme_open`, with its sole proof `sorry`.
It changes only the item's `lean` record; the accepted split and statement are preserved.
The old worker ending concerned a stage-1 unchanged-item gate, not this stage-2 work:
coord/brief-stage2.md §0 expressly authorizes continuing through deliver2.py.
No repair note exists for this item. The example CompactObject module is withdrawn and
contains no declarations; the module follows the required module/public-import/expose
convention and the current algebraic-space statement modules instead.

Hypotheses and conclusions, clause by clause:

- An arbitrary scheme S is `{S : Scheme.{u}}`, using Mathlib's Scheme unchanged.
- An algebraic space Y over S is `(Y : AlgebraicSpace S)`, using exactly the recorded
  fppf-sheaf/full-subcategory definition, including its representable diagonal and atlas.
- The relative diagonal Y → Y ×_S Y is
  `prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)`. Products of presheaves on Over S are relative
  products over S: every presheaf here has its unique structure map to terminal h_S.
  No absolute quasi-separatedness of Y or of S is assumed.
- Quasi-compactness on every scheme test is `hqs : IsRepresentableWith
  (fun _ _ p ↦ QuasiCompact p.left) ...`. This expands to each T over S and each
  h_T → Y ×_S Y having a representing scheme pullback with quasi-compact projection.
  Mathlib's QuasiCompact is exactly compactness of inverse images of compact opens.
  The existing diagonal representability means this is the stated property, not an
  added representability hypothesis. Projection properties are isomorphism invariant.
- The existential scheme V over S is `(V : Over S)`; V.left is the scheme and V.hom its
  structural map. The map `j : yoneda.obj V ⟶ Y.obj.obj` is a natural transformation
  on Over S, hence a morphism over S, as the node requires.
- The open immersion condition is `IsRepresentableWith
  (fun _ _ p ↦ IsOpenImmersion p.left) j`, exactly all scheme base changes being open
  immersions. It uses the dependency's scheme-open-immersion predicate, without a copy.
- The canonical underlying map |V| → |Y| is `schemePointMap j`, defined by the existing
  residue-field representatives, into Point Y.obj.obj with its existing atlas topology.
- Identification homeomorphically with an open subset is
  `Topology.IsOpenEmbedding (schemePointMap j)`: an embedding with open range.
- Density is `DenseRange (schemePointMap j)`, i.e. the closure of its range is all of
  Point Y.obj.obj. Together the last two clauses say exactly open dense image with its
  induced topology. They do not substitute scheme-theoretic density or universal density.
- There is no compactness, finite-type, Noetherian, separated-base, nonemptiness or
  characteristic assumption. The one explicit universe u is the dependency's size
  convention for schemes and test schemes; the point classes live in Type (u+1),
  exactly as the existing Point definition prescribes. Auto-implicits are disabled.

Statement dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace and
  AlgebraicSpace.IsRepresentableWith, with their full definitions and docstrings.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace; its
  public dependency AlgebraicSpacePointClasses provides Point and schemePointMap.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact supplies the scheme QuasiCompact
  predicate; Mathlib.Topology.Maps.Basic supplies IsOpenEmbedding and dense-range API.

The recorded proof modules are imported privately: AlgebraicSpaceEtaleOpenImage,
AlgebraicSpaceAffineAtlasOpenCover, AlgebraicSpaceFibreProductsEtaleCovers, and
SeparatedEtaleChart. Mathlib proof leaves are imported from Pullbacks, AffineScheme,
Morphisms.QuasiSeparated, Morphisms.FinitePresentation, Morphisms.Separated and
Morphisms.ClosedImmersion, including QuasiCompact already publicly imported.
Their recorded names include pullbackSpecIso, Scheme.compactSpace_of_isAffine,
quasiSeparatedSpace_of_isAffine, quasiCompact_of_compactSpace,
QuasiSeparated.of_quasiSeparatedSpace, the base-change permanence instances,
Scheme.instIsSeparatedOfIsAffine, Scheme.instIsSeparatedOfIsSeparated, and
IsClosedImmersion.isStableUnderBaseChange. The other proof nodes currently have no
recorded Lean modules, so there is nothing to import for those yet; none is needed to
state this theorem. The docstring preserves all six proof steps and their named inputs.

Edge cases checked before writing:

- Empty Y: take empty V over S; its map has empty range in an empty point space,
  which is both open and dense, and is an open embedding. No Nonempty binder occurs.
- Y already a scheme, even one not quasi-compact: identity is a possible dense open;
  the statement imposes no quasi-compactness on V or j.
- An arbitrary non-quasi-separated base S remains permitted; the hypothesis is on
  Y's relative diagonal, and the proof reduces locally on affine base opens.
- Disconnected spaces and infinitely many components are allowed. Density is tested
  on all nonempty opens, with no irreducibility, generic-point or finite-component claim.
- The diagonal hypothesis is not the tautological quasi-compact identity: it is the
  map into the product presheaf and requires quasi-compact equality loci on tests.

Searches for an existing statement (2026-10-23):

- msearch.py leanfinder: "A relatively quasi separated algebraic space over a scheme
  has a dense open subspace represented by a scheme". Eight results, all concerning
  quasi-separated schemes (e.g. QuasiSeparated.of_quasiSeparatedSpace), not the theorem.
- msearch.py loogle: `"AlgebraicSpace"`. Zero hits.
- msearch.py leansearch: "A quasi separated algebraic space has a dense open subscheme".
  Eight results concerning quasi-separated schemes and their diagonals; no match.
- msearch.py grep: `dense.*open.*scheme|open.*dense.*scheme|AlgebraicSpace` in
  AlgebraicGeometry. Ten scheme-birational/rational-map hits; no algebraic-space result.
- rg of the same dense/open patterns and the node id in lean/WeilConjectures and
  lean/Sheaf found only scheme statements and a schematic-closure theorem for a given
  open; no theorem constructing a dense open scheme in an algebraic space.
- rg in the upstream name index and algebraic-space modules found no
  exists_dense_scheme_open or competing dense schematic-locus theorem. Read the
  actual algebraic-space, point-class, topology and open-immersion declarations.

Source checked directly: literature/stacks-project/decent-spaces.tex,
theorem-decent-open-dense-scheme (Tag 086U), lemma-bounded-fibres (Tag 03JX).
The relative-to-affine-base reduction remains the accepted node's explicit proof.
No statement correction, new node, dependency-interface replacement, or disputed
statement is necessary.

Validation: scompile.py compiled this file both as a sandbox module and with its final
library module name, cleanly (8.0 s and 9.0 s). No errors or warnings were emitted.

## Second reading by Q74

Sequential self-check of the complete node and final Lean signature: the sole geometric
hypothesis is the relative quasi-compact diagonal on all scheme tests; the witnesses are
an actual scheme over S and its Yoneda map; the three conclusion conjuncts are scheme-test
open immersion, open topological embedding, and dense range of the existing canonical
point map. There are no implicit base finiteness or nonempty assumptions. Product in
presheaves on Over S correctly denotes Y ×_S Y. The empty-space case is retained.
No mismatch was found and no statement was changed. This is a self-check, not a claimed
independent worker review; the dispatch forbids spawning agents and assigns independent
review of this delivery to the maintainer.
