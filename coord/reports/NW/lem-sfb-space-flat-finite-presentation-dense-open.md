## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatFinitePresentationDenseOpen` states
`AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_flat_of_denseOpen`.
It has one theorem with proof `sorry`, no definitions, and no added or repaired nodes.
The item's only changed field is `lean`.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-flat-finite-type-finitely-presented-over-dense-open-X` (Tag 0877), together
with its preceding module lemma (Tag 0876). The three enumerated hypotheses and
conclusion agree with the DAG. The theorem docstring includes the six proof steps
of the node, including the polynomial-module argument through Tag 081P.

Hypothesis and clause correspondence:

- `S : Scheme.{u}` is the base scheme. `X Y V : AlgebraicSpace S` are algebraic
  spaces over this same base, using the existing fppf-sheaf full subcategory.
  `universe u` is explicit and `autoImplicit` is disabled. No independent smaller
  test-scheme universe or equality of distinct site universes is imposed.
- `f : X ⟶ Y` and `j : V ⟶ Y` are the maps in the statement.
- `hflat : MapIsFlat f` is flatness by the recorded compatible étale-chart test.
- `hft : MapIsLocally (@LocallyOfFiniteType) f` is exactly the locally finite type
  chart test. It does not assert finite type or quasi-compactness of f.
- `hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`
  makes j an open immersion: every scheme pullback is represented by an open
  immersion, using the recorded Mathlib scheme predicate.
- `hqc` quantifies over `T : Y.EtaleSite` with `IsAffine T.obj.left.left`.
  Its witnesses U, p, q and `IsPullback q (yoneda.map p) j.hom.hom T.obj.hom`
  identify U with the actual inverse image of V in this affine étale chart.
  `QuasiCompact p.left` says precisely that this open subscheme is quasi-compact.
  Since the target is affine, this is equivalent to compactness of its source;
  an open subscheme of an affine scheme is quasi-separated, so a quasi-compact
  such open has a quasi-compact inclusion. Uniqueness of pullback representations
  makes the existential independent of the representing scheme. The quantifier is
  over affine étale charts, exactly as specified in the node.
- `hdense` says that for every small étale object T of Y, two regular functions
  `a b : Y.structureSheaf.obj.obj (op T)` are equal whenever their restrictions
  along every scheme map p from an étale object U of V over T agree. The triangle
  `U.obj.hom ≫ j.hom.hom = yoneda.map p ≫ T.obj.hom` means precisely "over Y".
  The restrictions are the actual global-section ring maps
  `(Scheme.Γ.map p.left.op).hom`. This is sectionwise injectivity of
  O_Y → j_* O_V: sections of the direct image on T are compatible regular
  functions on the étale charts of T ×_Y V; such charts cover that open scheme.
  Equal direct-image sections therefore mean equality after every such restriction,
  and the sheaf condition gives the converse. This keeps schematic density,
  including nilpotents, rather than replacing it with topological density.
- `hfp` applies `MapIsLocallyOfFinitePresentation` to the canonical second
  projection `Limits.pullback.snd f.hom j.hom`. Its source is the sheaf pullback
  `Limits.pullback f.hom j.hom`, bundled as an algebraic space by
  `(fibreProduct_isAlgebraicSpace X V Y f j).1`. `ObjectProperty.homMk` merely
  views that existing sheaf projection as a morphism in the full subcategory.
  There is no arbitrary map or chosen comparison standing in for base change.
- The conclusion `MapIsLocallyOfFinitePresentation f` is exactly local finite
  presentation, using the dependency's existing chart predicate. No separatedness
  or quasi-compactness binder on f, and no additional conclusion, appears.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `EtaleSite`, `etaleForget`,
  `structurePresheaf`, and `structureSheaf`. In particular the last two are the
  actual regular-function presheaf and its sheaf, not an abstract ring sheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  its recorded quasi-compactness companion is `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, whose first conjunct bundles
  exactly the sheaf pullback and whose second conjunct is its universal property.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no
  declaration or module to import; explicit universe polymorphism implements it.

All recorded proof-dependency modules are imported, with plain `import` when
not already a statement dependency. In particular the module uses the upstream
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion` and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`, and the recorded
`Sheaf.TraceFormula.FlatFiniteTypeDensePresentation`, without redeclaring them.
The remaining Mathlib proof imports give the finite-presentation algebra/kernel,
module-kernel, étale-composition and affine morphism criteria.

Edge cases checked against the statement:

- Identity open V = Y: regular functions are detected on the identity chart;
  hfp is the ordinary local finite presentation hypothesis up to canonical base
  change. The statement retains this case.
- Empty Y, X or base: no nonemptiness or nonzero-ring hypothesis excludes them.
  Over the empty target a representable étale atlas is empty. All corresponding
  chart predicates have their expected vacuous values.
- Empty V with nonempty Y is correctly ruled out by hdense, since the affine
  chart restriction to the empty scheme is the zero ring and cannot detect all
  functions on a nonempty affine. Empty V over empty Y remains allowed.
- Nonreduced targets: equality of functions, including nilpotent functions, is
  required. Topological density alone is not substituted.
- Non-quasi-compact or nonseparated f is allowed. The only quasi-compactness
  hypothesis concerns the affine-chart inverse images of the open V.
- No restriction on characteristic, finite presentation of the base, or finite
  index set is introduced.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder` with query "A flat locally finite type morphism of
  algebraic spaces is locally of finite presentation if it is so over a quasi
  compact schematically dense open": eight results, including scheme
  `LocallyOfFinitePresentation`, its finite-type implication, affine criteria,
  flat descent and universal openness. No extension-from-dense-open statement.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`:
  twelve hits, including `UniversallyOpen.of_flat`, étale criteria, flat descent,
  flat-monomorphism openness and finite-flat rank; no exact match.
- `msearch.py ... leansearch` with query "Finite presentation of a flat locally
  finite type algebraic space morphism extends from a quasi compact schematically
  dense open": eight hits, all scheme definitions, affine consequences,
  finite-type implication, smoothness or flatness, with no exact match.
- `msearch.py ... grep` with regular expression
  `schematicallyDense|[Dd]ense.*[Ff]initePresentation|[Ff]initePresentation.*[Dd]ense`
  in `AlgebraicGeometry`: one Mathlib hit, `Morphisms/Smooth.lean:368`, concerning
  density of a smooth locus, not this theorem.
- `rg -n` with the same regular expression and the item's id in
  `lean/WeilConjectures` and `lean/Sheaf`: dense compactifications, fibre results,
  a proper-open density theorem and the scheme module-extension theorem, but
  no algebraic-space morphism extension theorem. Read the relevant existing
  `AlgebraicSpaceQcOpenSchematicClosure.lean` condition: it uses the same
  section-detection rendering of schematic density.
- A separate `rg -n` for the item's id and proposed full declaration suffix in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
  no existing declaration. The item has no released repair-note file.

No node faults or disputed statements were found. No statement correction,
new-node record, dependency repair, or extra mathematical hypothesis is needed.

## Second reading by NW

The dispatcher explicitly requires one worker and prohibits starting other
agents. This is the same worker's separate rereading, not a claim of independent
review; the maintainer's delivery review supplies the independent reading.

Reopened the node statement, Tag 0877, and the final module. Checked S and all
three spaces are over the same base; hflat and hft are separate local chart
conditions; hj is representable openness; hqc is limited to affine étale tests
and its square really pulls back j; hdense compares actual regular functions
with the correct contravariant Γ map; hfp uses the second projection to V,
not the first projection to X; the conclusion is exactly the same recorded
local-finite-presentation predicate on f. The ring-map density condition agrees
with O_Y → j_* O_V by testing equality on charts of the inverse-image scheme.
No clause mismatch was found. Added the explicit public import of
`Mathlib.AlgebraicGeometry.Scheme` to make the base-scheme statement dependency
visible directly; no mathematical change was required. The proof is solely
`sorry`, and all binders and the universe are explicit.

## Validation

The prescribed `scompile.py NW lem-sfb-space-flat-finite-presentation-dense-open`
compiled both sandbox and library module modes successfully (1.7 s and 2.1 s)
before adding the redundant direct public scheme import. Final validation is
performed by the prescribed server dry run and delivery tools.
