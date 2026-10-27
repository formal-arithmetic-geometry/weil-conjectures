## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsSpaceIntegralSchemeCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_surjective_integral_scheme_cover`, with its
whole proof postponed by `sorry`. There are no new definitions, helper theorems,
dependency modules, or statement corrections. The source was read in
`literature/stacks-project/decent-spaces.tex`, Tag 09YB(1), including the induction
proof of (2). Its ten-step DAG proof is reproduced in the declaration docstring.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. No condition on S is added;
  in particular S need not be quasi-separated or quasi-compact.
- The algebraic space over S is `(X : AlgebraicSpace S)`, using the recorded
  fppf-sheaf full subcategory, not a scheme specialization.
- Quasi-compactness of the underlying point space is
  `[CompactSpace (Point X.obj.obj)]`. Its topology is the existing final atlas
  topology of `pointTopologicalSpace`; no Hausdorff assumption is present.
- Absolute quasi-separatedness is `(hqs : IsAbsolutelyQuasiSeparated X)`.
  I read the existing definition and Stacks Tag 0AHR(3) in
  `spaces-properties.tex`: compactness of all affine-scheme pairwise fibre
  products is equivalent to quasi-compactness of the absolute diagonal.
  This avoids incorrectly using the relative diagonal over a possibly
  non-quasi-separated S.
- The S-scheme is existential `(Y : Over S)`, whose underlying scheme is
  `Y.left` and structure morphism is `Y.hom`. The morphism over S is
  `(p : schemeSpace Y ⟶ X)`. The existing `schemeSpace` retains the actual
  Yoneda sheaf of Y, and maps in this full subcategory are sheaf maps over S.
- Integrality is
  `IsRepresentableWith (fun _ _ q ↦ IsIntegralHom q.left) p.hom.hom`.
  The existing representability predicate quantifies over every test scheme
  and every map to X, requiring a representing scheme pullback whose projection
  has Mathlib's affine-and-integral-on-affine-opens property. Thus both
  representability and integral scheme projections are required, with no
  arbitrary comparison map substituted. The node's explanatory finite and
  affine conventions are the analogous uses of Mathlib `IsFinite` and
  `IsAffineHom`; neither is an additional conclusion of this lemma.
- Surjectivity on field-valued point classes is
  `pointImage p.hom.hom = Set.univ`, using the dependency's exact image
  definition. No sectionwise surjectivity or fixed-field lifting is assumed.
- `universe u` is explicit throughout: schemes have universe u and all test
  schemes and field representatives use the same size convention as the
  recorded algebraic-space framework. No independent test universe or bound
  on the cardinality of X is imposed. There are no auto-bound implicits.

Dependency interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms; `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, including their complete signatures.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  and `pointImage` (field representatives, no choice of an atlas).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`; its landed definition owner
  `def-sfb-space-absolute-quasi-separated` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` and its
  property theorem `schemeSheaf_isAlgebraicSpace`; its landed definition owner
  `def-trf-scheme-algebraic-space` is added to stmt_deps.
- `def-weil-size-convention` is the recorded metatheoretic convention rather
  than a Lean object; explicit universes implement it.

The other statement-dependency modules are publicly reachable through the
imports above. All currently recorded proof-dependency modules are plain
imports (apart from Finite, also a statement-dependency module): etale open
image, fibre products and etale covers (through EnlargedEtaleRingedSite),
separated etale diagonal, schematic closure, chartwise etale permanence,
reduced closed support, and upstream scheme representability. The matched
Mathlib proof inputs are imported from Affine (through Integral), Separated,
ClosedImmersion, UniversallyClosed and Limits. Nodes for the finite affine
atlas refinement, fibre bound, integral qcqs permanence, quasifinite integral
compactification, etale monomorphism, closed degree loci and integral extension
have no recorded Lean module yet; no private replacement is introduced.

Edge cases checked: X empty is allowed and admits the empty S-scheme with the
identity integral cover; there is no Nonempty binder. The induction docstring
handles fibre bound zero and one explicitly. The theorem has no bound variable
or nonempty atlas assumption. An arbitrary non-quasi-separated base remains
allowed because hqs is absolute. No finite-type, Noetherian, separatedness,
reducedness, or characteristic assumption is added to X or S; Y is not required
to be affine. No universal choice of Y is made in a definition. For represented
X the claim reduces to the usual scheme case (the identity suffices).

Searches for an existing statement:

- msearch.py leanfinder: "Every quasi compact quasi separated algebraic space
  admits an integral surjective morphism from a scheme". Eight hits, all
  scheme-level: normalization integral projection, compact schemes as
  surjective images of affine schemes, quasi-compactness of scheme morphisms,
  and scheme-local existence results. None states the algebraic-space result.
- msearch.py loogle: "AlgebraicGeometry.IsIntegralHom,
  AlgebraicGeometry.AlgebraicSpace". Zero hits; the service does not index the
  project's AlgebraicSpace identifier.
- msearch.py grep: "integral.*surjective|surjective.*integral|AlgebraicSpace"
  in Mathlib/AlgebraicGeometry. Two hits (integrality of closed immersions and
  geometrically integral scheme morphisms being surjective); neither matches.
- rg over lean/WeilConjectures and lean/Sheaf for qcqs/integral cover concepts
  found only scheme-level or unrelated results. The exact item-id search in
  lean/WeilConjectures had no match. Exact proposed declaration-name search
  over both library roots, Mathlib and dag/lean_names_upstream.json had no hit.
- Searches for absolute quasi-separatedness and schemeSpace found the two
  existing definitions and their DAG owners above; these are reused verbatim.

The example CompactObject module is now withdrawn and contains no declarations;
its node points to the existing source-library interface. The delivered module
follows the standing module/public-import/exposed-section conventions.

Validation: scompile.py checked this delivered module in sandbox and library
contexts against the published server build, clean in both contexts (2.1 s and
9.2 s respectively). The only postponed proof is the named theorem above.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
