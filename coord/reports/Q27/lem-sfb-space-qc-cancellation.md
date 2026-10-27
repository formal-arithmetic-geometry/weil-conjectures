## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactCancellation` states
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_of_comp_of_quasiSeparated` with a single
`sorry` proof. It defines no notions. Its declaration docstring carries all five steps
of the node's proof, including the diagonal pullback square, both atlas choices, and
composition on scheme tests. Sources read: Stacks `spaces-morphisms.tex`,
lemma-quasi-compact-permanence (03KS), lemma-quasi-compact-local (03KG), and
lemma-fibre-product-after-map (03KN). The original statement needs no correction.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using Mathlib's actual scheme category.
- Algebraic spaces over S: `(X Y Z : AlgebraicSpace S)`, the recorded full subcategory
  of big-fppf sheaves with representable diagonal and an etale surjective scheme atlas.
- Morphisms f and g: `(f : X ⟶ Y) (g : Y ⟶ Z)`. Their underlying natural transformations
  are `f.hom.hom` and `g.hom.hom`; categorical composition is in the order `f ≫ g`.
- Size convention: explicit `universe u`, `Scheme.{u}`, and the recorded algebraic-space
  universe. The predicate tests every `T : Over S` in that same scheme universe, and
  field-valued point classes live in `Type (u + 1)` as in the recorded Point definition.
  No universe equality or essential-smallness assumption is added.
- Atlas topology: `MapIsQuasiCompact` uses `Point` with the exact
  `pointTopologicalSpace` instance from `def-a1-space-point-topology`.
- Quasi-compact spaces: `CompactSpace (Point ...)`. This is compactness without a
  Hausdorff assumption, equivalent to every open cover having a finite subcover.
- Sheaf fibre products: the existing predicate uses `Limits.pullback f a` on underlying
  presheaves. For these sheaves this represents the sheaf fibre product; the recorded
  `fibreProduct_isAlgebraicSpace` supplies algebraic-space closure. The module imports
  its recorded owning module directly.
- Affine schemes: `MapIsQuasiCompact` quantifies over every `T : Over S` and map
  `a : yoneda.obj T ⟶ G`, with premise `IsAffine T.left`. Mathlib's IsAffine means
  isomorphic to Spec of a commutative ring, so this includes all affine tests and is
  invariant under changing the chosen spectrum presentation. `Spec` is the dependency's
  actual Mathlib spectrum; no replacement affine notion is introduced.
- Quasi-compact composite: `hcomp : MapIsQuasiCompact (f.hom.hom ≫ g.hom.hom)`.
- Quasi-separated g: `hg : MapIsQuasiCompact (pullback.diagonal g.hom.hom)`; this is the
  canonical relative diagonal into the self fibre product over Z, not an absolute
  diagonal over S and not representability by separated scheme maps.
- Conclusion: `MapIsQuasiCompact f.hom.hom`, with exactly the same affine tests and
  point-space compactness convention as the hypotheses.
- No global quasi-compactness: no `CompactSpace` hypothesis on X, Y, Z or S, and no
  hypotheses on their structure morphisms. No representability of f or g is assumed.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; read their signatures and docstrings in Scheme.lean (42, 74, 470, 479).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and its
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective` scheme-test
  interfaces. Read the full definitions, not only the names.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  also read Point and schemePointMap in AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, read with its
  full signature and docstring at line 55. This matches the statement exactly, so its
  landed owner `def-sfb-proper-curve-moduli` is added to stmt_deps under the explicit
  brief-stage2 §5 permission to cite an already landed definition node. Neither that
  node nor its module is edited; the item otherwise changes only in lean.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` (plain proof import):
  `points_compactSpace_iff`, with its full scheme-atlas existential and no nonempty
  condition. The other clauses of that proof dependency were also read.
- `Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests` (plain proof import): all four
  recorded theorems, especially `quasiCompact_iff_quasiCompact_scheme_tests` and
  `quasiCompact_presheafMap_baseChange`. These use the existing atlas convention;
  the proof first reconciles it with point compactness using points_compactSpace_iff.
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty` (plain proof import): the recorded
  `Scheme.instIsStableUnderCompositionPrecoverageOfIsStableUnderComposition` match
  for `lem-weil-pbc-etale-covering-composition`; read the instance and the
  `ofArrows_mem_precoverage_iff` signature. There is no missing lean record: this
  dependency is Mathlib-backed. This supplies the scheme-test singleton composition.
- `def-weil-size-convention` is metatheoretic (its record has no declaration), rendered
  by the explicit universe binders, not a new Lean object or assumption.

Edge cases checked before writing:

- Empty X and empty tested pullbacks: compactness and the empty scheme atlas are
  permitted, with no Nonempty binder or nonempty-cover assumption.
- Empty base S: the same universe and Over encoding work without points.
- Identity arrows: if g is identity, its relative diagonal is an isomorphism and the
  conclusion is the same quasi-compactness as the composite hypothesis. If f is
  identity, the conclusion is the valid identity-morphism affine-test property.
- Non-quasi-compact ambient spaces: identity maps of non-quasi-compact schemes still
  satisfy the relative affine-test property; the statement does not mistakenly demand
  compactness of their whole point spaces. Over arbitrary non-quasi-separated S,
  the diagonal in hg remains relative to Z.
- Nonrepresentable morphisms of algebraic spaces are included. Scheme cancellation
  alone cannot state this theorem. Nonreduced schemes, zero rings/empty spectra and
  all characteristics are included; no reducedness, field or characteristic binder.
- The two hypotheses are substantive in general: quasi-compactness of an arbitrary
  map, and compactness of the diagonal, are not inferred automatically by the API.

Searches for an existing statement (2026-10-24):

- msearch leanfinder: "For composable morphisms of algebraic spaces if the composite
  is quasi compact and the second map is quasi separated then the first map is quasi
  compact". Eight hits, headed by `AlgebraicGeometry.QuasiCompact.of_comp`; the full
  signature quantifies over Scheme, not AlgebraicSpace. No exact match.
- msearch loogle: `"QuasiCompact.of_comp"`. One hit, same scheme-only lemma; read its
  actual Mathlib source in Morphisms/QuasiSeparated.lean, including the full binders.
- msearch leansearch: "Quasi compactness cancellation for morphisms of algebraic spaces
  with quasi separated second morphism". Eight hits, all scheme properties; no exact
  algebraic-space cancellation statement.
- msearch grep: `AlgebraicSpace|algebraic space` in all Mathlib. Zero hits.
- rg over `lean/WeilConjectures` for AlgebraicSpace and the item id: no algebraic-space
  framework or existing statement. Searches for quasiCompact_of_comp locate only
  scheme usage. Search for the item id yields no upstream declaration.
- rg over `lean/Sheaf` for the item id, cancellation/of_comp names, and existing
  quasi-compactness declarations: no cancellation result; ProperCurveModuli supplies
  the exact existing MapIsQuasiCompact, which is reused without duplication. Also
  read SpaceQuasiCompactAffineTests and SpaceQCSeparatedEtaleLocal to distinguish
  the atlas predicate from the required point-topology predicate.

No STATEMENT-DISPUTED flag, missing notion, dependency repair, or statement correction.
No new node is needed. All theorem proofs in the delivery are sorry, as required.
The server scompile.py compiled both sandbox and library module forms cleanly (1.5 s
per form). `set_option autoImplicit false` enforces explicit variable binding; the
only universe parameter is explicitly declared u. No diagnostic commands remain.

## Second reading by Q27

A second self-review was made with the node JSON, the module, and the full definition
of MapIsQuasiCompact open. No additional worker was started, as the dispatch brief
expressly prohibits agents; the independent maintainer review remains separate.

The binders match precisely: S is a scheme, X/Y/Z are algebraic spaces over it, and
f/g are composable morphisms. hcomp uses f then g, not the reverse order. hg uses
`pullback.diagonal g.hom.hom`, so the hypothesis is quasi-compactness of the relative
Y-diagonal over Z, exactly the stated quasi-separatedness. The result is the same
MapIsQuasiCompact predicate on f. Its definition was expanded during this review:
every affine Over S object and every map to the target are tested, the pullback is
actual Limits.pullback, and compactness uses the existing point topology. No global
compactness or representability hypothesis has slipped in. Empty tests and arbitrary
S remain included. The only metadata adjustment was adding the already landed owner
of this reused definition to stmt_deps; no wording of the mathematical statement was
changed. All five proof steps appear in the docstring and proof-only imports remain
plain imports. No signature mismatch was found on this second pass.
