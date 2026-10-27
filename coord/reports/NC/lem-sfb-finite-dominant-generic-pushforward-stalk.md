## Worker report

Item: lem-sfb-finite-dominant-generic-pushforward-stalk. Group: NC. Stage: 2.
Date: 2026-10-22.

The delivery adds the module
`Sheaf.AlgebraicGeometry.FiniteDominantGenericPushforwardStalk` and records its main
statement `AlgebraicGeometry.Scheme.Hom.finite_dominant_generic_pushforward_stalk`.
It also defines `AlgebraicGeometry.Scheme.Hom.genericPushforwardStalkMap`, the
canonical map already described by this node. This helper belongs to the item's
notion, is listed in lean.declarations, and has real data: Mathlib's
stalkPushforward after transport along the generic-point equality. That equality
is proved directly from continuity, density and uniqueness inside the definition;
no postponed theorem is used to choose data. The main theorem's entire proof is
sorry. There are no new nodes, dependency modules, or statement corrections.
Only lean changes in the copied node; the N5 reviewed stage-1 split is preserved.
The previous attempt had mistaken that stage-1 review for a stage-2 completion.
The live node has reviewed but no lean or reviewed_lean record, so this is its
missing Lean statement, not a re-split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes X,Y: `{X Y : Scheme.{u}}`, with arbitrary explicitly bound universe u.
- Both integral: `[IsIntegral X] [IsIntegral Y]`. These give nonemptiness,
  irreducibility and the function-field field structures; there are no separate
  normality, smoothness, flatness, dimension or Noetherian assumptions.
- The morphism f: `(f : X ⟶ Y)`.
- Finite: `[IsFinite f]`, the recorded Mathlib class with affine inverse images
  and finite section-ring maps.
- Dense image: `[IsDominant f]`, whose exact defining field is `DenseRange f`.
- Generic points: `genericPoint X` and `genericPoint Y`; `genericPoint_spec` is
  IsGenericPoint for the whole space. The map definition derives
  `f (genericPoint X) = genericPoint Y`; it asks for no additional hypothesis.
- Function fields: `X.functionField` and `Y.functionField`, Mathlib abbreviations
  for the structure-sheaf stalks at these generic points. This is precisely the
  arbitrary integral-scheme clause of def-sc-function-field; its product-of-
  components definition for nonintegral curves is irrelevant here.
- The actual dominant function-field algebra is
  `Scheme.Hom.dominantFunctionFieldAlgebra f`, passed explicitly to algebraMap;
  there is no inferred or arbitrary alternative embedding.
- The sheaf F has underlying ring presheaf
  `(TopCat.Presheaf.pushforward CommRingCat f.base).obj X.presheaf`. Pushforward
  evaluates on V as X.presheaf on f inverse-image V. Thus it is exactly the
  direct image structure sheaf, with the same sections and germs; stalks use its
  underlying presheaf as usual, without an additional sheafification.
- Its stalk is taken at `genericPoint Y` in the source type of the helper.
  The canonical k(Y)-algebra structure homomorphism is
  `(TopCat.Presheaf.stalkFunctor CommRingCat (genericPoint Y)).map f.c`.
  Taking this ring homomorphism's RingHom.toAlgebra gives the scalar action
  r times z = (this hom r) * z. This is the germ multiplication action specified
  by def-weil-pbc-module-stalk, now retaining the ring multiplication too.
- The specified canonical comparison, rather than an abstract isomorphism, is
  `f.genericPushforwardStalkMap`: stalkSpecializes along equality of points,
  followed by `TopCat.Presheaf.stalkPushforward CommRingCat f.base X.presheaf
  (genericPoint X)`. The existing germ_stalkSpecializes and stalkPushforward_germ
  formulas say precisely that this sends a germ over f inverse-image V to the
  source generic germ of the same section.
- The isomorphism assertion is the first conjunct
  `Function.Bijective (f.genericPushforwardStalkMap)`; the map already has type
  CommRingCat.Hom, so preserves addition, multiplication, zero and one.
- The k(Y)-algebra qualification is the second conjunct: for every
  `a : Y.functionField`, applying that same canonical comparison to the source
  scalar hom gives the target algebraMap of dominantFunctionFieldAlgebra f.
  Equality on all scalars is exactly the AlgHom commuting square. Since the
  comparison is multiplicative, c(s(a)*z) = alpha(a)*c(z) for every z follows
  immediately. Conversely any isomorphism of these algebras satisfies both
  displayed conjuncts. This encoding neither strengthens nor weakens the node.

Dependencies read and used, with the recorded declaration names:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite;
  IsIntegralHom and IsFinite.instIsIntegralHom supply the proof's integrality.
- Mathlib.Topology.Sober: IsGenericPoint, genericPoint, genericPoint_spec;
  IsGenericPoint.eq supplies uniqueness in the helper's elementary construction.
- WeilConjectures.AlgebraicGeometry.FunctionField: the dependency's
  Scheme.functionFieldOfComponents and its documented integral-scheme clause,
  reusing Mathlib.AlgebraicGeometry.FunctionField's Scheme.functionField.
- Sheaf.TraceFormula.LocalDimensionFormula:
  AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra. I read its full
  definition and its underlying Scheme.Hom.functionFieldMap in
  WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback. Its map is the actual
  generic stalk map, not a chosen field embedding.
- WeilConjectures.Topology.PresheafModuleStalkFunctor:
  PresheafOfModules.moduleStalkFunctor and stalkObj; the ring-stalk portion of
  this dependency's mathlib_match is TopCat.Presheaf.stalk, which is used here.
  There is no duplicate presheaf-module stalk or carrier.
- Proof-only import WeilConjectures.AlgebraicGeometry.AffinePushforwardStalkLocalization:
  AlgebraicGeometry.affine_pushforward_stalk_isLocalization. Other proof
  dependencies use Mathlib's scheme sobriety, functionField_isFractionRing_of_isAffineOpen,
  locally ringed-space morphism, and Spec, from their recorded modules (the
  locally ringed-space morphism module is a plain proof-only import). Every
  recorded proof-dependency module is imported or supplied by the statement
  imports. No proof-import cycle is introduced.

Sources read: the complete node and seven-step proof; every stmt_deps node and
its recorded declaration and docstring; Stacks varieties.tex,
lemma-degree-pullback-map-proper-curves (Tag 0AYZ), the first proof paragraph
identifying generic rank with the function-field degree; the existing affine
pushforward-stalk localization and generic function-field constructions. The
module docstring and the theorem docstring give the source and blueprint id, and
the theorem docstring carries all seven proof steps with their dependency ids.
The proof works for all finite dominant integral schemes, as the reviewed split
explains; the source's proper-curve application does not add hypotheses here.

Edge cases checked before writing: the identity; a finite extension of fields
(dimension zero); a finite inseparable cover t mapping to t^p in characteristic p;
the normalization of the cusp k[t^2,t^3] inside k[t] (nonnormal target and no
flatness assumption); arbitrary-dimensional and non-Noetherian domains in the
localization argument. Empty schemes and zero section domains cannot occur at
these generic points because integrality is nonempty and the chosen affine
opens contain the generic points. No separability or characteristic restriction
is used. Dropping finiteness would fail: for the projection induced by
k[x] → k[x,t], the direct-image generic stalk is k(x)[t], whereas the source
function field is k(x,t). Dominance is also essential to identify the generic
points and scalar map.

Searches performed through msearch.py (all four services succeeded; full query
records are retained in sandbox searches.jsonl):

- LeanFinder: "For a finite dominant morphism of integral schemes the generic
  stalk of the pushforward structure sheaf is canonically isomorphic to the
  source function field as an algebra over the target function field". Eight
  hits: stalkFunctionFieldAlgebra, Scheme.functionField, rational-map
  constructors, fraction-field instances and germToFunctionField. None states
  the finite direct-image stalk comparison.
- Loogle: `"stalk", "pushforward"`. Twelve hits including stalkPushforward,
  stalkPushforward_germ, and stalkPushforward_iso_of_isInducing. I read their
  definitions/signatures. The first is used to construct our canonical map;
  the isomorphism theorem requires an inducing map, which finite dominant
  morphisms need not have. Thus it is not an existing theorem for this item.
- LeanSearch: "A finite dominant map of integral schemes induces an isomorphism
  from the generic stalk of its direct image structure sheaf to the function
  field". Eight hits on localRingHom_comp_stalkIso, arrowStalkMapSpecIso,
  stalkMap, IsDominant, germToFunctionField, and finite-implies-integral.
  None asserts the required comparison.
- Mathlib grep via msearch.py:
  `stalkPushforward|generic.*pushforward|pushforward.*generic` in AlgebraicGeometry.
  Three hits, in GammaSpecAdjunction and ClosedImmersion, concern the
  construction and the closed-immersion inducing case.
- Project rg searches in lean/WeilConjectures and lean/Sheaf for generic stalks,
  stalkPushforward, finite dominance and dominantFunctionFieldAlgebra located
  AffinePushforwardStalkLocalization, BirationalLinePushforwardGenericStalk,
  FiniteSingletonFibreLocalization, and LocalDimensionFormula. The first supplies
  a localization ingredient; the others concern line modules or a singleton
  fibre or the existing scalar algebra, and do not state this theorem.
- Exact node-id search in lean/WeilConjectures had no hit. Name searches for
  genericPushforwardStalkMap and finite_dominant_generic_pushforward_stalk in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json had no
  hit before writing. No alternative definition of the function field,
  dominant algebra or stalk was introduced.

Validation: the prescribed scompile.py compiled this delivered file both as an
isolated sandbox module and under its intended library module name, with no
errors or unexpected warnings (reported times 7.9 s and 12.4 s). Both automatic
implicit-variable mechanisms are disabled in the file. Every source line is at
most 100 characters. The node's lean.statement is the verbatim main theorem
signature, ending immediately before :=. The required deliver2.py dry run and
push follow this report.

There is no STATEMENT-DISPUTED flag or outstanding mathematical node fault.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
