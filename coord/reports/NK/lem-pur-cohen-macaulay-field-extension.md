## Worker report

The module `Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension` states all three
parts of `lem-pur-cohen-macaulay-field-extension`, using three named theorems.
Every proof is `by sorry`; no definition or instance is introduced. The node copy
changes only `lean`. No dependency nodes, new nodes, or statement corrections are
needed. The previous empty sandbox has been populated with the module, node copy,
and this report.

Hypotheses and conclusions, clause by clause:

1. A field k and any field extension K/k are `{k K : Type u} [Field k]
   [Field K] [Algebra k K]` in
   `AlgebraicGeometry.stalk_depth_eq_ringKrullDim_iff_of_field_extension`.
   There is no finite-generation, separability, algebraicity, or perfectness
   hypothesis on this extension. The explicit structure map
   `f : X ⟶ Spec (.of k)` with `[LocallyOfFiniteType f]` renders the locally
   finite-type k-scheme. An explicit map is appropriate here because it defines
   the specified base change.
2. The base-changed scheme is exactly
   `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))` and the projection
   p is its `pullback.fst`. The binder `x'` ranges over all points of this
   scheme; its image x is written as the projection applied to `x'`.
   The conclusion is an iff between depth equal to dimension at `x'` upstairs
   and at this image downstairs. It asserts no equality of their dimensions.
3. Every Cohen–Macaulay condition is the equality
   `(IsLocalRing.depth (R := T) T : WithBot ℕ∞) = ringKrullDim T`, where T is
   precisely the relevant structure-sheaf stalk. This uses the recorded
   definitions of depth and dimension, with the injective inclusion of `ℕ∞`
   into `WithBot ℕ∞`. These stalks are Noetherian local rings by local finite
   type over the relevant field; no extra Noetherian-stalk hypothesis is added.
4. The relative setting is `{X S : Scheme.{u}} [IsNoetherian X]
   [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]` in
   `AlgebraicGeometry.fibre_depth_eq_ringKrullDim_iff_geometric`.
   `IsNoetherian` is Mathlib's locally Noetherian and compact condition,
   equivalent to a finite affine cover by Noetherian rings
   (`isNoetherian_iff_of_finite_affine_openCover`). `IsNoetherianRing` means
   every ideal is finitely generated (`isNoetherianRing_iff_ideal_fg`).
5. For `s : S`, `y : f.fiber s` is an arbitrary ordinary-fibre point.
   The geometric fibre is the recorded alternative expression
   `pullback (f.fiberToSpecResidueField s)
     (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))`.
   Here `Ω` is an arbitrary chosen algebraic closure, expressed by
   `[Field Ω] [Algebra (S.residueField s) Ω]
     [IsAlgClosure (S.residueField s) Ω]`.
   These binders introduce the closure used to define the geometric fibre;
   they impose no extra restriction on f, its residue fields, or the extension
   in the first theorem. This pullback is the geometric fibre as recorded by
   `def-weil-geometric-fibre`, canonically isomorphic by pullback pasting to
   the pullback of f along the composite geometric point.
6. The geometric theorem gives both iff statements: ordinary Cohen–Macaulayness
   is equivalent to the existence of a geometric lift z over y with that
   property, and equivalent to that property at every such z. Each lift is
   required to satisfy `pullback.fst ... z = y`. The existential half keeps
   the geometric test from being merely an assertion about an unspecified
   or potentially absent point. Ordinary-fibre points correspond to the
   original x with f(x) = s by `Scheme.Hom.fiberHomeo s`, so this states exactly
   the ordinary/geometric equality of the relative locus on X.
7. In `AlgebraicGeometry.fibre_depth_eq_ringKrullDim_locus_baseChange`, the
   binders additionally give an arbitrary `g : S' ⟶ S` and
   `[IsNoetherian S']`. No flatness, finite-type, or separation condition is
   imposed on g, and no global Noetherian hypothesis is imposed on
   `pullback f g`. The base-changed morphism is exactly `pullback.snd f g`.
8. The final equality is the locus of x' where the stalk of the ordinary
   fibre of `pullback.snd f g` is Cohen–Macaulay, equal to
   `(pullback.fst f g) ⁻¹'` of the corresponding locus for f. The points in
   these ordinary fibres are the canonical `Scheme.Hom.asFiber x'` and
   `f.asFiber x`. Thus the formula is literally U_f' = p⁻¹(U_f), including
   every point and both implications.

Dependency declarations used (the recorded statement interfaces were read):

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback, pullback.fst, pullback.snd |
| def-weil-pbc-depth | Sheaf.RingTheory.Depth | Ideal.depth, IsLocalRing.depth |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | Scheme.Hom.fiber, fiberι, fiberToSpecResidueField; its canonical point asFiber |
| def-weil-geometric-fibre | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | pullback along Spec.map of the residue-field inclusion into a chosen algebraic closure |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |

The module also uses the existing Mathlib `Scheme.residueField`, `Spec.map`,
`IsAlgClosure`, and `IsNoetherian` interfaces. The theorem docstrings carry all
nine proof steps from the node: affine finite-presentation reduction; the
polynomial chart and its tensor identification; preservation of local dimension;
the fibre-flat criterion on both charts; localized flatness ascent; faithful-flat
descent; the absolute conclusion; geometric-fibre tests including existence of
lifts; and residue-field base change for the relative conclusion. All recorded
proof dependencies with modules are imported, with proof-only imports non-public.
In particular the polynomial chart, polynomial-chart fibre-flat criterion,
dimension-at-point field-extension, localized-module flatness, and faithfully
flat descent interfaces are imported from their recorded modules.

Edge cases checked: an empty X makes the absolute point assertion and the
geometric point assertions vacuous, and gives equality of empty relative loci;
an empty S' likewise gives equality of empty loci. For K = k and identity g
the assertions specialize to the identity base changes. Zero-dimensional local
rings use depth = dimension = 0. Generic and closed points are both covered,
even when dimension changes after field extension. Purely inseparable and
transcendental extensions are allowed. No reducedness, smoothness, flatness of f,
perfectness, or global quasi-compactness of the absolute X is assumed. The
scheme universe u is explicit and arbitrary, and both fields/closures live in
that same universe so that the scheme fibre products are well typed; every
variable and universe is bound explicitly.

Searches made before writing:

- `msearch.py leanfinder`: “Cohen Macaulay locus of a finite type scheme is
  invariant under arbitrary extension of fields”. Eight results concerned
  smooth/unramified loci, geometric reducedness, and proper finite-type
  morphisms; no depth/dimension or Cohen–Macaulay equivalence.
- `msearch.py loogle`: `"depth", "TensorProduct"`. Zero results.
- `msearch.py grep`: `Cohen.?Macaulay|cohen_macaulay`. Zero Mathlib results.
- `msearch.py leansearch`: “Cohen Macaulay locus commutes with base change”.
  Eight results about general stability of ring or scheme morphism properties,
  localization, and formally smooth maps; none is this statement.
- Direct `rg` over the upstream `WeilConjectures` source for
  `Cohen.?Macaulay|cohen_macaulay`: no matches. The item-id search using
  `grep -rn` likewise found no declaration.
- Direct `rg` over `lean/Sheaf` found existing Cohen–Macaulay ring results and
  fibre-locus openness results. In particular `FibreCohenMacaulayLocus` is
  openness for a flat locally finitely presented morphism, and
  `PolynomialChartFibreFlatCriterion` is the chart-flatness criterion. Neither
  states the present field-extension or relative base-change assertion.
- Searched the three proposed full declaration names in upstream, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: no matches.
- Read the actual Stacks source at `lemma-extend-field-CM-locus` (00RJ) and
  `lemma-CM-locus-commutes-base-change` (00RK). These give the affine assertions
  whose local scheme formulations are exactly the node's clauses.

Validation: `scompile.py NK lem-pur-cohen-macaulay-field-extension` compiled the
module in both sandbox and library contexts, with no errors or warnings. An
initial type-inference failure in point binders was repaired by annotating the
pullback objects with `Scheme.{u}`. No mathematical hypothesis changed. The
maximum Lean line length is at most 100 characters. The node's `lean.statement`
is the exact source signature of its primary declaration, and `lean.declarations`
lists all three theorems. No statement dispute or dependency fault was found.

## Second reading by NK

I independently read the node, its nine proof steps, the complete delivered module,
Stacks `algebra.tex` at `lemma-extend-field-CM-locus` (00RJ, lines 33700–33736)
and `lemma-CM-locus-commutes-base-change` (00RK, lines 33738–33754), and the
recorded statement dependencies. These lemmas are self-contained: 00RJ assumes
a finite-type algebra over a field and an arbitrary field extension; 00RK assumes
a finite-type ring map and an arbitrary base ring map. Their affine statements
localize to the node's scheme assertions. The node intentionally restricts its
relative consequence to Noetherian schemes; the Lean has exactly this restriction,
without adding it to the absolute assertion. No statement correction is needed.

Object/hypothesis/conclusion checklist (in the order of the node):

1. **Field k, arbitrary extension K/k.** The first theorem's
   `{k K : Type u} [Field k] [Field K] [Algebra k K]` introduces precisely these.
   An algebra map from a field to a field is injective. There is no assumption
   of finite type, finite degree, separability, algebraicity, or perfectness.
   Verdict: exact.
2. **Locally finite-type k-scheme X.** `{X : Scheme.{u}}`, the specified
   `f : X ⟶ Spec (.of k)`, and `[LocallyOfFiniteType f]` use the recorded scheme
   and finite-type definitions. I read the class field `finiteType_appLE`, which
   requires finite-type maps on affine opens. There is no quasi-compactness or
   global Noetherian assumption. The explicit f is needed for this base change.
   Verdict: exact, including non-quasi-compact X.
3. **X_K, projection p, point x' and image x.** The first theorem uses the actual
   scheme `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, its
   `pullback.fst`, an arbitrary point `x'`, and its image. I read `pullback`,
   `fst`, `snd`, `Spec` and `Spec.map`: the latter reverses the field inclusion,
   so the two morphisms have common target Spec k. Verdict: correct objects and
   projection direction, with no arbitrary comparison map.
4. **Cohen–Macaulay equivalence at corresponding points.** The first theorem
   compares `(IsLocalRing.depth (R := T) T : WithBot ℕ∞) = ringKrullDim T`
   for the upstairs stalk and the downstairs stalk at p(x'). I read
   `Sheaf.RingTheory.Depth`: `IsLocalRing.depth` uses the maximal ideal and
   `Ideal.depth` uses lengths of regular sequences, not a private CM predicate.
   I read `ringKrullDim`, which is Krull dimension of the prime spectrum.
   The inclusion of ℕ∞ into WithBot ℕ∞ is injective. Local finite type over a
   field ensures these stalks are Noetherian, without requiring extra instances
   in the signature. Verdict: exactly the two CM conditions, not equality of
   the two local dimensions (which would be wrong).
5. **Relative locally finite-type f between Noetherian X and S.** The second
   and third theorems bind `[IsNoetherian X] [IsNoetherian S]` and
   `[LocallyOfFiniteType f]`. Mathlib `IsNoetherian` extends locally Noetherian
   and compact; its finite-affine-cover characterization matches the node's
   final sentence. `isNoetherianRing_iff_ideal_fg` matches its ring definition.
   There is no flatness, separation, or smoothness assumption. Verdict: exact.
6. **Ordinary fibre local ring at x.** The second theorem uses any `s : S`
   and `y : f.fiber s`; the third uses `f.asFiber x` in `f.fiber (f x)`.
   I read `fiber`, `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber` in
   Mathlib's `Fiber.lean`: the fibre is the pullback along
   `S.fromSpecResidueField s`, and `asFiber` is the inverse homeomorphism
   applied to x. Thus these are fibre stalks, not stalks of X itself.
   Verdict: exact, including nonclosed points s and x.
7. **Testing geometric fibres gives the same relative locus.** The second
   theorem takes any chosen closure `Ω` with its field, residue-field algebra,
   and `IsAlgClosure` instances. I read `IsAlgClosure` and the dependency
   `def-weil-geometric-fibre`, whose statement explicitly permits base-changing
   the ordinary fibre. The displayed pullback along the residue-field inclusion
   is exactly that expression. Its first projection maps z to y. The two
   conjuncts assert equivalence both with `∃ z, p z = y ∧ CM(z)` and with
   `∀ z, p z = y → CM(z)`. This is the node's some/every geometric-lift test;
   it cannot become vacuous through an absent lift because the existential
   equivalence is also present. `fiberHomeo` identifies these y with points x
   of X over s. Verdict: exact for every choice of algebraic closure.
8. **Any Noetherian base change S' → S.** The third theorem binds
   `{S' : Scheme.{u}} [IsNoetherian S'] (g : S' ⟶ S)`. It puts no property on
   g and no global Noetherian hypothesis on the pullback scheme. Its new map
   is `pullback.snd f g`. Verdict: exact; g need not be flat or finite type.
9. **U_f' = p⁻¹(U_f).** The third theorem's set equality uses precisely the
   fibre stalk at `(pullback.snd f g).asFiber x'` on the left and
   `(pullback.fst f g) ⁻¹'` of the original fibre-stalk locus on the right.
   Both directions hold at every point. Verdict: exact equality of loci.

Dependency and proof audit: I opened the signatures behind all eight statement
nodes, including the geometric-fibre node's note specifying its pullback
expression. These interfaces are usable; no missing notion, new definition node,
or dependency repair is needed. I also read the polynomial-chart,
polynomial-chart fibre-flat criterion, dimension-at-point field-extension, and
localized-module base-change declarations used in the proof plan. The criterion
requires flat locally finitely presented structure maps, supplied over fields in
the first theorem's docstring. Its dimension is topological dimension at a point,
not stalk dimension. Steps 1–7 are in the first theorem's docstring, step 8 in
the second, and step 9 in the third. Recorded proof modules are imported as
non-public imports. There are exactly three theorem declarations, all with
`sorry` proofs; no definition, instance, private copy, or hollow data is added.
Every declaration has its blueprint and source docstring.

Edge cases: empty X gives no points for the absolute and geometric assertions;
empty fibres admit no y, and empty X or empty S' makes the final equality an
empty-set equality. A stalk at an actual point is a nonzero local ring, so the
zero-ring depth convention cannot introduce a spurious CM point. Dimension zero
is allowed with depth zero and no positivity binder; there is no n parameter
excluding n = 0. The identity extension/base change is admitted. Positive
characteristic, imperfect fields, purely inseparable extensions, and arbitrarily
transcendental extensions are admitted. The common arbitrary universe u is the
standard Scheme/Spec universe convention, not a small test-field quantifier;
all fields, schemes and a chosen algebraic closure may be placed in a common
ambient universe. No independent test universe or unbound universe/variable is
present. The closure can be chosen within u. No mathematical edge case is lost.

Independent searches, using different queries from the worker:

- `msearch.py leanfinder`: “The depth of a local ring equals its Krull dimension
  before and after scalar extension of a finite type algebra over a field”.
  Eight hits: local-ring ranks, prime heights, regular-element dimension
  formulas, localization dimension, and support dimension. I checked the
  returned signatures; none is the present equivalence.
- `msearch.py loogle`: `"depth", "ringKrullDim"`; no hits.
- `msearch.py grep`:
  `depth.*(baseChange|tensorProduct|field_extension)|Macaulay|cohen_macaulay`;
  no Mathlib hits.
- `msearch.py leansearch`: “For any extension of fields the inverse image of
  the Cohen Macaulay locus is the Cohen Macaulay locus of the base changed
  finite type scheme”. Eight hits about zero/smooth/free loci and stable
  scheme morphism properties; no CM statement.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for `macaulay|cohen_macaulay|depth.*(basechange|tensorproduct|field_extension)`.
  No upstream or Mathlib match. Project hits are the existing ring results,
  polynomial-chart criterion, and fibre-locus openness modules. I opened
  `FibreCohenMacaulayLocus` and `AffineFibreCohenMacaulayLocus`: their public
  conclusions are openness under flat locally finitely presented hypotheses.
  The former's private `fibre_locus_base_iff` assumes an open immersion on the
  base, so it does not supply arbitrary base change or the absolute assertion.
  None is an exact existing implementation of this node.
- The three proposed full declaration names and the module name have no
  match in upstream, the project library, or `dag/lean_names_upstream.json`.

Mismatches repaired: the module docstring began `/-!+#`, so I changed it to
`/-! #`. The geometric theorem cited Morphisms Tag 01ZA; I checked the tag table,
where 01ZA is `limits-proposition-approximate`, unrelated to geometric fibres.
I replaced that citation by Schemes Tags 01JO (fibre products) and 01K0
(ordinary fibre), explicitly followed by algebraic-closure base change. No Lean
signature, mathematical hypothesis, conclusion, node statement or dependency
changed. The node's `lean.statement` remains verbatim the primary signature.

Validation: all delivered files are compiled separately through `scompile.py`;
the single module compiles in sandbox and library contexts without errors or
warnings. A first delivery dry run correctly required this independent report;
the final dry run is repeated after adding it and repairing the citations.
