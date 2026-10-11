## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension` states
`AlgebraicGeometry.exists_etale_open_of_smooth_of_fibre_dimension_zero` with only a `sorry`
proof. It introduces no definitions and changes the item's node only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary schemes and scheme morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The universe `u` is explicitly declared and arbitrary.
- The point is `(x : X)`; the point `s = f(x)` is used directly as `f x`, without an
  independent point or an extra equality hypothesis.
- The residue field `κ(s)` is Mathlib's `S.residueField (f x)`, defined as the residue
  field of the structure-sheaf stalk. It occurs inside the definition of `f.fiber (f x)`.
- The scheme-theoretic fibre `X ×_S Spec κ(s)` is `f.fiber (f x)`, definitionally
  `Limits.pullback f (S.fromSpecResidueField (f x))`, exactly the pullback specified
  by the recorded base-change conventions.
- Its point corresponding to `x` is `f.asFiber x : f.fiber (f x)`, defined using the
  fibre homeomorphism; `Scheme.Hom.fiberι_asFiber` says its first projection is `x`.
- A given open subscheme containing `x` is `(U : X.Opens) (hx : x ∈ U)`.
  Passing the neighbourhood as a parameter preserves the conclusion's dependence on
  that same neighbourhood: the assertion holds for every witness to the premise.
- Its restricted morphism `f|_U : U → S` is `U.ι ≫ f`, and smoothness is precisely
  `(hSmooth : Smooth (U.ι ≫ f))`. There is no global smoothness assumption on `f`.
- Dimension zero at the corresponding fibre point is
  `(hDim : topologicalKrullDimAt (f.asFiber x) = 0)`. This is dimension computed on
  open neighbourhoods, not the Krull dimension of the point's local ring.
- The output open subscheme is `∃ U' : X.Opens`; containment in the given neighbourhood
  is `U' ≤ U`; containing the original point is `x ∈ U'`; and the entire restricted
  morphism being étale is `Etale (U'.ι ≫ f)`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`, as recorded by its Mathlib match. `Scheme.Opens.toScheme`
  and `Scheme.Opens.ι` in `Mathlib.AlgebraicGeometry.Restrict` implement the open subschemes.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField`; the residue
  field is used through the fibre definition, without a private substitute.
- `def-pc-base-change`: imported `Sheaf.AlgebraicGeometry.BaseChangeConventions`.
  Read all six recorded declarations: `Scheme.Modules.moduleBaseChange`,
  `baseChange_morphism_projections`, `baseChange_iterated`, `baseChange_fiber`,
  `Scheme.Hom.geometricFiberAt`, `baseChange_section_characterization`.
  The record explicitly instructs users of `X_T` to use `Limits.pullback f T.hom`;
  the fibre used here is that very pullback. Module pullback, sections and geometric
  fibres are not needed in this statement. No unusable record or duplicate definition.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` (and read
  `SmoothOfRelativeDimension`) in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-kun-dimension`: `topologicalKrullDimAt` in
  `WeilConjectures.Mathlib.Topology.KrullDimension` (imported), and `topologicalKrullDim`
  in `Mathlib.Topology.KrullDimension`. Local dimension is the infimum of dimensions
  of open neighbourhoods, as the node requires.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (imported), as recorded by its Mathlib match.

Edge cases checked before writing: empty `X` admits no `x`, and `U = ⊥` cannot satisfy
`hx`; neither requires an additional nonemptiness hypothesis. The fibre over `f x`
always contains `f.asFiber x`, so its dimension-zero condition does not mistake the
empty fibre's dimension `⊥` for zero. `U = ⊤`, zero-dimensional components of a
smooth morphism with different dimensions on other components, arbitrary characteristic,
and nonclosed points are all permitted. No finite-type, Noetherian, affine, separated,
perfect-field, algebraically-closed-field or closed-point assumption was added.
The conclusion only concerns a neighbourhood of the given point, as required.

Sources read: the local literature checkout has no Stacks `.tex` files, so read the
source places online: [0A43](https://stacks.math.columbia.edu/tag/0A43), final proof
sentence; [02G1](https://stacks.math.columbia.edu/tag/02G1), rank of differentials equals
fibre dimension; [02G2](https://stacks.math.columbia.edu/tag/02G2), smooth relative
dimension; [02GI](https://stacks.math.columbia.edu/tag/02GI), étale morphisms. The
standalone criterion uses the general differential-rank fact of 02G1; the Noetherian
and finite-type hypotheses on the infinitesimal lifting lemma 0A43 are not needed
for this criterion. No statement correction or dispute was found.

Searches made (2026-10-11):

- `msearch.py ... leansearch "smooth morphism zero dimension fibre point etale neighbourhood"`:
  unavailable, Internal Server Error; no verdict inferred from unavailable search.
- `msearch.py ... leanfinder "A morphism smooth on an open neighbourhood of a point with
  fibre dimension zero at that point is etale on a smaller open neighbourhood"`: eight
  hits, including étale implies smooth, ring étale-locus openness, and standard smooth
  charts; none states the required scheme pointwise criterion.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale"`: one hit,
  `AlgebraicGeometry.Etale.instSmooth`, the reverse implication without a fibre condition.
- `msearch.py ... grep "topologicalKrullDimAt|[Ee]tale.*[Dd]im|[Dd]im.*[Ee]tale"
  AlgebraicGeometry`: five hits, all in Mathlib's Etale module about
  `Etale.iff_smoothOfRelativeDimension_zero` and its proof, not the present assertion.
- `rg -n` with `topologicalKrullDimAt|etale.*(fiber|fibre|dim)|Etale.*(fiber|fibre|Dim)`
  over both `WeilConjectures` and `lean/Sheaf`, followed by narrower reads in the
  algebraic-geometry trees: source `Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`,
  `topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`,
  `smoothOfRelativeDimension_of_fiberToSpecResidueField`, and scheme fibre dimension
  comparison modules were found and inspected. None states this criterion; the fibre
  relative-dimension theorem requires a hypothesis on every fibre, not one point.
- `grep -rn "lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension" WeilConjectures`:
  no hits.
- Full proposed declaration name searched with `rg` in `dag/lean_names_upstream.json`,
  Mathlib, WeilConjectures and `lean/Sheaf`: no hits, so the name is fresh.

The declaration docstring contains all three DAG proof steps and their named inputs.
All six statement dependencies are reused. No new nodes or dependency modules are needed.

## Second reading by E1

I independently read the item node, its six statement-dependency nodes and their recorded
source declarations, and the delivered Lean module. No statement correction is present or
needed. There are no new definition nodes or dependency modules to review.

Object/hypothesis/conclusion checklist (each verdict is exact):

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes X, S and their morphism f | `{X S : Scheme.{u}} (f : X ⟶ S)` | Exact; arbitrary schemes, no finiteness instances. |
| Point x in X | `(x : X)` | Exact; not assumed closed. |
| s = f(x) | `f x` in the type of `f.asFiber x` | Exact; s is defined, not independently quantified. |
| Residue field of s | `S.residueField (f x)` in `f.fiber (f x)` | Exact; `Scheme.residueField` is `IsLocalRing.ResidueField` of the structure-sheaf stalk. |
| Scheme-theoretic fibre X_s | `f.fiber (f x)` | Exact; Mathlib Fiber.lean defines this as `pullback f (S.fromSpecResidueField (f x))`, the base-change dependency's prescribed construction. |
| Point of X_s corresponding to x | `f.asFiber x` | Exact; the inverse of `fiberHomeo` at x, with `fiberι_asFiber` verifying its projection. |
| Given open subscheme U containing x | `(U : X.Opens) (hx : x ∈ U)` | Exact; the theorem is parametrized by the given witness U, as required by the conclusion U' contained in U. |
| Smoothness only of f restricted to U | `(hSmooth : Smooth (U.ι ≫ f))` | Exact; `U.ι` includes the open subscheme with its restricted structure sheaf. No smoothness away from U. |
| Dimension of the fibre at its corresponding point is zero | `(hDim : topologicalKrullDimAt (f.asFiber x) = 0)` | Exact; dimension is on open neighbourhoods of that fibre point, not the local ring dimension. |
| Existence of an open subscheme U' | `∃ U' : X.Opens` | Exact. |
| U' contained in the given U | `U' ≤ U` | Exact. |
| U' contains the original x | `x ∈ U'` | Exact. |
| f restricted to U' is étale | `Etale (U'.ι ≫ f)` | Exact; étale on all of U', with target S. |

Dependency audit: I read `Scheme` in Mathlib Scheme.lean, `residueField` and
`Hom.residueFieldMap` in ResidueField.lean, the six recorded declarations and conventions in
`Sheaf.AlgebraicGeometry.BaseChangeConventions`, `Smooth` and
`SmoothOfRelativeDimension` in Mathlib Morphisms/Smooth.lean, `Etale` and
`Etale.iff_smoothOfRelativeDimension_zero` in Morphisms/Etale.lean, and
`topologicalKrullDimAt` in WeilConjectures/Mathlib/Topology/KrullDimension.lean.
The latter definition is literally the infimum of the dimensions of open neighbourhoods;
its ambient assumptions are only a type and a topology. The fibre/point implementations
are in Mathlib Fiber.lean. All notions needed by the signature already exist; no private
replacement, extra ring/field structure, or additional instance is introduced.

Sources independently checked: the local literature tree has no Stacks .tex checkout.
I read the actual upstream raw `morphisms.tex` at labels
`lemma-smooth-omega-finite-locally-free`, `definition-smooth-relative-dimension`,
`definition-etale` (including its following remark), and `more-morphisms.tex` at
`lemma-check-smoothness-on-infinitesimal-nbhds`, as well as the tag pages
[02G1](https://stacks.math.columbia.edu/tag/02G1),
[02G2](https://stacks.math.columbia.edu/tag/02G2),
[02GI](https://stacks.math.columbia.edu/tag/02GI), and
[0A43](https://stacks.math.columbia.edu/tag/0A43).
The general criterion is justified by 02G1 and the remark after 02GI, which have no
Noetherian, separatedness, or quasi-compactness assumptions. The finite-type and locally
Noetherian assumptions of 0A43 concern the preceding infinitesimal lifting argument;
they do not restrict the general criterion extracted here. Thus their omission is correct.

Edge cases: empty X (including spectra of zero rings) and empty S cannot supply the
required point and morphism; U empty cannot supply hx. The fibre over f(x) has the actual
point `f.asFiber x`, so no empty-fibre dimension ambiguity occurs. The case of relative
dimension zero is included directly, with no positivity hypothesis. Other components of
the fibre may have different dimensions. Generic/nonclosed points, all characteristics,
and arbitrary base schemes are allowed. There is no index set in this statement.
The universe u is explicitly bound and arbitrary; both schemes live in the same category
of schemes, with no restriction to small or finite objects. Every variable is bound.

Independent searches (2026-10-11), using different formulations from the first reader:

- LeanFinder through `msearch.py`: "A smooth scheme morphism at a point whose fibre has
  dimension zero admits an etale open neighbourhood". Eight hits: reverse implication
  étale implies smooth, ring étale loci, and smooth charts; none is this criterion.
- Loogle through `msearch.py`: `AlgebraicGeometry.Etale, topologicalKrullDimAt`.
  No hits; the service does not know the source-only local-dimension identifier.
- LeanSearch through `msearch.py`: "smooth morphism etale on an open neighbourhood if
  dimension at point of fibre is zero". Service returned Internal Server Error;
  recorded as unavailable, with no negative verdict inferred.
- `rg` over Mathlib/AlgebraicGeometry, WeilConjectures, and the repository lean/Sheaf:
  `etale.*(dimension|krull|asFiber)|(?:dimension|krull|asFiber).*etale|smooth.*zero`,
  followed by `topologicalKrullDimAt|dimension.*zero|zero.*dimension` on the relevant
  algebraic-geometry trees. Mathlib's equivalence with globally smooth relative
  dimension zero is not the pointwise neighbourhood assertion. I opened the source
  declarations `Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`,
  `topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`, and
  `smoothOfRelativeDimension_of_fiberToSpecResidueField`; their conclusions/hypotheses
  differ. No exact existing declaration was found.

Mismatch/change audit: none found in the node, signature, or three-step proof docstring.
The docstring tracks the open-fibre comparison, free differentials of rank zero, and
étaleness on the resulting affine neighbourhood, with the DAG inputs explicitly named.
The module has only one theorem, whose proof is `sorry`, and no definitions or proved
auxiliary statements. Source/blueprint docstrings, namespace, explicit universe, line
width, and the node's verbatim `lean.statement` are correct. I preserved the Lean and node
unchanged and appended this independent review only.
