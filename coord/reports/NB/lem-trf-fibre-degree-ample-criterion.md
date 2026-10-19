## Worker report

The new module `Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos` states
`AlgebraicGeometry.Scheme.Modules.isAmple_iff_normalizedComponentDegree_pos`, with
`sorry` as its entire proof. No definition is added, no theorem is proved, and no
natural-language statement or dependency is changed. The item's node copy changes
only `lean`.

The prior message saying that NX already delivered this item refers to its stage-1
split at 98ce9222219e9a4d04343963a3696360e2bb4010. That commit added the proof plan
and two supporting nodes; the current item still had no `lean` field. This delivery
supplies its stage-2 statement rather than repeating the split.

Hypotheses and conclusion, checked against the node and Stacks Varieties 0B5Y:

- The arbitrary field is `(k : Type u) [Field k]`. No algebraic closure, perfectness,
  characteristic restriction, or global-sections hypothesis is imposed.
- The scheme over this field is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`. The
  structure morphism is the recorded `X ↘ Spec (.of k)`.
- Properness over the original field is `[IsProper (X ↘ Spec (.of k))]`.
- Topological dimension at most one is `(hdim : topologicalKrullDim X ≤ 1)`.
  The value belongs to `WithBot ℕ∞`, so the empty scheme, of dimension bottom,
  is included.
- The invertible module is `(M : X.Modules) [M.IsInvertible]`, using the recorded
  `Scheme.Modules.IsInvertible`, rather than a different sheaf predicate.
- Absolute ampleness is the left side `Scheme.Modules.IsAmple X M`, from the
  recorded `WeilConjectures.AlgebraicGeometry.Ample`. This is the compactness and
  affine nonvanishing-locus definition, not the field-relative projective-space
  predicate `AlgebraicGeometry.IsAmple` in the older source.
- The equivalence is `↔`, so both directions are stated.
- The one-dimensional irreducible components of the reduction are represented by
  `∀ (C : Scheme.{u}) [IsIntegral C] (i : C ⟶ X), IsClosedImmersion i →
  Set.range i ∈ irreducibleComponents X → topologicalKrullDim C = 1 → ...`.
  These are precisely all representatives of the reduced induced component schemes:
  integrality implies reducedness; the closed immersion identifies the carrier
  with an irreducible component; and a reduced closed subscheme with that image is
  unique up to unique isomorphism over X, by the existing
  `reduced_induced_closed_subscheme` theorem. Conversely the reduced induced
  structure on every component is integral. Reduction is a homeomorphism, so its
  components and dimensions are those of X. There is no extra global hypothesis
  `[IsIntegral X]` or `[IsReduced X]`. Quantification over representatives avoids
  choosing or redefining a component construction and agrees with the component
  encoding used by `MarkedNodalDualizingDegrees` in the published side library.
- The normalization is the recorded `C.normalization`, with canonical map
  `C.fromNormalization`. It is normalization in the component's own function field,
  not an arbitrary normal cover and not a smooth model.
- The pullback is exactly `(Scheme.Modules.tensorPullback
  (C.fromNormalization ≫ i)).obj M`, using the recorded tensor-formula functor.
- Degree is the recorded `Scheme.Modules.degree`. Its `Over` instance is supplied
  explicitly as `⟨C.fromNormalization ≫ i ≫ (X ↘ Spec (.of k))⟩`. Thus the Euler
  characteristics are over k, with the induced structure map, and no unrelated
  field structure on the normalization is quantified over. The `@` application
  directly supplies this instance; there is no `let`/hidden `have` in the statement.
- Strict positivity is `0 <` that integer degree. The antecedent
  `topologicalKrullDim C = 1` excludes point components from the tests. No condition
  on their degree, number, or presence is added.

Dependencies read and used (module followed by declarations):

- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`. Read the live source via
  `scompile.py --source`, since the older local slopmaster2 checkout lacks this file.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; its full signature and local
  trivialization docstring were read in the pinned source.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`, the integer Euler-characteristic
  difference with `[X.Over (Spec (.of k))]`, read with its entire docstring.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `Scheme.fromNormalization`, read
  with their integral-scheme hypothesis and function-field construction.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, read in the live source through
  `scompile.py --source`; its real data is inverse image, extension of scalars and
  sheafification. The statement never substitutes Mathlib's module pullback.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and
  `AlgebraicGeometry.IsIntegral`; the former is implied by the latter on C.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`. This dependency has
  `mathlib_match` instead of `lean`; that recorded declaration was read directly.

The module also imports all available proof-dependency modules: Mathlib
`AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.Morphisms.Finite`,
`RingTheory.Noetherian.Defs`, and upstream
`AlgebraicGeometry.ReducedInducedClosedSubscheme` and
`AlgebraicGeometry.Modules.InvertiblePullbackTensor`. The latter two source
interfaces were read via `scompile.py --source`. Proper composition and finite
properness are in the already public Proper module; normalization existence and
its dimension theorem are in the normalization module. The scheme sobriety
instances and integral predicate are in Properties. The two proof dependencies
`lem-trf-finite-surjective-ample-reflection` and
`lem-trf-proper-integral-curve-ample-degree` have no Lean records yet, hence no
module to import. Their use is preserved in the complete six-step proof docstring;
these are proof inputs and are not needed to elaborate the statement. No import
cycle was introduced.

Sources checked: local Stacks `varieties.tex`, labels
`lemma-ampleness-in-terms-of-degrees-components` (0B5Y), `lemma-ample-curve` (0B5X),
`lemma-normalization-locally-algebraic` (0BXR), and
`lemma-degree-pullback-map-proper-curves` (0AYZ). Stacks 0B5Y states the component
criterion; 0BXR provides finite birational normalization; 0AYZ explains unchanged
degree under its degree-one pullback. The node's proof instead applies finite
surjective ampleness reflection directly to the normalized-component cover, as
its docstring records. Nothing requires smoothness over an imperfect field.

Edge cases checked before writing:

- X empty: the dimension bound admits bottom; no nonempty integral component can
  immerse into X. Positivity is vacuous, and the ampleness predicate's compactness
  and pointwise section condition hold for the empty scheme.
- A proper zero-dimensional scheme, including a nonreduced finite scheme such as
  Spec(k[epsilon]/epsilon^2): it has no dimension-one components; ampleness holds
  for every invertible module, without a degree-zero contradiction.
- A curve with a disjoint isolated point: the point imposes no additional test.
- A reducible curve with positive total degree but nonpositive degree on one
  component: this statement tests each component separately, so total positivity
  alone cannot satisfy its right side.
- Singular integral curves, including a nodal curve: C is the reduced component,
  and the degree test is on C.normalization. No smoothness of C is assumed.
- Imperfect fields: the canonical normalization may fail to be smooth over k;
  the signature contains no smoothness or geometric-integrality assumption.
- P^1 with O(d): d positive, zero, and negative give the expected strict-positive
  criterion. For P^1_K over a finite extension K/k, the degree is measured over k
  and equals [K:k] times the usual degree; the sign criterion is unchanged.
- Different representatives of the same reduced component are isomorphic over X.
  Canonical normalization and tensor pullback transport along that isomorphism,
  and Euler degree is invariant under it; the universal representative formulation
  therefore has precisely the node's content.

Searches actually run for an existing statement:

- `msearch.py leanfinder`, query: "A line bundle on a proper scheme over a field of
  dimension at most one is ample if and only if its degree is positive on the
  normalization of every one-dimensional irreducible component". Eight hits:
  morphism normalization, its maps, dominance, affineness and integrality; none is
  an ampleness/degree criterion.
- `msearch.py loogle`, query: `"IsAmple", "degree"`. Zero hits.
- `msearch.py grep`, query: `isAmple.*degree|degree.*normalization|ample.*component`
  in Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py leansearch`, query: "A line bundle is ample on a proper curve
  precisely when its pullback to every normalized irreducible component has
  strictly positive degree". Eight hits concern topological vector bundle
  pullback, normalization morphisms, additive module pullback, finite properness,
  convex ample sets and affine pullbacks; none states the item.
- `rg` and `grep -rn` of the item id in upstream WeilConjectures: no declaration.
  `rg` in upstream and `lean/Sheaf` for ampleness, degrees and normalized components
  found the related RiemannRoch theorem and the side module
  `MarkedNodalDualizingDegrees`, not the item. Broad degree/component hits concerned
  unrelated graded modules, cochain complexes, and group-scheme degree components.
- `rg isAmple_iff_degree_pos` led to
  `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1519`. Read its full
  signature, docstring and enclosing hypotheses. It assumes a smooth proper curve
  and GlobalSectionsBijective k X, and uses `AlgebraicGeometry.IsAmple`, so it
  cannot bind this arbitrary dimension-at-most-one, possibly reducible/nonreduced
  absolute-ampleness criterion.
- Checked the new declaration name in Mathlib, upstream WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py NB lem-trf-fibre-degree-ample-criterion
lean/Sheaf/AlgebraicGeometry/AmpleIffNormalizedComponentDegreePos.lean` exited zero.
Its sandbox check took 11.1 seconds and its actual module check took 16.4 seconds;
both had no errors or warnings. Universes and all variables are explicitly bound,
with `autoImplicit` and `relaxedAutoImplicit` set false. Only the required named
statement has `sorry`. No new node, dependency repair or statement correction is
needed, and there is no STATEMENT-DISPUTED finding.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
