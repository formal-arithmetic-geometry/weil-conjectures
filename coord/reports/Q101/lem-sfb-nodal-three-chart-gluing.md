## Worker report

The module `Sheaf.AlgebraicGeometry.NodalThreeChartGluing` states
`AlgebraicGeometry.NodalThreeChart.gluing`. Its sole theorem has proof `sorry`.
The three helpers `left`, `right`, `scalar` have real data: they restrict the
published quotient coordinate classes or coefficient to the actual scheme pullback
intersection, using its projections and `Scheme.ΓSpecIso`. They introduce no second
binomial ring, nodality predicate, regularity predicate, or gluing construction.
No node statement or other field has been changed; only the item's `lean` is set.

Hypothesis-by-hypothesis correspondence:

- A DVR R: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  A uniformizer: `π` and `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`.
  The exponent: `n : ℕ`, `hn : 2 ≤ n`.
- The R-scheme Z: `Z : Scheme.{u}` and `f : Z ⟶ Spec (.of R)`.
  The morphism is explicit since the statement also uses base change.
- The three displayed chart rings: the existing `BinomialPlaneCurve.curve R π`,
  `curve R (π ^ (n - 2))`, `curve R π`. Their respective coordinates 0,1
  are x,t; r,s; y,h. `ix`, `im`, `iy` and their `IsOpenImmersion` instances
  identify them with open subschemes of Z. `hcover` says precisely that their
  images cover Z. `hx`, `hm`, `hy` make these identifications over R.
- First overlap `D(t)=D(r)`: `hxm` and `hmx` specify the inverse images of the
  two chart ranges as those principal opens. `htr` is tr=1, hence r=t⁻¹;
  `hs` is s=x^(n-2)t^(n-1); `hxr` is x=πr.
- Second overlap `D(h)=D(s)`: `hym`, `hmy` give the opens. `hhs` is hs=1,
  `hr` is r=y^(n-2)h^(n-1), and `hys` is y=πs.
- Outer overlap: `hxy` specifies D(x^(n-2)t^n) in the x-chart; `hyx` gives
  the symmetric open in the y-chart. `hyy` is y=x^(n-1)t^n, and `hh` is
  h*(x^(n-2)t^(n-1))=1. This is the regular-function interpretation of h=π/y,
  since xt=π and y=x^(n-1)t^n. It records the transition everywhere, including
  the n=2 special fibre, rather than dividing a zero-divisor after base change.
  `hxx` and `ht` record exactly the symmetric inverse.

Conclusion-by-conclusion correspondence:

- Flatness: `Flat f`.
- Local finite presentation: `∃ hfp : LocallyOfFinitePresentation f, ...`;
  the proof is supplied explicitly as the instance parameter of the existing
  `@HasNodalGeometricFibres _ _ f hfp`, with no hidden let binder.
- Nonempty, connected, one-dimensional nodal geometric fibres:
  `HasNodalGeometricFibres` is exactly the dependency predicate, quantifying over
  every algebraically closed field and every map from its spectrum. Its
  `ConnectedSpace` includes nonemptiness, its dimension is topological dimension
  exactly 1, and its nonsmooth stalk completions are Ω[[u,v]]/(uv).
- Reduced geometric fibres: the additional universally quantified
  `IsReduced (pullback f g)`; this clause is not built into the nodality predicate.
- Generic fibre is the Laurent line: an isomorphism of the pullback along
  `Spec.map (algebraMap R (FractionRing R))` with
  `Spec (.of (LaurentPolynomial (FractionRing R)))`. The projection compatibility
  states that this is an isomorphism over the fraction field.
- Regular outer charts: `IsRegularScheme (curve R π)`. Both chart domains are
  the identical scheme, so this single assertion covers both.
- Only possible nonregular point: for every `z`, failure of regularity of the
  actual stalk implies `4 ≤ n` and that z is the image under `im` of the point
  with prime ideal `(π,r,s)`. The fixed open immersion `im` from the displayed
  middle chart supplies exactly the asserted open local model. A prime ideal
  specifies its point uniquely; no origin is chosen from an unspecified theorem.
- For n=2: smoothness of the middle structural morphism, an R-compatible
  isomorphism of that chart with `Spec R[z,z⁻¹]`, and `IsRegularScheme Z`.
- For n=3: `IsRegularScheme` of the middle chart and of Z.
- Every algebraically closed extension and every residue characteristic:
  the universal Ω-test is the dependency's scheme-universe convention;
  there is no characteristic, completeness, perfection or excellence assumption.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`;
  the exact maximal-ideal formulation is used.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme.Hom.appTop`; `Scheme.ΓSpecIso` is the canonical section identification.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; the two-variable quotient
  uses the existing `MvPolynomial (Fin 2)` ring in the published chart module.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with its
  affine-local docstring and stalk equivalence read.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, its full affine-local class.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`:
  `AlgebraicGeometry.HasNodalGeometricFibres`, full definition and docstring read.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme = IsLocallyNoetherian ∧ IsRegular`;
  `WeilConjectures.AlgebraicGeometry.Regular` supplies the existing stalk class
  `AlgebraicGeometry.IsRegular`.
- The already recorded proof dependency
  `Sheaf.AlgebraicGeometry.BinomialGeometricFibres` supplies its existing
  `BinomialPlaneCurve.Ring`, `coord`, `curve`, `toField`; their full definitions
  were read, as were its geometric-properties and base-change statements.
  These concrete chart specializations abbreviate precisely the quotient rings
  in the node, and the public module also supplies the Laurent polynomial ring.

The imports also retain stated proof dependencies for stage 3: DVR dimension
(TFAE), ring-flat localization, affine stalk localization, standard smoothness,
open-cover Krull dimension, and the binomial geometric-fibre theorem. The two
unstated proof nodes `lem-sfb-dvr-binomial-local-geometry` and
`lem-sfb-monomial-local-completion` have no usable recorded module in the read
clone, so there is no module to import for them; they are only proof prerequisites,
not objects missing from this statement. Their names and uses are in the proof
docstring. No missing statement notion or new dependency module was needed.

Edge cases checked before writing and again against the signature: n=2 gives
rs=1, so the middle chart is already in both adjacent opens and the outer
intersection is D(t²)=D(t), not empty; the total-space fraction π/y is expressed
by a regular inverse and remains defined on the special fibre. For n=3 every
chart has exponent one. For n=4 the middle exponent is two, with origin the only
possible failure; higher n has the same location. The geometric adjacent opens
are Laurent lines even when π maps to zero, with t=1 and h=1 witnesses, so the
connectedness proof never relies on the outer intersection being nonempty.
Nonzero π, nontriviality and nonfieldness follow from the DVR uniformizer
hypothesis. No characteristic-two exception occurs. The empty Z cannot satisfy
this open cover, since its chart domains are nonempty; there is no extra
nonempty binder. The generic fibre comparison is over the fraction field,
not only an abstract scheme isomorphism.

Searches for an existing theorem:

- `msearch.py ... leanfinder`: “Gluing three affine curves xy equal to uniformizer
  powers over a DVR using reciprocal overlap coordinates gives connected nodal
  fibres and regularity”. Eight elliptic-curve good-reduction/minimality hits;
  no three-chart gluing theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Scheme, AlgebraicGeometry.Flat`.
  Twelve general flatness and base-change hits; no explicit gluing theorem.
- `msearch.py ... leansearch`: “Three explicit affine binomial charts over a
  discrete valuation ring glued by inverse coordinates have connected nodal
  geometric fibres and a unique possible nonregular point”. Eight hits on
  affine covers, affine fibres and smoothness, none the theorem.
- `msearch.py ... grep`: `(Nodal|nodal|[Tt]hree[Cc]hart)` in AlgebraicGeometry.
  No Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `three.chart|ThreeChart|nodal_three|nodal.*gluing|BinomialPlaneCurve`.
  Found the existing binomial-coordinate API used here, the parent nodal
  blowup calculation, the symmetric-blowup theorem and unrelated scalar gluing;
  no theorem on an arbitrary Z with exactly this cover and these overlaps.
- `grep -rn lem-sfb-nodal-three-chart-gluing lean/WeilConjectures`: no hits.
  `rg` in DAG nodes found this item, its parent, and the distinct exceptional-
  curve and chart-algebra calculations. Their statements are not this gluing
  assertion. Read the latest blueprint direct-images proof clause (3) and the
  actual source curves.tex nodal-family lemma/definition; those tags provide
  local nodal context, not the global connectedness assertion.

No statement dispute or correction. The apparent π/y issue is rational-expression
notation for a uniquely determined regular transition, rendered by its explicit
inverse identity; the statement and its symmetric inverse are preserved.

Validation: `scompile.py Q101 lem-sfb-nodal-three-chart-gluing <module>` passes
both the sandbox and named library module (2.2 s and 2.3 s), without errors or
unexpected warnings. The initial principal-open coercion mismatch was repaired
using `.carrier`; all variables and universes are explicitly bound.

## Second reading by Q101

This is the dispatcher's single-worker self-reading, not a claim of an independent
agent review; the delivery receives the maintainer's independent reading.
Reopened the original node and the final module together. Checked all R, π, n,
Z, cover, over-base and six overlap-open hypotheses against the binders above.
Checked the three identities on each adjacent overlap and the two identities
in each outer transition direction. Specifically recomputed
π/y = 1/(x^(n-2)t^(n-1)) using xt=π, and its symmetric inverse; on D(x^(n-2)t^n)
the indicated denominator is a unit, including when n=2. Thus the identity adds
no hypothesis and loses no part of the transition.

Checked every conclusion: Flat; existential local finite presentation; the exact
recorded nodal predicate; explicit reducedness for every geometric test; generic
Laurent isomorphism with projection compatibility; the common regular outer model;
nonregular stalks only at the specified middle-origin ideal for n≥4; both n=2
clauses (smooth Laurent middle, regular Z); both n=3 clauses (regular middle and Z).
The middle open immersion in the hypotheses already is the requested local-model
identification, so no unrelated arbitrary comparison map was introduced. Read the
helper definitions to their actual restriction maps and canonical ΓSpec identification.
No additional mismatch found; the only compile repair was the open-set coercion.
No new nodes, dependency repairs or statement changes.
