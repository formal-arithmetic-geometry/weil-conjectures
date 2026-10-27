## Worker report

The delivery states `Complex.Taylor.weightedTaylorBanachModel` in
`Sheaf.Analysis.Complex.WeightedTaylorBanachModel`. Its sole postponed theorem is
`∃ M : BanachModel, @BanachModel.Spec M`, proved by `sorry`. The model packages
structures on explicitly constructed coefficient and germ subtypes. Its specification
fixes every operation, norm and germ map by the actual coefficients or representatives.
No chosen unknown object, arbitrary comparison map, new axiom or proved theorem occurs.
The target's prose statement and twelve-step proof are unchanged.

Source read: Jean Frenkel, Séminaire Henri Cartan 1951–52, exposé 10,
https://www.numdam.org/item/SHC_1951-1952__4__A10_0.pdf, §4, printed pp.6–7
(convergent series defined by absolute coefficient majorants and analytic functions
at the origin), and §5, pp.7–9 (convergence argument). The PDF is not present in
literature, so it was read online. As the original node already records, the complete
weighted Banach formulation is agent supplied rather than a verbatim theorem in
Frenkel. Also read the current blueprint's
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
part (3); this is the inherited supporting local analytic/GAGA prerequisite chain,
not a change of that unit's statement or proof route.

Hypotheses and clauses, in statement order:

- `d : ℕ` includes every finite dimension, zero included. `Polyradius d` is exactly
  `{ρ : Fin d → ℝ // ∀ i, 0 < ρ i}`; positivity is built into the radius data and no
  uniform radius for all germs is assumed.
- `AnalyticGerm d` is the subtype of `Filter.Germ (𝓝 (0 : Fin d → ℂ)) ℂ` admitting
  an `AnalyticAt ℂ f 0` representative. `Filter.Germ` is the existing quotient by
  eventual equality. Thus equality is agreement on a neighbourhood of zero. Taking
  total representatives imposes no extension requirement: values outside the local
  domain can be arbitrary. No global analyticity is required.
- `weight ρ α = ∏ i, ρ.val i ^ α i`. The finitely supported multiindices
  `Fin d →₀ ℕ` encode all of `ℕ^d`, since the coordinate set is finite.
- `CoefficientSpace ρ` consists exactly of `MvPowerSeries (Fin d) ℂ` families
  with `Summable (fun α ↦ ‖c α‖ * weight ρ α)`. For this nonnegative real family,
  summability is precisely the finite absolute weighted sum requirement. The
  separate `coefficientNorm` definition is that sum, not a pre-existing product
  topology or supremum norm.
- `BanachModel.coefficientRing` and `.coefficientAlgebra` give the normed unital
  complex algebras. `Spec.coefficient_operations` provides an algebra homomorphism
  to `MvPowerSeries` whose value is exactly the underlying family. Consequently
  addition/scalars are coefficientwise, multiplication is the existing finite
  antidiagonal convolution, and the unit is the family supported at zero.
  These are not structures selected without normalization.
- `Spec.norm_eq` identifies their norm with `coefficientNorm`. Submultiplicativity
  is a field of the `NormedCommRing` structure. `BanachModel.complete` is
  `CompleteSpace` for the very metric/uniformity in that ring structure. Since
  this is a metric space, this is equivalent to the node's Cauchy-sequence
  convergence clause; no different topology or extra completeness assumption occurs.
- `Spec.convergence` asserts absolute summability of `c.val α * monomialValue α z`
  at every `z ∈ polydisc ρ`, together with `AnalyticOnNhd ℂ (seriesValue c)` on
  that same open polydisc. Thus analyticity is at every interior point, not only
  at zero. Both monomial and series evaluation are explicit definitions.
- `BanachModel.germRing` and `.germAlgebra`, normalized by
  `Spec.germ_operations` and `.germ_scalar`, are exactly pointwise germ operations.
  The ring inclusion is the underlying subtype inclusion, and scalar action is
  the existing pointwise scalar action on `Filter.Germ`.
- `Spec.gamma` asserts a family of `ℂ`-algebra homomorphisms `γ d ρ` with
  `(γ d ρ c).val = Filter.Germ.ofFun (seriesValue c)` and `Function.Injective`.
  This fixes the canonical map by its representative; it is not an arbitrary
  injective homomorphism. A single existential binds the same family for all
  subsequent comparison clauses.
- The next gamma conjunct is `∀ d g, ∃ ρ c, γ d ρ c = g`: every germ is represented
  at some positive radius. It does not incorrectly demand a common radius.
- For positive `ρ σ` with `∀ i, σ.val i ≤ ρ.val i`, a homomorphism `r` has
  `(r c).val = c.val`, `‖r c‖ ≤ ‖c‖`, and `γ d σ (r c) = γ d ρ c`.
  This is the coefficient-preserving radius transition with the specified bound
  and commutation. Equality of the radii is included.
- Every coordinate subspace is represented by `e : Fin k ↪ Fin d`.
  `coordinateRadius e ρ` retains its radii and `coordinateInclusion e` inserts
  zero outside its image. Its restriction map satisfies
  `(r c).val α = c.val (α.embDomain e)`: exactly the exponents zero outside the
  retained coordinates survive. For every representative of `γ d ρ c`, the
  gamma conjunct asserts that its composition with this inclusion has the
  restricted series germ. In particular it is genuine germ restriction, not
  merely a formula on a selected representative. Algebra preservation follows
  from the same coefficient convolution and is included in the map type.
- For every `ρ : Polyradius 0`, algebra equivalences to `ℂ` identify a coefficient
  family with its coefficient at `0`, and a germ with its constant representative;
  the displayed square says gamma becomes the identity under these identifications.
  These are the precise mathematical identifications `A_ρ = G_0 = ℂ`.

Dependency interfaces read and used:

- `lem-sfb-complex-analytic-function-operations` is a Mathlib leaf, not a missing
  Lean record. Read its recorded declarations in full: `analyticAt_const`,
  `AnalyticAt.add`, `AnalyticAt.mul`, `AnalyticAt.inv`, `AnalyticAt.pi` in
  `Mathlib.Analysis.Analytic.Constructions` (54, 106, 639, 1020, 560);
  `ContinuousLinearMap.analyticAt` in `Mathlib.Analysis.Analytic.Linear` (61);
  `AnalyticAt.comp` in `.Composition` (859); and `AnalyticAt.continuousAt`
  in `.Basic` (1046). Its `AnalyticAt` notion is used directly in the germ
  subtype, re-exported by the public import of `AnalyticGerm`.
- The norm in `def-weil-complex-absolute-value` is Mathlib's complex norm:
  `Complex.instNorm` and `Complex.norm_def`, `Mathlib.Analysis.Complex.Norm`,
  lines 26–29. The coefficient definition imports complex normed field structure.
- Proof-only imports supply the recorded Mathlib leaves:
  `lp.norm_eq_tsum_rpow`, `lp.normedAddCommGroup`, `lp.instNormedSpace`,
  `lp.completeSpace` in `Mathlib.Analysis.Normed.Lp.lpSpace`;
  `Summable.of_norm_bounded`, `tsum_of_norm_bounded`, `summable_of_sum_le`,
  `Real.tsum_le_of_sum_le` through the normed infinite-sum imports;
  `Summable.mul_norm`, `summable_mul_of_summable_norm`,
  `tsum_mul_tsum_of_summable_norm` in `Mathlib.Analysis.Normed.Ring.InfiniteSum`;
  `HasSum.tsum_fiberwise` in `Mathlib.Topology.Algebra.InfiniteSum.Constructions`.
  Read the relevant definitions/signatures and source comments. The proof dependency
  `lem-sfb-monomial-series-coordinate-derivatives` presently has neither a Lean
  record nor Mathlib match; it is cited in the full proof docstring and has no
  module to import. It is not needed to type the statement. No dependency was
  privately redefined or silently replaced.

Edge cases checked before and after drafting: empty coordinate sets, the singleton
multiindex set in dimension zero, zero families, the supported-at-zero unit,
constants, equal/shrinking radii, retaining every coordinate, retaining none, and
arbitrary relabellings of retained coordinates. All weights are strictly positive,
including the empty product. Only interior analyticity is asserted; no boundary
holomorphy or convergence of differentiated boundary series is asserted.

Searches actually run through `msearch.py Q48 lem-sfb-weighted-taylor-banach-model`:

- LeanFinder: `Weighted l1 Banach algebra of multivariate complex Taylor coefficients
  embeds in analytic germs`: eight hits including `analyticOn_taylorComp`,
  `WithLp.analyticOn_ofLp`, `PiLp.analyticOn_ofLp`, `CPolynomialAt.analyticAt` and
  `AnalyticAt.hasFPowerSeriesAt`; no weighted coefficient/germ model.
- Loogle: `lp, Summable, Filter.Germ`: OK, zero hits.
- LeanSearch: `weighted absolutely summable complex multivariate power series Banach
  algebra`: eight hits including `MvPowerSeries.hasSum_aeval`,
  `FormalMultilinearSeries.le_radius_of_summable_norm` and unrelated weighted order
  results; none is the claimed Banach/germ model.
- Grep: `weighted|Weighted|convolution` in `Analysis/Normed/Lp`: OK, zero hits.
- LeanFinder: `Subtype of multivariate complex power series with summable weighted
  absolute coefficients and subtype of analytic germs at zero`: eight hits,
  specifically `AnalyticAt`, `HasFPowerSeriesAt`,
  `FormalMultilinearSeries.analyticOnNhd`, `PowerSeries.IsRestricted`,
  `hasFPowerSeriesAt_iff`, `HasFPowerSeriesAt.analyticAt`,
  `HasFiniteFPowerSeriesOnBall`, `HasFPowerSeriesWithinAt`; none defines our subtypes.
- LeanSearch: `Weighted Taylor coefficient space and analytic function germs at the
  origin`: eight hits including `taylorCoeffWithin`, `AnalyticAt` and its formal
  series existence lemmas; none defines the weighted subtype or analytic germ subtype.
- Grep: `AnalyticGerm|analyticGerm|WeightedTaylor|weightedTaylor`: OK, zero hits.
  Direct `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` also found no declaration of our notions.
  Broader germ/Taylor searches in the project found only other analytic inputs,
  analytic function sheaves, and unrelated sheaf stalks. A search for the exact
  item id in `lean/WeilConjectures` found no match.
- DAG searches for analytic germs at zero and weighted coefficients found the
  item and its Weierstrass/derivative/jet consumers, not a definition node.
  The project `SmoothAnalyticData` defines holomorphic function sheaves on an
  atlas, not this germ subtype or coefficient space; its declarations were read.
  `tools/blueprint_refs.py search 'weighted Taylor'` and `search 'holomorphic germ'`
  each returned zero blueprint nodes. `ancestor` returned `None`, consistently
  with the item's inherited null ancestor; the full inherited via chain is retained.

Validation: all three delivery modules compiled separately in dependency order
using the prescribed `scompile.py`, both as sandbox probes and actual library
module names. No errors and no non-sorry warnings remain. Initial compile probes
caught a missing direct complex import and the wrong uniform-space projection;
both were repaired. Instance-producing model projections have explicit
`instance_reducible` attributes. `autoImplicit` is false throughout, and all
lines are at most 100 characters. The theorem docstring reproduces all twelve
proof steps and their dependency ids.

## New nodes

`def-sfb-weighted-taylor-coefficients` defines positive polyradii, weights,
the summable coefficient subtype, its sum-norm function, monomials, series sums,
open polydiscs and coordinate inclusions/radii. Source: Frenkel §4, pp.6–7,
and the exact agent-supplied formulas already in the item. It cites
`def-weil-complex-absolute-value`. Mathlib's `MvPowerSeries` supplies the actual
coefficient indexing and finite convolution rather than a second formal-series
multiplication. Generic l1 and formal-series spaces do not define this weighted
subtype. The actual three search kinds and their results are in its JSON record.
All definitions have real data and contain no postponed proofs.

`def-sfb-complex-analytic-germ` defines only the subtype of the existing
`Filter.Germ` quotient admitting a locally power-series analytic representative.
Source: Frenkel §4, pp.6–7. It cites and uses the `AnalyticAt` notion in
`lem-sfb-complex-analytic-function-operations`. Existing `Filter.Germ` represents
all functions, so is not by itself the required analytic germ subtype. No existing
DAG node defines this object. The same actual specialized three-kind searches
apply and are recorded in its JSON record. Pointwise algebra laws remain part
of the target theorem rather than hollow instance definitions.

## Second reading by Q48

This is the dispatcher's required author's second reading; the maintainer supplies
the independent review. I reopened the node statement and all three modules and
matched their hypotheses and conclusions in the order listed above. I specifically
checked that the two structure packages do not lose the canonical operation data:
the coefficient algebra inclusion fixes convolution and the supported unit; the
norm equality fixes the metric; the germ ring inclusion plus scalar formula fixes
pointwise complex algebra operations; and the gamma representative equality fixes
the canonical germ map. The same gamma family occurs in surjectivity, both kinds
of restriction, and the zero-dimensional comparison.

I checked that using an arbitrary representative in coordinate restriction is
well-defined mathematically, since the coordinate inclusion is continuous and
preserves zero. `α.embDomain e` inserts zero exponents, while
`coordinateInclusion e` inserts zero coordinate values; these are the two different
maps needed for the clause. No coordinates are accidentally forced nonempty.
The zero-dimensional clause is an algebra equivalence with the coefficient/constant
germ normalizations, not an unsupported definitional equality. The analytic
predicate applies on the full polydisc, not just at zero, and the germ subtype
requires only analyticity at zero. There is no hidden global continuation assumption.
No mathematical mismatch, disputed statement or source correction remains.

## Source error

Frenkel §4, printed p.7, explicitly says in a parenthetical sentence that the
fixed-radius normed algebra is not complete. This disagrees with the explicit
space in the assigned node when every coefficient family with finite absolute
weighted sum is admitted. That space is complete: multiplication by the positive
weights is a linear isometry onto the entire complex l1 space, with inverse
coordinatewise division by the weights. Its inverse always gives a convergent
series on the open polydisc, including when the sum on the boundary is finite.
Thus the assigned complete-space formulation is correct independently of that
parenthetical claim. No correction to the DAG statement is made. This discrepancy
must be kept visible to the maintainer's independent review; the source is used
for its majorants and analytic-at-the-origin notion, not as a quoted completeness
theorem. The original node already labels the complete formulation agent supplied.

Final dry run: `deliver2.py Q48 lem-sfb-weighted-taylor-banach-model --no-push`
printed `OK (dry run): commit 2201a77cfa9 passes the preflight and compiles; nothing pushed`.
