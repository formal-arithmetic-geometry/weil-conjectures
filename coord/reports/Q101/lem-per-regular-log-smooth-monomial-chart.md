## Worker report

The module Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart states
AlgebraicGeometry.regular_logSmooth_monomial_chart, with one postponed theorem
proof. Its two helpers spell out the actual polynomial quotient and its canonical
coefficient map; neither chooses data or uses a postponed result. Nothing is proved.
The source was read directly: ILO Expose XVI Definition 3.6.1 and Proposition 3.6.3,
printed p.252 (PDF p.258), and Proposition 3.6.5 with its proof, printed p.253
(PDF p.259). The source's splitting into N^r and the unit group gives precisely
the nonnegative, not-all-zero exponent tuple in the node.

Hypothesis and conclusion correspondence:

- A trait and chosen uniformizer: `(R : Type u) [CommRing R] [IsDomain R]
  [IsLocalRing R] [IsNoetherianRing R]`, `hdim : ringKrullDim R = 1`,
  `(π : R)` and `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`.
  These express the node's definition, without assuming an excellent or complete ring.
- The canonical log structure: `M : EtaleLogStructure (Spec (.of R))`, `hfs`,
  and `hcanonical`. The last is an actual natural isomorphism of the underlying
  monoid presheaf with `divisorialLogPresheaf` for the generic open D(π), commuting
  with `divisorialStructuralMap` and `M.alpha`. In a one-dimensional Noetherian
  local domain with principal maximal ideal, D(π) is the generic point. Thus this
  is exactly the subsheaf of regular functions invertible generically, not a free
  choice of log structure or a hypothesis of chart existence alone.
- An fs log scheme and morphism: `X : FineSaturatedLogScheme.{u}` and
  `f : EtaleLogHom X ⟨Spec (.of R), inferInstance, M, hfs⟩`.
  The target has exactly the prescribed scheme and log structure. The bundled
  source includes local Noetherianity, as required throughout the fs-log interface.
- Regular Noetherian source: `hregular : IsRegularScheme X.scheme` and
  `[IsNoetherian X.scheme]`. Regularity includes local Noetherianity and ordinary
  stalkwise regularity, while the separate Noetherian assumption is global.
- The node's precise log-smooth chart hypothesis is `hcharts`. For every ordinary
  point `y`, it gives `c : FSLogChart f` with `y ∈ Set.range c.V.hom`. This is an
  etale covering, with etale target neighbourhood `c.W`, fs source monoid `c.Q`,
  compatible log charts and canonical toric comparison supplied by the existing API.
  `e : c.P ≃* Multiplicative (ULift.{u} ℕ)` specifies the base chart monoid N,
  and the formula on `M.alpha ... (c.chartY p)` says its monomial has structural
  image π to the corresponding exponent, pulled back to `c.W`.
  `Function.Injective c.groupMap` is injectivity on group completions;
  `Finite (CommGroup.torsion c.cokernel)` and the `IsUnit (Nat.card ...)` tests in
  every ordinary local ring of `c.V.left` give exactly finite invertible torsion.
  `Smooth c.comparison` is smoothness of the canonical map to the actual scheme
  fibre product. No torsion-free cokernel is assumed.
- Every chosen point is `(x : X.scheme)`. Every uniformizer is covered because π
  and its generation equation are unrestricted parameters of the theorem.
- The conclusion existentially binds `U`, `a : U ⟶ X.scheme`, and `v : U`.
  `IsAffine U ∧ IsRegularScheme U ∧ IsNoetherian U` gives all three required
  properties; `Etale a ∧ a v = x` gives the etale neighbourhood and point above x.
- `n : ℕ`, `e : Fin n → ℕ`, `0 < n`, and `∃ i, e i ≠ 0` express positive length,
  nonnegative exponents and the nonzero tuple. `Fin n` is only a relabeling of 1..n.
- `monomialTraitAlgebra R π n e` is literally
  `MvPolynomial (Fin n) R ⧸ Ideal.span {(∏ i, X i ^ e i) - C π}`.
  In particular the subtraction is outside the entire product.
  `b : U ⟶ Spec (.of (monomialTraitAlgebra R π n e))` and `Etale b` give the
  required target and etaleness. The final equation
  `b ≫ Spec.map (CommRingCat.ofHom (monomialTraitAlgebraMap R π n e)) = a ≫ f.base`
  says precisely that b is an S-morphism for U's induced structure map. The ring
  map here is the quotient map composed with the polynomial coefficient map.

Dependency declarations read and used:

- def-trf-fs-log-blowup: Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup,
  `EtaleLogStructure`, `EtaleLogStructure.IsFineSaturated`,
  `FineSaturatedLogScheme`, `EtaleLogHom`, and the chart definitions.
- def-weil-regular-scheme: Sheaf.AlgebraicGeometry.IsRegularScheme,
  `AlgebraicGeometry.IsRegularScheme` (locally Noetherian and `IsRegular`).
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth`.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- Newly cited landed node def-per-fs-log-smooth-etale:
  Sheaf.AlgebraicGeometry.FSLogSmoothEtale, `FSLogChart`, `FSLogChart.groupMap`,
  `FSLogChart.cokernel`, and `FSLogChart.comparison`. Its existing general
  `EtaleLogHom.IsLogSmooth` is not copied or silently substituted: the theorem
  explicitly specifies this node's injective, uniformizer-chart specialization.
- The canonical divisorial presheaf and structural inclusion are the existing
  `divisorialLogPresheaf` and `divisorialStructuralMap` from
  Sheaf.AlgebraicGeometry.LogRegularPair, publicly supplied by the fs-log module.

Proof-only imports preserve the stated plan: LogSmoothInvertibleTorsionLogRegular
(logSmooth_invertibleTorsion_logRegular), FreeCharacteristicRegularBoundary
(FineSaturatedLogScheme.free_characteristic_regular_boundary),
EtaleSmoothZeroDimensionalFibres (smooth_and_fibre_dimension_zero_of_etale),
FsFaceSharpening (face_sharpening), Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
(AlgebraicClosure, IsAlgClosure.equiv), and Mathlib.LinearAlgebra.FreeModule.PID
(Module.basisOfFiniteTypeTorsionFree'). Noetherianity and etale cancellation are
already publicly supplied by statement imports. The proof dependency
lem-per-trait-log-smooth-uniformizer-chart has no recorded declaration, so its
module is not imported; it is not needed to type this statement. Its role is
fully described in proof step 2 of the theorem docstring. No proof is attempted.

Searches: retained searches.jsonl records the earlier LeanFinder query
"Regular log smooth scheme over a discrete valuation ring admits etale local
monomial hypersurface charts" (eight ordinary smooth-presentation hits, no match),
Loogle "IsDiscreteValuationRing, IsUniformizer" (unknown IsUniformizer, no hits),
grep "LogSmooth|logSmooth|MonomialChart|IsDiscreteValuationRing" in
Mathlib/AlgebraicGeometry (seven unrelated valuation/elliptic hits), and LeanSearch
"fine saturated log smooth chart over trait with finite invertible torsion cokernel"
(eight ordinary smoothness hits, no log notion). These are preserved from the
interrupted attempt. This continuation repeated LeanFinder with "Regular log
smooth scheme over a trait has etale local monomial hypersurface charts" (eight
ordinary smoothness or etale-site hits); repeated Loogle (same unknown identifier);
and ran msearch grep "LogSmooth|logSmooth|MonomialChart" in AlgebraicGeometry
(no hits). Direct rg for MonomialChart, regular_logSmooth_monomial_chart and this
node id in upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
found no matching theorem. Direct rg for monomialTraitAlgebra and monomial
hypersurface/trait names and polynomial products found no existing hypersurface
helper; the polynomial products found are unrelated. The landed FSLogSmoothEtale
API was opened in full and replaces the obsolete duplicate partial sandbox module,
which is retained as FineSaturatedLogSmooth.lean.retained and is not delivered.

Edge cases checked: an empty X has no x so the conclusion is vacuous; n=0 and an
all-zero tuple are expressly excluded; individual exponents may be zero; the free
characteristic rank may be zero (the unit-group coordinates can still supply the
nonzero tuple, so points above the generic point are included); unit-group rank
zero is allowed; finite nonzero tame cokernel torsion is allowed, while torsion of
noninvertible order is excluded exactly as in the node; no residue characteristic
is restricted otherwise. All ring, scheme and monoid universes are explicitly u,
with ULift ℕ allowing the base chart in that same universe. No test-object universe
is quantified independently of the source. No statement correction or dispute.

## Second reading by Q101

The dispatched brief assigns the independent reading to the maintainer and
explicitly forbids starting other agents. This section records the worker's
self-check, not a claim that an independent reader was run. Comparing the node
and retained partial module found (1) its duplicate unpublished log-chart API,
(2) forbidden let binders for the logged trait and quotient ring, and (3) a missing
pair of parentheses that would subtract π within each factor. The final module
uses the landed canonical-comparison API, explicit target construction and real
quotient helpers, with the subtraction outside the product. Each hypothesis and
conclusion is matched above. No DAG statement was changed. Independent approval
remains with the maintainer's delivery review, as required by the dispatcher.
