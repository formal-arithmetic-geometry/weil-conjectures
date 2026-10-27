## Worker report

The module `Sheaf.AlgebraicGeometry.MonoidalChartDenseInjective` states
`AlgebraicGeometry.FineSaturatedLogScheme.monoidalChart_dense_injective`, with proof
`sorry`. Two fully defined helpers, listed in `lean.declarations`, bundle this
criterion's chart assumptions and transport the existing log-unit inclusion along
the canonical strict-local-ring comparison. Neither introduces an independent
mathematical construction or chooses an unspecified map.

Hypothesis-by-hypothesis correspondence:

- `(X : FineSaturatedLogScheme.{u})` supplies the scheme, étale log structure, fs
  condition, and local Noetherianity (`X.locallyNoetherian`). It does not assume
  `X.IsLogRegular`.
- `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and
  `t : Spec (.of Ω) ⟶ X.scheme` describe each geometric point.
- `Scheme.strictHenselizationRing t` is exactly the recorded affine pointed-étale
  coordinate-ring colimit A. `hdom` requires `IsDomain` of this ring at every
  geometric point.
- `hcharts` supplies, at every geometric point, a monoid P, a pointed étale
  neighbourhood W with lift w, and a chart c. The helper
  `IsContractingSharpChart t W w c` requires `IsAffine W.left` and the existing
  `M.IsChart W c`. The étaleness of W's structure morphism is part of `X.Etale`.
- P is written additively, with `AddCancelCommMonoid P` encoding integrality
  (cancellativity), `Monoid.FG (Multiplicative P)` encoding finite generation,
  and `∀ p, IsUnit (Multiplicative.ofAdd p) → p = 0` encoding sharpness.
- The canonical map `p ↦ Associates.mk (germ (c (ofAdd p)))` is required to be
  bijective onto `M.characteristic t`. This is the stated identification with
  the characteristic quotient, not an arbitrary bijection.
- The helper quantifies over every `J : Set P` satisfying
  `∀ j ∈ J, ∀ p, j + p ∈ J`, without a nonemptiness condition. Its equality of
  sets is precisely `a ⁻¹' (Ideal.span (a '' J)) = J`.
- `a_W(p)` is `X.logStructure.alpha.app (op W) (c (Multiplicative.ofAdd p))`.
  Its germ `a(p)` is the existing `chartStrictHenselizationMap t W w c` applied
  to `Multiplicative.ofAdd p`. This map uses the actual chart germ and the
  canonical ring comparison, not a supplied or chosen ring map.

Conclusion-by-conclusion correspondence:

- `∃ U : X.scheme.Opens, (U : Set X.scheme) = M.trivialityLocus ∧ Dense ...`
  states that the zero-characteristic locus V is open and dense. An open U
  representing exactly V records openness without requiring it as a hypothesis.
- The next universal quantifier ranges over every pointed chart satisfying
  exactly the displayed chart assumptions. `∀ p, chartStrictHenselizationMap ...
  (ofAdd p) ≠ 0` states nonvanishing of every chart monomial.
- `r : ℕ`, `p : Fin r → P`, and `AddSubmonoid.closure (Set.range p) = ⊤`
  specify any finite generating list, including repetitions and r=0.
  `∏ i : Fin r, ...` is the exact product s (respectively s_W). The first
  generating-list conjunct states s≠0.
- `W.hom ⁻¹' U = W.left.basicOpen s_W` identifies the base change of V to W
  with D(s_W). The latter is the usual nonvanishing open of a global section.
- `Scheme.strictHenselizationStructuralMap t ⁻¹' U =
  (PrimeSpectrum.basicOpen s).carrier` gives its inverse image in Spec A as
  D(s), the primes not containing s. This is the canonical inverse image:
  the structural morphism factors through the pointed affine neighbourhood W,
  so it is also the pullback of the preceding D(s_W).
- `Function.Bijective ((germ.hom.comp c).coprod
  (M.strictHenselizationUnitsIn t))` says the canonical monoid homomorphism
  `Multiplicative P × Aˣ → M_stalk` is an isomorphism. `coprod` multiplies the
  chart germ by the canonical image of the unit. In commutative monoids this
  product is the finite direct sum P⊕Aˣ of the node.
- `Function.Injective (fun z : Multiplicative P × Aˣ ↦
  (z.2 : A) * chartStrictHenselizationMap ... z.1)` states injectivity of the
  structural map (p,u)↦u*a(p) in these canonical coordinates.
- The last `∀ W m, IsUnit ((pullback.fst W.hom U.ι).appTop (alpha.app ... m))`
  says that every log section on every étale test object restricts to a unit
  over V. It uses the actual scheme pullback and restriction of the structural
  image, not just a pointwise-unit assertion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`, `characteristic`,
  `trivialityLocus`, `unitsIn`, and `EtalePrelogStructure.germ`/`stalk`/`stalkAlpha`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, present in the
  fs log scheme's recorded data.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-point
  convention uses the morphism `t : Spec (.of Ω) ⟶ X.scheme`. Also read
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`, used
  in the recorded definition of the triviality locus.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing` and `Scheme.strictHenselizationScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, implicit in `X.Etale`.
- Definition dependency `def-trf-chart-strict-henselization-map` (landed Q85,
  existing:true) records the declarations in
  `Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`:
  `strictLocalRingIsoStrictHenselization` and
  `EtaleLogStructure.chartStrictHenselizationMap`. These helpers have no
  log-regularity assumptions. The module's theorem `monoidalIdeal_contraction`
  does require log regularity and is not invoked or assumed here.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, whose actual construction and
  universal leg characterization were read.
- Proof dependency `lem-weil-pbc-flat-lfp-open` is the Mathlib instance
  `UniversallyOpen.of_flat`, imported privately from
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.

The construction-owning DAG nodes `def-trf-chart-strict-henselization-map` and
`def-weil-pbc-strict-henselization-structural-map` were added to `stmt_deps`, as
already landed definitions explicitly used in the signature/helper definitions.
No existing dependency interface was changed. No statement was corrected.

Edge cases checked before writing: empty X (all chart hypotheses and section
restrictions remain valid and the empty locus is dense in the empty space);
trivial P (r=0 is permitted and both products are 1, so D(1) is the full chart);
a nonminimal/repeated generating list; J=∅ (contraction forces no chart monomial
to vanish); J=P (the generated ideal contains a(0)=1); and the zero ring (correctly
excluded by `IsDomain A` at an existing geometric point). There is no rank,
positive dimension, connectedness, saturation of the chosen sharp chart, or
log-regularity hypothesis added. All variables and universes are explicit.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "Sharp integral logarithmic charts with contraction
  of monoid ideals over domain geometric stalks have injective structure map and
  open dense triviality locus" returned eight ordinary scheme/germ-injectivity
  results, including `instIsGermInjectiveOfIsIntegral`, `Scheme.IsGermInjective`,
  and `germ_injective_of_isIntegral`. Their signatures concern scheme structure
  sheaf germs, not log structural maps, and do not state this criterion.
- `msearch.py ... loogle '"LogStructure"'`: 0 hits.
- `msearch.py ... grep 'LogStructure|MonoidalIdeal|trivialityLocus'`: 0 Mathlib hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and monoidal dense/injective names found no existing statement.
  Searches for `trivialityLocus`, `IsChart`, and monoidal contraction located the
  existing log framework and the canonical chart-ring-map helpers reused here.
- Read ILO VI 1.1--1.4 (printed p.69) and VIII 3.4.1--3.4.3 (printed p.110) from
  the local PDF. The node deliberately extracts a criterion using explicit
  domain/contraction hypotheses; it is not a restatement of the source's full
  log-regular theorem. The current blueprint unit is unchanged.

Validation: `scompile.py Q06 lem-trf-monoidal-chart-dense-injective` checked both
sandbox and intended module imports cleanly, with no errors or warnings. The
single theorem is the only postponed proof. Every helper has real data and a
source/blueprint docstring. The theorem docstring reproduces all six proof steps.

## Second reading by Q06

A separate pass through the node and completed module rechecked the quantified
charts, the characteristic identification, all monoid ideals including empty,
the two generator products, both inverse-image formulas, density, the canonical
product-to-stalk bijection, structural injection, and section restrictions.
All match the node. The explicit `.carrier` on `PrimeSpectrum.basicOpen` repairs
only Lean's coercion to the underlying set of Spec A. The finite list is indexed
by `Fin r`, not a set, so repeated generators and the empty list are retained.
The inverse-image formula uses the canonical structural morphism, and the unit
map uses the inverse of the canonical ring comparison. No arbitrary comparison
map or additional mathematical assumption was introduced. This is a second pass
by the dispatched worker; no additional agent was started, as the prompt forbids
it. The maintainer's independent review is the delivery's independent reading.

## Repair of return at 47219ed7a55c

H2 repaired: replaced the theorem dependency
`lem-trf-log-regular-monoidal-ideal-contraction` in `stmt_deps` with the already
landed definition owner `def-trf-chart-strict-henselization-map` (Q85). Read that
node's full statement, Lean record, and both recorded definition bodies in
`Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`. They supply exactly
the canonical comparison and chart structural map used here, with no
log-regularity hypothesis. The containing module's import stays because it is
the definition node's recorded module. Updated the dependency list above and the
module provenance docstring to identify that definition owner.

Compared the retained delivery with the current read-only main node: all original
node fields are identical except for the authorized statement-dependency additions
and Lean record. The theorem signature and all helper bodies remain exactly those
reviewed as mathematically correct at the returned head. The delivery wrapper
refreshes the base and builds the repaired commit on current main. No independent
node, mathematical hypothesis, conclusion, or proof was changed.
