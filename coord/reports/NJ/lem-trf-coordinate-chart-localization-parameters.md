## Worker report

The module `Sheaf.RingTheory.CoordinateChartLocalizationParameters` states
`AlgebraicGeometry.AffineBlowup.CoordinateChart.localization_and_parameters`.
Its only theorem has proof `sorry`. All auxiliary declarations have real data:
`Chart` specializes the existing `chartRing`, `ratio` is its actual generating fraction,
`coordinate` assembles the exceptional coefficient and the distinctly labelled nonpivot
ratios, `basePrime` is contraction, the three local-ring abbreviations use the recorded
localization/chart constructions, and `baseToLocal` is `Localization.localRingHom`.
No new independent mathematical notion or copied parameter predicate is introduced.

Hypothesis and clause correspondence (names below are in the `CoordinateChart` namespace):

- The commutative Noetherian ring with regular localizations is `{A : Type u}`,
  `[CommRing A] [IsRegularRing A]`. The latter is precisely Mathlib's Noetherian
  regular-ring class; it has both `IsNoetherianRing A` and regularity at every prime.
  This uses the ring clause of `def-weil-regular-scheme`, whose `mathlib_match`
  explicitly records `IsRegularRing` and `IsRegularLocalRing`, rather than its separate
  scheme clause `IsRegularScheme`.
- `m : ℕ`, `hm : 1 ≤ m`, `t : Fin m → A`, `i : Fin m` give the positive finite
  family and chosen chart. The pointwise hypothesis `ht` quantifies over every
  `p : PrimeSpectrum A` and supplies one parameter list `s` and an injection from
  `{j : Fin m // t j ∈ p.asIdeal}` to `Fin s.length`, with equality at each position.
  Thus repeated labels are not collapsed into a set of equal elements.
- `Chart t i` is exactly `chartRing (Ideal.span (Set.range t)) (t i)`, the subalgebra
  of `Localization.Away (t i)` from the recorded upstream definition. `ratio t i j`
  has ambient value `chartFraction (t i) 1 (t j)` for every j, including i.
- The first four conclusions are `IsNoetherianRing (Chart t i)`, the equality of
  the extended ideal with `Ideal.span {algebraMap A (Chart t i) (t i)}`, the named
  equation `ratio t i i = 1`, and `∀ j, t_j = a * ratio t i j` with the displayed
  coefficient maps. These are precisely Noetherianity, IC=(a), z_i=1, and t_j=az_j.
- Every subsequent clause is quantified over `y : PrimeSpectrum (Chart t i)`.
  `basePrime t i y` is y contracted along A to C; `BaseLocal t i y` is R=A_p;
  `ChartLocal t i y` is S=C_y. No local structure on A or C is assumed.
- `LocalBaseChart t i y` is `chartRing (I.map (algebraMap A R)) (t_i in R)`,
  so it is literally R[IR/t_i] inside R[1/t_i], not an unrelated presented ring.
  The existential algebra equivalence `e : (C ⊗[A] R) ≃ₐ[A] LocalBaseChart t i y`
  is normalized for every c and r: its ambient value is r times the image of c
  under `Localization.awayMap`. This determines the canonical map uniquely,
  and in particular sends every named ratio to the same fraction. Tensor factors
  are in the order of the node, C then R.
- The prime `P` of this local-base chart is specified by
  `∀ c, e (c ⊗ₜ[A] 1) ∈ P.asIdeal ↔ c ∈ y.asIdeal`.
  It is the prime induced by y under localization, not an arbitrary prime.
  `eS : Localization.AtPrime P.asIdeal ≃+* ChartLocal t i y` is normalized on
  every c from C. This fixes the canonical identification of S with this local
  chart ring. Since the chart over R is C localized at A minus p, its prime and
  this equivalence are determined by these conditions. These conditions also cover
  inverses of the inverted base elements and the subsequent prime denominators.
- Under `¬ I ≤ (basePrime t i y).asIdeal`, the unit `a : (ChartLocal t i y)ˣ`
  has value exactly the image of t_i. `Function.Bijective (baseToLocal t i y)`
  says the actual canonical R-to-S ring homomorphism is an isomorphism. The final
  equation in that branch sends every ratio to `baseToLocal (t_j in R) * ↑(a⁻¹)`;
  this is division by the specified unit, with no arbitrary field/division structure.
- Under `I ≤ (basePrime t i y).asIdeal`, a parameter list of R and an injection
  from all of `Fin m` express extension of the entire family at distinct positions.
  The equivalence `eQ` identifies the actual polynomial chart
  `traceChartRing (fun j ↦ algebraMap A R (t j)) Finset.univ i` with R[IR/t_i].
  Its coefficients are fixed, and each polynomial variable is sent to t_j/t_i
  in the ambient localization. Combined with `P` and `eS`, this says exactly that
  S is the local ring of the standard coordinate blowup chart. The family passed
  to this polynomial presentation need not already be a full parameter list;
  the preceding list-extension witness provides the full system needed by the proof.
- In both cases `∃ hS : IsRegularLocalRing S` supplies regularity, including the
  Noetherian structure needed to type a parameter system. The explicit projection
  `hS.toIsNoetherian` is used only to provide that instance, not as an additional
  hypothesis. A single list `s` is a regular system of parameters and the subtype
  of labels `Option {j : Fin m // j ≠ i}` whose coordinates belong to y injects into
  `Fin s.length`, with the corresponding elements of S at those positions.
  `none` denotes a, `some j` denotes z_j; the pivot ratio z_i is excluded exactly
  as in the node. The final universal unit clause applies to every remaining label.

Dependencies read and used:

- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`, `IsRegularLocalRing`,
  the ring clauses of `def-weil-regular-scheme`; these are publicly reexported by
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded declaration
  of `def-weil-pbc-noetherian-ring`, reexported by the same parameter-system import.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, exactly the recorded list-length and
  maximal-ideal-generator definition, including the empty list.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`:
  `AlgebraicGeometry.AffineBlowup.chartRing` and `chartFraction`, the recorded
  `def-nagata-blowup-chart-ring` and its actual generating fractions.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, and `PrimeSpectrum.comap`; the recorded prime
  localization and its canonical functorial map. Read also the recorded residue-field
  and fiber declarations; neither additional clause is needed in this item.
- `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`,
  `Localization.awayMap`, implementing the recorded away-localization notion.
- `Mathlib.RingTheory.TensorProduct.Basic` and its public imports: `TensorProduct`,
  the recorded tensor product, with its standard commutative-algebra structure.
- `Mathlib.RingTheory.Localization.Submodule`: the existing Noetherian localization
  instance needed for the parameter systems of R.
- Added already-landed statement dependency `def-trf-parameter-blowup-chart-ring`:
  module `Sheaf.RingTheory.ChartCoordinateNonzerodivisors`, `traceChartRing` and
  `traceChartCoordinate`. This is the existing polynomial quotient, not a new copy.
- Proof-only import `Sheaf.RingTheory.ParameterBlowupCoordinateQuotients`:
  `ParameterBlowupCoordinateQuotients.coordinate_quotients_and_parameters`, as in
  proof step 7; proof-only `Mathlib.RingTheory.FiniteType` provides
  `Algebra.FiniteType.isNoetherianRing`, as in step 1. The proof dependency
  `lem-trf-parameter-blowup-algebra-regular` has no recorded module in the read
  DAG, so no guessed module was imported. Its conclusion is not used to construct
  data or to type this statement; it is cited in the theorem's proof docstring.

Source and edge cases:

Read the actual ILO PDF, VIII 4.1.8 and Lemma 4.2.9 (printed pp.118 and 121), with
its local coordinate formulas, and the latest blueprint ancestor proof. The global
statement remains unchanged; no `STATEMENT-DISPUTED` or statement correction.
For m=1 there are no nonpivot variables and the label family is just the exceptional
coordinate. For a zero-dimensional base local ring, `ht` forces every t_j there to
be a unit and uses the allowed empty parameter list. Empty vanishing subfamilies
have an empty-domain injection. The center may be the unit ideal, and a chart can
be the zero ring (for example from a component on which the pivot vanishes); its
prime spectrum is then empty, and all pointwise conclusions are vacuous. The zero
base ring is allowed. No nonzerodivisor assumption on the global pivot, no domain
hypothesis, no base/chart locality, no rationality of y, no field or characteristic
restriction, and no uniform dimension bound have been introduced. Distinct labels
with identical nonunit values are disallowed by `ht`, not silently identified;
identical unit values are permitted.

Searches performed before writing:

- `msearch.py ... leanfinder`: "Localization of a global regular coordinate blowup
  chart and regular systems of parameters at every prime" returned eight smoothness
  and localization results, including `Algebra.IsStandardSmooth.localization_away`
  and `RingHom.isStandardSmooth_localizationPreserves`; none states this theorem.
- `msearch.py ... loogle`: "AlgebraicGeometry.AffineBlowup.chartRing,
  Localization.AtPrime" returned zero hits, with unknown identifier for the project
  chart name in Mathlib. The project definition was inspected directly instead.
- `msearch.py ... grep`: "chartRing|blowup" under Mathlib/RingTheory returned the
  future-blowup comment in ReesAlgebra only.
- `msearch.py ... leansearch`: "Blowup coordinate chart localization at primes
  regular systems of parameters" returned eight general localization results,
  including `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`.
  None contains the parameter-coordinate or regularity conclusions.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for `traceChart`,
  `coordinate_chart`, `localization_parameters`, `chart.*localization`,
  `localization.*chart`, and the item id found the existing affine chart algebra,
  strict-transform chart constructions, coordinate quotient theorem, and unrelated
  completion/standard-basis results. Read their relevant declarations. None is an
  existing statement of the entire node. The literal item-id search upstream had
  no hit. `dag/lean_names_upstream.json` was consulted for the chart and candidate
  names. The new fully qualified namespace does not occur upstream.
- `tools/blueprint_refs.py search 'parameter blowup chart'` found no blueprint
  node by that phrase. Direct DAG inspection found the already-landed
  `def-trf-parameter-blowup-chart-ring`, which is reused rather than recreated.

Validation: `scompile.py NJ lem-trf-coordinate-chart-localization-parameters`
compiled the delivered file both as sandbox and as its actual library module,
cleanly (5.9 s and 4.8 s). Earlier compile probes caught and repaired an incorrect
import path and the class-projection name; no errors or non-sorry warnings remain.

## Second reading by NJ

The same worker reopened the node and the final file for a separate clause-by-clause
pass; no second agent was started, as required by the dispatcher brief. Independent
review is performed by the maintainer after delivery. This pass checked especially:
`ht` preserves labels and allows empty vanishing subsets; the two sides of `e` are
exactly C tensor R and the existing subalgebra R[IR/a]; the pure-tensor equation
fixes the canonical map rather than merely asking for an isomorphism; P contracts
to y, and eS fixes all c; the outside-center branch uses the actual localRingHom;
the center branch fixes every coefficient and ratio of the polynomial chart; and
one injection into one parameter list simultaneously treats the exceptional
coordinate and all nonpivot ratios. The Noetherian argument required to type the
last parameter-system predicate is obtained from the asserted regularity hS,
without moving any conclusion into the hypotheses. No mathematical mismatch was
found and no source statement was changed. The auxiliary declarations abbreviate
existing constructions and never choose data from a postponed existence theorem.
