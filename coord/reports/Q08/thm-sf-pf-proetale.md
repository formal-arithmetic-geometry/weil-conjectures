## Worker report

Bind thm-sf-pf-proetale to the existing declaration
`WeilConjectures.sf_proetale_projection_formula` in
`Sheaf.Paper.SfProEtaleProjectionFormula` (source line 238 onward).
No new Lean module or declaration is delivered. The same theorem already carries
sk-thm-sf-pf-proetale, explicitly listed in this item's blueprint.same_as; that
binding was independently reviewed on 2026-10-17. Its proof remains sorry.
I read the entire existing module, including Origin, integralDomains, integralMap,
and all four conjuncts, rather than inferring a match from its name.

Hypothesis and conclusion correspondence:

- The global tuple p,a,q,k0,k is `D : FiniteFieldDatum.{u}`. Its prime,
  exponent_pos, cardinality_eq, card_base and isAlgClosure fields give exactly
  the opening finite-field hypotheses.
- `l`, `[Fact l.Prime]`, `hl : l ≠ D.p` are the distinct coefficient prime.
  Each finite/integral/rational conjunct quantifies `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`.
  The prescribed valuation ring, uniformizer and quotient are the constructions
  behind `Padic.coefficientExtensionRing`; exponent `n+1` ranges over exactly
  the positive levels of the node. No level zero is added.
- `X,Y : Scheme.{u}` with the two `Over (Spec (.of D.k))` instances are the
  k-schemes. Each structure morphism has LocallyOfFiniteType and QuasiCompact.
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` give
  precisely the separated finite-type k-morphism. No structural separatedness
  of X or Y is required. `c : Compactification f` is arbitrary, not just Nagata's
  selected compactification.
- The mention of the six-functor datum specifies its concrete realization and
  canonical arrows; it is not a request to assume its projection axiom A3 as
  the proof. The existing concrete theorem has no abstract operation choices or
  A3 assumption. It uses the prescribed categories and actual constructions
  underlying that datum. There is no need to introduce or assume another datum.
- The finite conjunct uses `K,L : proEtaleDerivedCategory ...` and
  `finiteTorConstructible ... K/L`. This predicate is the intrinsic bounded
  constructible predicate intersected with HasFiniteProEtaleTorAmplitude.
  The retained `SfProEtaleProjection.Origin` packages an actual
  `Scheme.FixedEtaleOriginWitness`, its bounded constructibility, and the
  canonical intrinsic module realization isomorphism. This is the node's
  explicit-witness presentation, not an arbitrary comparison functor.
- The intrinsic finite presentation gives the very same assertion: the equality
  of intrinsic and etale-origin bounded-constructible predicates in
  `ProEtale.constructible_proEtale_origin` supplies Origin for every intrinsic
  input, via the recorded exact fixed/intrinsic equivalence. Tor bounds descend
  by `ProEtale.comparison_torAmplitudeIn_iff`, tested against every module sheaf.
  Origin arguments therefore do not exclude any of the intrinsic inputs in the
  item. They retain choices only to compare actual maps, as the item requests.
- The finite arrow is exactly `finiteRingCompactSupportProjection ... c`, the
  intrinsic transport of the proper counit/open tensor composite. The existing
  theorem asserts bounded-below endpoints and IsIso in the full D+ category;
  that is equivalently IsIso of this arrow in the ordinary derived category.
  The endpoint bounds are typing information and do not restrict the inputs.
- The integral conjunct uses `sfIntegralConstructibleCategory` and
  `finiteTorConstructibleIntegral`: actual completed coefficients, derived
  completeness, constructible positive reductions with one common cohomology
  interval, and one uniform Tor interval. Its Origin families are the finite
  reduction witnesses, supplied intrinsically by the same origin theorem.
  There is no discrete constant-integral comparison assumption.
- `SfProEtaleProjection.integralMap` is the canonical completed projection:
  inverse source completion unit, followed by the ordinary proper/open
  projection and compact support of the inner tensor completion unit. Its
  source is completed tensor of Rf!K with L, and its target is Rf! of completed
  tensor with pullback. The tensor models carry signed K-flat normalizations;
  they are presentations of the prescribed tensor, not arbitrary bifunctors.
  integralDomains supplies the actual membership and source-unit proofs, not
  a choice of a projection arrow. The map has the required completion-unit
  normalization, so its IsIso conclusion is for the indicated completed map.
- The rational conjunct is IsIso of `sfRationalConstructibleLocalization.map`
  applied to that integralMap. Every raw rational object is an integral
  object with localized Hom, so quantifying its integral representatives covers
  every pair. It imposes no separate finite-Tor or lattice hypothesis on field
  objects. There is no Karoubi completion.
- The last conjunct takes the image under the actual
  `GeneralAlgebraicallyClosedCoefficients.inclusion F` of the localized map
  at every finite field F in every chosen closure Ω. Any two input pairs
  acquire representatives over their compositum, so this states invertibility
  in the exact common-stage category in the node, including pairs initially
  represented over different coefficient fields. The common-stage transition
  construction supplies the identifications; no discrete Qbar module category
  or arbitrary comparison is substituted.
- Naturality and compactification/coefficient comparisons belong to these
  recorded canonical constructions. The conclusion asserts invertibility of
  these maps for every c; the node requests no additional compatibility
  theorem beyond using those supplied comparisons to form the maps.

Dependency declarations read and used to identify these notions:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum and CoefficientDatum.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and its imported coefficient constructions.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType and QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and IsSeparated.
- Sheaf.Paper.SixFunctorDatum: SixFunctorDatum, whose operation part fixes the
  concrete realization and whose A3 is not assumed by the reused theorem.
- Sheaf.Paper.ExchangeProjectionSuppliedDomains:
  SuppliedExchangeProjection.ExchangeProjectionStage and its projection composite.
- Sheaf.Paper.SixFunctorDualNotation: the documentation identifying the existing
  finite projectionMapOfCompactification and higher projectionComponent notation.
- Sheaf.Paper.FiniteTorAmplitudeSites: finiteTorConstructibleEtale, with the
  imported original finite, integral and field definitions in FiniteTorAmplitude.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules: FiniteCoefficientModules and
  derived categories and their canonical scalar realization.
- Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness.
- Sheaf.Paper.ProEtaleConstructibleOrigin:
  ProEtale.constructible_proEtale_origin and ConstructibleOriginComparison.
- Sheaf.AlgebraicGeometry.ComparisonTorInterval:
  ProEtale.comparison_torAmplitudeIn_iff.
- Sheaf.Paper.SfIntegralConstructible: sfIntegralConstructible/category.
- Sheaf.Paper.SfRationalizationKaroubi: sfRationalConstructibleCategory and localization.
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients:
  generalAlgebraicallyClosedConstructibleCategory and common-stage inclusions.

Edge cases checked: positive finite level 1 is n=0 in the existing indexing;
zero complexes and empty schemes are allowed; X and Y need not be separated;
f may be an identity or open immersion; c is any compactification; Tor intervals
are not fixed in advance; integral bounds are uniform in all positive levels;
field inputs need not carry supplied lattices or lie initially at one field;
no small closure universe is imposed (Ω has independent universe v).

Searches:

- msearch.py leansearch, "Compact support projection formula on the pro etale site":
  eight unrelated hits (support of kernel, profinite constructions, sheaf condition).
- msearch.py leanfinder, "compact support projection formula for pro-etale bounded
  constructible finite Tor complexes": eight unrelated condensed/limit hits.
- msearch.py loogle, "projectionMapOfCompactification, IsIso": no hit,
  unknown identifier projectionMapOfCompactification in Mathlib's index.
- msearch.py grep, "pro.?etale.*projection|projection.*pro.?etale": no Mathlib hit.
- rg in WeilConjectures for projection and this node ID found
  ProEtale.FiniteCoefficient.Derived.ProjectionFormula and ProjectionExtendScalars.
  Read them: finite clauses apply, but their integral/field clauses are discrete
  etale-origin statements and do not alone give the current completed statement.
- rg in Sheaf/Paper for projection and four stages found
  SfProEtaleProjectionFormula.lean. Full reading and the matching unit's lean
  record confirmed its reviewed concrete four-stage theorem. This supersedes
  writing a fresh restatement with SixFunctorDatum's A3 among its assumptions.

No new nodes, dependency repair, statement correction, or disputed statement.
The stage-1 repair note for this item is resolved and required keeping its
statement and repaired nine-step proof unchanged. This delivery changes only lean.

## Second reading by Q08

A separate in-session second pass compared the complete item, its source, the
existing SfProEtaleProjectionFormula module and the unit's reviewed binding.
No additional agent was started, as the dispatcher explicitly prohibits that.
The maintainer performs the independent review of this delivery.

I checked each geometry binder against the first paragraph, finite n+1 against
n>=1, the exact canonical finite arrow, both Origin arguments and their intrinsic
supply, integral completeness and the two uniform intervals, and localization and
common-stage inclusion against the final clauses. The important mismatch in the
first search candidate was its discrete integral etale-origin model: it was
rejected as a full match. The existing Sheaf theorem uses the completed coefficient
sheaf and completion-unit projection, and its two field clauses use the required
raw categories. The D+ finite result is equivalent to the ambient result because
it is a full subcategory. The retained witnesses do not impose an existence
restriction, by the statement dependency's intrinsic-origin equivalence. No new
module is delivered and no theorem is claimed proved by this task.

Validation: deliver2.py --no-push returned OK, commit 0b16933d3d: server
existing-declaration probes compiled and maintainer preflight passed. The current
server source was also read with scompile.py --source. A JSON comparison confirms
that lean is the only changed node field and its signature is verbatim source.
