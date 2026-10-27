## Worker report

The module `Sheaf.Paper.StrictDirectImageMixedUnit` states
`WeilConjectures.StrictDirectImageMixedUnit.strictDirectImageMixedUnit` with
`sorry`. All other declarations are constructions, normalized comparison
structures or predicates used to spell out this one node. No data definition
contains `sorry`; there is only one postponed theorem.

Hypotheses and objects, clause by clause:

- `l : ℕ` with `[Fact l.Prime]` is the prime. `k : Type u`, `[Field k]`,
  `_hl : IsUnit (l : k)` express exactly the field and invertibility conditions.
- `Ω : Type v`, its field, Q_l-algebra and `IsAlgClosure` instances give the
  specified algebraic closure, without equating its universe to the scheme universe.
  `e j : AlgebraicallyClosedCoefficients.Index l Ω`, `h : e ≤ j` give arbitrary
  finite subextensions. `Coefficient` and `coefficientInclusion` are their existing
  small models and embedding, not new coefficient objects.
- `X,Y : Scheme.{u}` with `Over (Spec k)`, locally finite type, quasi-compact and
  separated structure maps express separated finite-type k-schemes.
  `f`, `[f.IsOver (Spec k)]`, `[IsProper f]` express the proper k-morphism.
- `sfIntegralConstructibleCategory` is the recorded derived-complete bounded
  constructible category, with its uniform reduction-amplitude condition.
  `D.integral e`, `D.integral j` are its strict direct images. `D` and `HasIntegralLaws`
  are the precise normalized comparison data quantified in the referenced scalar
  comparison theorem; they are not arbitrary comparisons or extra geometric hypotheses.
- `Padic.coefficientExtensionRing l H (n+1)` and the existing integral/sequence
  ring sheaves give the chosen valuation rings, uniformizers, positive quotients,
  completed coefficients and small pro-etale sites. Every positive exponent occurs
  exactly once as `n+1`, including exponent one.
- `finiteReduction` transposes the actual reduction adjunction unit through the
  geometric restriction/direct-image comparison and normalized reconstruction.
  The two `StrictProjections` clauses of `CoherentLaws` require exactly that these
  are the adjuncts of actual Roos total-limit projections of `SfIntegralDirectImage`.
  The system reduction comparison is the explicit adjunction transpose `reductionMap`;
  its invertibility is a conclusion, the two `IsIso (reductionMap ...)` clauses.
- `integralScalarExtensionOfUniverses` and its constructible restriction give T.
  `(D.integralComparison e j h).symm` is b, literally the inverse of the prescribed
  normalized ambient counit/tensor comparison. `HasIntegralLaws` retains its
  reconstruction/completion conjugation; no arbitrary b is substituted.
- The finite ring map is `integralScalarQuotientMap`. Exact restriction is
  `(proEtaleCoefficientRestrictScalars ...).mapDerivedCategory`.
  Eta is exactly the recorded `sfMixedCompletedReductionUnit`. The definition
  `finiteRestriction` chooses the normalized intrinsic comparison from
  `proEtaleDerivedDirectImage_restrictScalars`, including its K-injective resolution
  formula and the displayed direction rho. Both finite rings are proved finite
  by `Padic.finite_coefficientExtensionRing`, with no flatness assertion.
- `FiniteLaws` states the displayed equation, in Lean's left-to-right composition:
  eta_Y followed by restriction of (reduced b followed by r_L) equals r_E followed
  by finite direct image of eta_X followed by rho. The universal-lift clause is the
  `Function.Bijective` map given by restriction followed by precomposition with eta.
  Surjectivity and injectivity express existence and uniqueness for every target;
  combined with the equation, the specified B-linear composite is the unique lift.
- `CoherentLaws ...` states these normalizations simultaneously on
  `coefficientSequenceDerived`, the actual derived category of modules on the ringed
  sequence site (not a functor category of separate derived objects).
  Its equation clause is an equality in that category before finite evaluation, and
  its final clause is the whole-system universal-unit bijection.
- The four calculus witnesses and their coherence witnesses retain actual reduction/limit unit/counit
  and their scalar-association coherence. `AX/AY` and `dX/dY` retain the canonical
  coefficient adjunctions, tensor association and flat-term K-flat representative
  normalizations of the coefficient-reduction model. The `MixedEvaluation`,
  `ReductionEvaluation` and `RestrictionEvaluation` clauses identify their evaluations
  with the *specified* finite eta, r and rho, including all transport arrows.
  `LimitComparison` is fixed by ordinary limit projections on sections and the
  universal derived units on whole complexes; `RestrictionComparison` is fixed
  by the identity on sections and the universal right-derived normalization.
  Thus no auxiliary comparison is specified merely by its finite evaluations.
- There is no hypothesis that finite evaluations detect morphisms, no quotient
  flatness assumption, no finite Tor-amplitude assumption on the reductions.

The hypotheses remain exactly those of the node. Auxiliary comparison witnesses
are outputs of `CoherentLaws`, rather than assumptions. The node statement and proof
are unchanged. Two already landed definition nodes are added to `stmt_deps` to
cite the actual ringed-system direct image and its derived operation, which the
whole-system equation uses. No new nodes or dependency repairs are needed.

Dependency declarations read and used:

- `def-weil-scheme-morphism-properties`: convention node; the theorem uses the
  standard Mathlib structure-map properties listed above.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`.
- `lem-sf-integral-direct-image-constructible`: `Sheaf.Paper.SfIntegralDirectImageConstructible`, `WeilConjectures.sfIntegralDirectImage_constructible`.
- `lem-weil-derived-scalar-extension-restriction-adjunction`: `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, `WeilConjectures.derivedScalarExtensionRestrictionAdjunction`.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`, `WeilConjectures.integralScalarExtensionOfUniverses`.
- `lem-sf-strict-direct-image-scalar-comparison`: `Sheaf.Paper.SfStrictDirectImageScalarComparison`, `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageScalarComparison`.
- `def-weil-mixed-reduction-unit`: `Sheaf.Paper.MixedReductionUnit`, `WeilConjectures.sfMixedCompletedReductionUnit`.
- `lem-pur-coefficient-extension-reduction-model`: `Sheaf.Paper.CoefficientExtensionReductionModel`, `WeilConjectures.coefficientExtensionReductionModel`.
- `lem-weil-proetale-direct-image-restriction-of-scalars`: `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`, `AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_kInjective`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `def-trf-integral-comparison-sequence-systems`: `Sheaf.Paper.IntegralComparisonSequenceSystems`, `WeilConjectures.integralComparisonDerivedSequencePullback`.
- `def-weil-system-operation-exchange-realization`: `Sheaf.Paper.SystemOperationExchangeRealization`, `WeilConjectures.FrobeniusExchange.integralExchange`.

For restriction/direct image we use
`AlgebraicGeometry.Scheme.proEtaleDerivedDirectImage_restrictScalars` in
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`. This declaration
is already explicitly listed in the dependency's `lean.declarations`; it is the
intrinsic constant-ring-sheaf presentation required by the coefficient calculus.
The fixed-ModuleCat presentation is equivalent but has different literal objects.
No record is changed or second restriction functor introduced.

All recorded proof dependencies with Lean modules are imported. The two mate
pasting nodes without recorded Lean modules are cited in the six-step proof
docstring, which follows the node's complete natural-language proof. The scalar
adjunction, actual total-limit counit, and geometric restriction comparison appear
explicitly in the definitions so later proof work can use their triangle identities.

Edge cases checked before writing: exponent one (`n=0` in Lean), identity coefficient
inclusion (`e=j`), zero complex, empty schemes, arbitrary cohomological degrees,
and ramified E-to-L inclusions. No cancellation uses flatness of the quotient map;
completed extension is compared to derived tensor by the existing normalized model.
No boundedness is imposed on the target of either Hom bijection. Independent
algebraic-closure universe v is retained; finite coefficient models are in u as in
the recorded constructible integral interface. Identity scalar change is governed
by `HasIntegralLaws` and the existing coefficient-system unit/association laws.

Searches for existing declarations:

- msearch LeanFinder: "Mixed reduction tensor unit normalization of scalar extension
  and strict integral derived direct image on coherent quotient systems": eight
  unrelated algebra-presentation/cotangent hits, no exact match.
- msearch Loogle: `Adjunction.homEquiv, SheafOfModules.restrictScalars`: rejected
  the first unqualified name; repeated with `"restrictScalars"`, twelve linear-map
  restriction facts, no strict-image mixed-unit theorem.
- msearch Mathlib grep: `mixed.*[Uu]nit|strictDirectImage.*[Uu]nit`: only unrelated
  number-field mixed-embedding unit actions.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for mixed-unit/strict-image names:
  found the recorded `MixedReductionUnit`, reused here, and compact-support scalar
  normalization, a different operation. No declaration of this node was found.
- rg of `dag/lean_names_upstream.json` and both source trees for the proposed
  namespace/theorem and literal node id: no existing statement/name collision.
  Literal `grep -rn` of the node id in `lean/WeilConjectures` also had no hits.

No statement dispute or correction. All writes are confined to this sandbox;
compilation and delivery use only the prescribed launcher wrappers.

The complex-level normalization uses `restrictionComparisonComplex`, with the
existing `FrobeniusExchange.systemDirect_additive` supplied explicitly for each
coefficient. This is a real construction of termwise application of the ordinary
comparison, avoiding an ambiguous instance search. The typeclass structure does
not add a mathematical assumption and introduces no postponed obligation.

`CoherentLaws` is an existential proposition with conjunctions, rather than a
large structure generating expensive eliminators. Each of its four coherence
records is retained as `Nonempty`; those records contain canonical comparison
data determined by their normalization, and are not definitions chosen from a
bare existence claim. This change in packaging preserves every witness and law.

Validation: prescribed `scompile.py` completed successfully for both its isolated
sandbox module and the final module path, with no errors or warnings (only the
expected postponed-theorem status). The final library-module compilation reported
42.9 seconds. There are no diagnostic traces or temporary `#check` commands.

For the two added landed nodes, the declarations used directly are
`WeilConjectures.integralComparisonSequenceDirectImage` and
`WeilConjectures.FrobeniusExchange.systemDirect`, `systemDirectEvaluation`,
`systemDirect_additive`. They are listed among those nodes' recorded declarations.
The final module imports the site and every statement dependency's defining
module publicly, and retains ordinary imports for the proof-only dependencies.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
