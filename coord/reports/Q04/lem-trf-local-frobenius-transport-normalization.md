## Worker report

Item: `lem-trf-local-frobenius-transport-normalization`.
Module: `Sheaf.Paper.LocalFrobeniusTransportNormalization`.
Main declaration: `WeilConjectures.localFrobeniusTransportNormalization`.
The item is stated with `sorry`; no mathematical proof is supplied. All definition
bodies are genuine constructions. The auxiliary postponed theorems and definitions
belong to this normalization node and are recorded in `lean.declarations`.

The source read is blueprint main-20261015,
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final sentence. The node supplies the extracted local normalization statement and
the ten-step proof plan, reproduced in the main theorem's docstring. Its source
sentence concerns transporting Frobenius endomorphisms by the common-stage
comparison. No statement correction or disputed mathematical statement is proposed.

### Hypotheses and objects

* `D : FiniteFieldDatum.{u}` retains the prime p, a, q, k0 and the specified algebraic
  closure k. `X₀ : Over (Spec (.of D.k₀))` is the given model, not an arbitrary k-scheme.
  `LocallyOfFiniteType X₀.hom` and `QuasiCompact X₀.hom` express finite type;
  `IsSeparated X₀.hom` is the stated separation assumption.
* `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` express precisely the coefficient
  prime restriction. Residue-characteristic invertibility is constructed from these
  data using `frobeniusPointPrimeInvertible` and
  `D.schemeFrobeniusCoefficientInvertible`; it is not an extra theorem hypothesis.
* `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]` is a finite coefficient field. As in the recorded
  dependencies, one uses a small model of a finite subextension of the fixed
  algebraic closure; neither the constructions nor the equations depend on its
  embedding. The scalar equation quantifies over every finite coefficient model M
  and every `ι : E →ₐ[ℚ_[l]] M`, covering inclusions of subextensions in that closure.
* `r : ℕ` represents m = r+1. Thus m = 1 is included, m = 0 is excluded, and every
  positive m is represented. `y : D.extensionPoints X₀ (r+1) (Nat.succ_pos r)`
  is the F_(q^m)-point, and `localExtensionPoint D X₀ ... y` is its induced geometric
  point. The actual finite subfield and geometric fibre come from D.
* `D.geometricFiber X₀`, `frobeniusPointIso D`, and `D.geometricFrobenius X₀`
  give X, s, g_s and g_X. The endomorphism powers in the finite presentation use
  `End.of (D.geometricGaloisFrobenius X₀)`. The latter is the recorded underlying
  scheme map of geometric Frobenius, not a purported k-linear morphism.
* `C : IntegralComparisonSystem.{u} l` records the node's stipulated choice of
  simultaneously normalized strict-system realization data for all fields.
  Its `coefficient` and `scalar` fields contain the representative-normalized
  pullback and scalar models. This is not an arbitrary compositor or an assumed
  normalization equation. `integralComposition` uses
  `integralComparisonComposition l E C`, and `rationalScalar` is uniquely specified
  as the localization of `integralComparisonScalar ... C`. In particular the
  unrelated choices in the older existential composition theorem are not used.
* Finite exponent n is represented by n+1. Finite source objects are the actual
  `intrinsicFiniteTorsionConstructible` full subcategory; integral objects are
  `sfIntegralConstructibleCategory`; rational objects and ALL their morphisms are
  in `sfRationalConstructibleCategory`, the framework raw rationalization.
  No Karoubi envelope or field-vector-space replacement is used for source objects.

### Clause-by-clause rendering

All local helper names below are in `WeilConjectures.LocalFrobeniusTransport`.
`Normalization` is an explicit Prop-valued conjunction, with no missing assumptions
hidden in an abstract predicate.

1. The scheme equality g_X^m ybar = ybar g_s^m is `returnEquation`.
   `positiveReturnEquation` is the same equality in the positive-power presentation.
   `fixedEquation` states Phi^m ybar = ybar. These named theorems have source and
   complete natural-language proof docstrings; the definitions refer to their
   proofs only for equality transport.
2. Finite `J_y` is `finiteFibre`: actual constant-coefficient pullback followed by
   exact point sections. It uses the same module and derived-category instances
   as `pointFiniteFibre`; restriction to the bounded finite source is its ambient
   realization. `finitePointIterate` recursively composes the actual one-step
   `frobeniusPointTransportFinite` maps of the recorded point-transport definition.
   Every step uses `pointPowerPullbackModel` to change to constant-ring pullback;
   `proEtaleConstantRingPullbackComposition` joins the nested pullbacks.
   `finiteTransport` uses the iterate with predecessor index m-1, the equality
   (m-1)+1=m, and `finiteReturn`, the canonical return-square compositor.
   Thus the map is defined by m successive transports, without invoking the
   separate point-transport-composition theorem. `finiteRho` is exactly the
   fixed-point equality transport followed by the inverse pullback compositor.
3. `finiteKappa` is the dependency's `D.canonicalSchemeGaloisComparison`, with its
   canonical absolute-Frobenius normalization and the canonical coefficient
   annihilator. No scalar parameter is admitted. `finiteNormalized` is rho followed
   by `finiteFibre.map` of kappa. The first two conjuncts of `Normalization` give
   finite naturality for every morphism and the finite normalization equation.
4. `strictTower f` is the simultaneous quotient-complex tower for f, followed
   degreewise by point sections. `finiteOrdinary` extracts the actual ordinary
   section map from the fully faithful degree-zero embedding; this is unique,
   rather than an arbitrary chain representative of a derived map.
   `StrictFormula` fixes every degree and section of both recipes, transported
   through the existing `integralFinitePullbackModel` identifications.
   `strictRecipe_existsUnique` specifies an actual natural morphism of the WHOLE
   tower, including quotient transitions and differentials. `strictMap false`
   is the point-transport recipe and `strictMap true` is rho/kappa. The third
   conjunct asserts equality of their whole tower maps on every good simultaneous
   integral representative.
   This is stronger information than equality of separate derived reductions and
   is precisely the strict-system equality required by the node.
5. `integralPointIterate` recursively applies
   `frobeniusPointTransportIntegralConstructible` on successive pullbacks.
   `integralReturn` is the return-square compositor using C; `integralTransport`
   composes them to land in J_y of the direct-composite g^m pullback.
   `positivePower_eq` identifies the positive recursive scheme power with the
   ordinary endomorphism power. Canonical composition identifications express
   this as the node's J_y G^m. The fourth conjunct is integral naturality for every
   morphism of constructible integral objects.
6. `sectionsRoos` is uniquely characterized by BOTH unshifted and shifted cone
   projection equations, with the actual transition endomorphism 1-s. It compares
   exact point evaluation of the completed pullback's Roos cone with the Roos cone
   of the evaluated tower. `integralModel` includes the prescribed K-flat
   representative comparison, the exact-sections localization comparison, and
   that cone comparison. For ANY good representative P and ANY `e : Q(P) ≅ K`,
   `integralNormalized` applies `integralOperationsRoosMap` to the actual strict
   rho/kappa map, localizes it, and conjugates by `integralModel`.
   The fifth conjunct equates this with `integralDirect`, the same successive
   integral transport before its final c(y,g). Thus integral normalization
   explicitly realizes the whole strict map. Good representatives are the
   existing flat-term K-flat model, not a perfectness or finite-Tor-amplitude
   condition on K or on any reduction; every integral constructible K has them.
7. `rationalPointIterate`, `rationalComposition`, `rationalReturn` and
   `rationalTransport` rationalize the very same specified integral compositions,
   retaining the recorded point transport. The sixth conjunct is rational
   naturality, quantified over every framework rationalized morphism, not just
   localized integral arrows or pure tensors.
   `rationalFibreModel` is the recorded rational pullback object identification,
   rational point object comparison and canonical size descent. `pointFractionDerived`
   is fraction-field tensor with exactly the source/target point-derived instances.
   `rationalNormalized` rationalizes the WHOLE integral map above and applies the
   fixed size descent. The seventh conjunct is rational normalization for every
   object and every good integral representative of its underlying integral object.
8. `rationalScalar` is the natural isomorphism uniquely characterized on every
   unchanged rationalization object by the localization of the specified integral
   scalar comparison. Its data is selected from an exists-UNIQUE statement, whose
   proof docstring explains existence and uniqueness on all rational morphisms.
   `rationalFibreScalar` is the inverse recorded point-sections scalar comparison,
   followed by point-fibre application to that pullback comparison. It is b in
   composition order. The final conjunct of `Normalization` is exactly
   `(t_E tensor M) ≫ b_(G_E^m K) ≫ J_M(d_K) = b_K ≫ t_M(T K)`.
   Here d is `rationalScalar` for the direct g^m map; its identification with the
   iterated comparison uses the SAME specified compositors as `rationalComposition`.
   Identities and towers use `AlgHom.id` and composition of the quantified ι's,
   with the existing completion-normalized tensor unit/associator from the recorded
   scalar and point comparisons. No newly chosen unit, tower associator or scalar
   comparison is introduced, so the comparisons retain the node's stipulated
   identity/tower identifications.

### Dependency declarations used

All names are in `WeilConjectures` unless explicitly qualified. Each recorded
statement-dependency module is directly publicly imported.

| Module | Declarations used |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `FiniteFieldDatum`, `FiniteFieldDatum.geometricFiber`, `FiniteFieldDatum.extensionPoints` |
| `Sheaf.AlgebraicGeometry.FrobeniusDetailed` | `FiniteFieldDatum.geometricFrobenius`, its underlying Galois map |
| `Sheaf.Paper.DerivedPullbackTensorHom` | `constructibleIntegralPullback`, `rationalDerivedPullback`, its object formula |
| `Sheaf.Paper.FiniteCoefficientPoint` | `pointFiniteFibre`'s exact sections and instances, `pointIntegralFibre`, `pointFibreIntegralAmbient`, `pointRationalFibre`, `pointFibreRationalLarge`, `pointRationalFibreObjIso`, `pointFibreSizeDescent`, `pointRationalFibreScalarIso`, fraction-field exactness instances |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | `frobeniusPointIso`, `frobeniusPointPrimeInvertible`, `frobeniusPointTransportFinite`, `frobeniusPointTransportIntegralConstructible` |
| `Sheaf.Paper.IntegralPullbackComposition` | Recorded integral composition interface, specialized by the specified realization dependency |
| `Sheaf.SixFunctors.SchemeFrobenius` | `FiniteFieldDatum.schemeFrobeniusIterate`, `FiniteFieldDatum.schemeFrobeniusCoefficientInvertible` |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | `FiniteFieldDatum.canonicalSchemeGaloisComparison` |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | The existing integral scalar normalization data and tensor units/associators used by the prescribed comparison family |
| `Sheaf.Paper.PointSectionsScalarExtension` | The prescribed rational sections comparison, as used by `pointRationalFibreScalarIso` |
| `Sheaf.Paper.SfRationalizationKaroubi` | `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`, `sfRationalScalarExtension` |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | `IntegralComparisonSystem`, `integralComparisonComposition`, `integralComparisonScalar`, `integralComparisonConstructibleScalar` |

Additional existing helpers are reused, not redefined: `localExtensionPoint`,
`localPositivePower`, `localPullbackObjectIso`, `localPointTransport` from
`Sheaf.Paper.LocalFrobeniusTrace`; `pointFrobeniusAut`, `pointPowerPullbackModel` from `Sheaf.TraceFormula.PointTransportComposition`;
`FiniteFieldDatum.frobeniusCoherenceAnnihilator` from
`Sheaf.Paper.FrobeniusCoefficientReductionCoherence`; and full faithfulness of
`DerivedCategory.singleFunctor` from Mathlib. The remaining private imports are
recorded proof dependencies, retained for stage 3. The finite constant-pullback,
completed pullback, simultaneous quotient tower and Roos constructions are the
recorded dependency implementations, not private replacement definitions.

### Edge cases checked

* r = 0 means m = 1 and the point-iterate definitions start with exactly one
  transport. n = 0 means A_(E,1), not an excluded first quotient.
* A point rational over a proper subfield of F_(q^m) remains allowed; none of the
  return/fixed equations assumes m is its minimal period.
* An empty X0 has no specified y, so the theorem makes no false existence claim.
  Zero objects and zero complexes remain included in all three coefficient stages.
* Nonreduced separated finite-type models and singular models are allowed; no
  smoothness, properness, regularity or finite Tor dimension is assumed.
* Ramified finite coefficient extensions are allowed. The strict formulas use
  quotient maps; no flatness assertion about quotient coefficient changes is made.
* Rational naturality ranges over the entire rational Hom module. Scalar extension
  includes the identity embedding and composite embeddings in every finite tower.
* Derived point-module Hom universes are u+1, while the ambient sheaf derived
  categories use u+2. Explicit existing HasDerivedCategory instances preserve this
  convention; no equality between site and coefficient universes is postulated.
* All variables and universes are bound explicitly; `autoImplicit` is disabled.

### Searches

* `msearch.py Q04 <item> leanfinder "Geometric Frobenius rational point transport natural scheme Frobenius normalization scalar extension"`:
  eight results about field/scheme Frobenius (`SpecToEquivOfField`, arithmetic
  Frobenius at primes, field Frobenius etc.); no theorem with the present statement.
* `msearch.py ... loogle '"frobenius", "stalk"'`: zero results.
* `msearch.py ... grep 'Frobenius.*(stalk|transport)|((stalk|transport).*Frobenius)' AlgebraicGeometry`:
  zero results.
* `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`, plus the prescribed exact-item-id grep in the upstream source:
  no declaration with the full statement. Nearby modules were LocalFrobeniusTrace
  (definition of local operators), PointTransportComposition (finite iterates) and
  FrobeniusStalkTrivializationNormalization (a different normalization statement).
* The upstream name index and dependency source declarations were consulted.
  Current-source inspection through `scompile.py --source` confirmed the coefficient
  annihilator's namespace and the live interfaces. No new independent notion was
  found necessary and no existing definition was replaced.

### Verification

Only the owning module and its node record are delivered. The saved packet was
first checked as instructed: `deliver2.py --no-push` passed preflight and per-file
compilation (dry-run commit `f93f7cd7e9`). The repairs then changed the finite
transport construction and the report's second reading; they retain the main
signature and every node field outside `lean`. The declaration list includes
`finitePointIterate` and matches every declaration in the delivered file.

The compile-budget repair explicitly reuses the existing point and scheme
invertibility instances in the transport maps, rational realization and all
normalization clauses. A diagnostic profiler confirmed repeated failed
residue-field comparisons during inference (individual searches took up to about
two seconds). This changes no construction or hypothesis; profiling options are
removed from the delivered module.

The repaired source passed `scompile.py` cleanly in both sandbox and library-artifact
compilation, with no warnings. The prescribed `deliver2.py --no-push` checks the
same packet again for preflight and per-file compilation. Every invocation uses
the unchanged 60-second per-file limit; wrapper timings include slot acquisition.
No live library file or shared Git state is edited directly, and no global build
is run.

## Second reading by Q04

This is the required second self-reading: no other agent was started, as the
worker brief explicitly forbids it. I opened the node and source again and checked
each hypothesis and conclusion as follows.

1. Global data: the theorem binds `D : FiniteFieldDatum`, the prime `l` and
   `hl : l ≠ D.p`. It binds the finite extension through `Field E`,
   `Algebra ℚ_[l] E` and `FiniteDimensional ℚ_[l] E`. The given model is
   `X₀ : Over (Spec (.of D.k₀))`; local finite type, quasi-compactness and
   separation are precisely its three scheme hypotheses. No smoothness,
   properness or Tor bound occurs. The coefficient and site universes retain
   the recorded dependency conventions.
2. Point and exponent: `r : ℕ` encodes every m=r+1≥1; `y : D.extensionPoints`
   is the specified finite-field point. `localExtensionPoint` supplies its
   geometric point, while `D.geometricFiber` and the recorded Frobenius maps
   supply X, g_X and g_s. Nonminimal periods remain allowed. `n : ℕ` in
   `Normalization` likewise encodes every finite exponent n+1≥1.
3. Chosen comparisons: `C : IntegralComparisonSystem l` is the stipulated
   realization family, used by `integralComposition` and `rationalScalar`.
   The integral and rational categories are the recorded constructible category
   and its raw scalar localization, with all rational morphisms retained.
4. Return and definition of t: `returnEquation` is the node's semilinear square.
   The returned version substituted `pointPowerTransportFinite` for the node's
   successive finite transports; this was the H3/H4 mismatch. The repair adds
   `finitePointIterate`: its zero branch performs one recorded
   `frobeniusPointTransportFinite` followed by `pointPowerPullbackModel`; its
   successor branch performs one step and recursively performs r+1 further
   steps on that pullback, then applies
   `proEtaleConstantRingPullbackComposition`. Thus index r performs r+1 steps.
   `finiteTransport` uses r=m-1, reindexes by `Nat.sub_add_cancel hm`, and
   applies `finiteReturn`. `integralPointIterate` and `rationalPointIterate`
   already had the corresponding successive definitions and were retained.
5. Naturality: conjunctions 1, 4 and 6 of `Normalization` quantify over every
   morphism in the finite, integral and framework rational categories,
   respectively, and assert J(u) ≫ t_L = t_K ≫ J(G^m u). The first conjunct
   now refers to the repaired successive finite map through `finiteTransport`.
6. Finite normalization: `fixedEquation` supplies Phi^m ybar=ybar;
   `finiteRho` uses that equation and the canonical compositor.
   `finiteKappa` uses `canonicalSchemeGaloisComparison` with its specified
   absolute-Frobenius normalization and coefficient annihilator. Conjunct 2 is
   precisely t = rho ≫ J(kappa), now for the successive finite t. There is
   no scalar rescaling or extra annihilator hypothesis on the main theorem.
7. Whole strict equality: `finiteOrdinary false` extracts the repaired
   `finiteTransport` on single sheaves through the fully faithful single
   functor; `StrictFormula false` uses those exact ordinary term maps.
   The true recipe still uses rho/kappa. `strictRecipe_existsUnique` fixes
   the natural morphism of entire towers, including differentials and quotient
   transitions. Conjunct 3 equates those whole maps on every good simultaneous
   representative. The repair therefore reaches the strict maps as well as
   the first two conjuncts, without a separate power-transport theorem.
8. Integral and rational realization: conjunct 5 compares `integralDirect`
   with `integralNormalized` for every good P and representing isomorphism e.
   The latter applies the actual whole strict map through `integralOperationsRoosMap`
   and `integralModel`, including both Roos cone components. Conjunct 7 is
   its rationalization via `pointFractionDerived` and `rationalFibreModel`.
   Neither restricts reductions to perfect complexes or finite Tor amplitude.
9. Coefficient extension: the last conjunct quantifies over every finite M and
   `ι : E →ₐ[ℚ_[l]] M`. `rationalFibreScalar` is b, composed from the specified
   point-sections and pullback comparisons; `rationalScalar` gives d. Its
   equation is `(t_E tensor M) ≫ b_(G_E^m K) ≫ J_M(d_K) = b_K ≫ t_M(TK)`.
   Identity and composite embeddings use the same recorded tensor units and
   completion-normalized associators; no auxiliary comparison is chosen.
10. Self-check: m=1 performs exactly one step; m=2 performs two steps followed
    by the canonical compositor. m=0 remains excluded, every finite coefficient
    level is included, and empty schemes make no point-existence assertion.
    All definitions have real bodies, every postponed theorem has its proof
    docstring, and the main docstring retains all ten DAG proof steps.
    The two `letI` witnesses in `Normalization` are now named and passed
    explicitly to the same helpers. The rational pullback/scalar helper also
    receives its point/scheme instances explicitly. These are precisely the
    witnesses already constructed from l≠p, so no hypothesis or map changes.

The finite-map mismatch is repaired without changing the node's mathematical
statement or dependencies. The H11 repair is the explicit match above, replacing
the previous generic account of a second reading.
