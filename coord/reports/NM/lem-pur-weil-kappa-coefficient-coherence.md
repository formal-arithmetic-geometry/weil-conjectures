## Worker report

Repair of immutable returned heads 46d525037c04 and 251dbf669277. The former
arbitrary categories, functors, κ, changed-stage κ, free comparison records and
arbitrary tensor-route functions have all been removed. The main theorem fixes
only the actual purity datum P and the actual k₀-scheme T₀. All subsequent
coefficient fields, quotient levels and base-changed arrows are quantified in
the displayed equations; comparison data are never quantified.

The item statement is unchanged. Its existing non-Lean fields match the shared
current node. The only additional statement dependencies are the three new
helper-definition nodes below. Definitions contain real data, or select a
uniquely normalized map from a named existence-and-uniqueness theorem. None
selects an unnormalized isomorphism from Nonempty. Theorem proofs are sorry.

Hypotheses and objects:

* P : PurityFiniteSetting supplies primes p ≠ ℓ, a ≥ 1, q, k₀, k, a finite
  coefficient extension and the positive level. T₀ is an Over object over
  Spec k₀. LocallyOfFiniteType T₀.hom and QuasiCompact T₀.hom say finite type;
  IsSeparated T₀.hom says separated. The same hypotheses are present on T'₀
  and T''₀ wherever they occur.
* T is P.frobeniusFiber T₀, g is P.frobeniusGaloisMap T₀, Φ is
  P.frobeniusSchemeMap T₀, and u is P.frobeniusMap u₀. The finite H and G are
  proEtaleConstantRingDerivedPullback at those maps. The finite κ is literally
  P.schemeGeometricFrobeniusComparison T₀, or its recorded
  Purity.finiteReductionSchemeGeometricFrobeniusComparison presentation when
  paired with finiteReductionPullbackComparison.
* E and L are Type u fields, finite dimensional over Padic ℓ; scalar change
  uses an actual Padic-linear AlgHom. Integral objects use
  sfIntegralConstructibleCategory and finiteTorConstructibleIntegral. Finite
  objects use proEtaleDerivedCategory and finiteTorConstructible. Rational
  objects use sfRationalConstructibleCategory (over a field bounded objects
  have finite Tor amplitude); common-stage objects use the actual
  generalAlgebraicallyClosedConstructibleCategory of pairs.
* The small pro-etale site retains object universe u+1 and morphism universe
  u. The tensor calculation uses ModuleCat at u+1 and the existing ULift ring
  convention. No equality of site universes has been imposed. kappaFiniteDerivedCategory
  selects exactly HasDerivedCategory.standard at the native finite coefficient
  size, as already fixed by proEtaleDerivedCategory; it prevents the general
  IntegralHom.derivedCategory instance from introducing an unresolved universe.

Clause-by-clause translation (the seven components of KappaCoefficientCoherence):

* finite.finite_quotient is the coefficient square for the actual finite
  quotient functor, the recorded finiteReductionPullbackComparison and the
  specified κ at the changed PurityFiniteSetting. finite.simultaneous is the
  four-edge mixed coefficient/geometric equation, including the final scalar
  comparison for u. finite.coefficient_identity and coefficient_successive
  expand to KappaFiniteCoefficientIdentity/Composition: these use the actual
  scalar-extension unitor and multiplication associator, and the single
  composite quotient ring map. They are not inverse-followed-by-forward
  identities.
* geometric.geometric is the displayed equation for each actual u₀.
  kappaGeometricH/G are exactly inverse frobeniusDerivedComposition, eqToIso
  of the actual commuting scheme-map equality, and frobeniusDerivedComposition.
  geometric_identity and geometric_successive compare the actual square map
  with the specified identity and successive-pullback compositors. No
  smoothness or Cartesianity of the Frobenius square is assumed.
* integral.integral_reduction uses the actual derived reduction,
  integralPullbackReductionIso and kappaFiniteFor at A_{E,n+1}, on a good
  representative of the given finite-Tor object. integral_scalar uses the
  actual sfConstructibleIntegralScalarExtension and the recorded
  integralPullbackScalarComparison. integral_geometric uses integralComparisonConstructibleComposition for the recorded simultaneous
  whole-system realization, conjugated along the commuting square.
* strict.strict_geometric and strict_geometric_inverse are equations of maps
  of entire cochain complexes of coefficient-sequence modules, on complexes representing the actual normalized reduction systems of
  bounded constructible finite-Tor objects. Their comparison maps use integralComparisonSequenceComposition.
  sequence_realization explicitly identifies the completed κ with this same
  sequence-site map under the recorded simultaneous realization models.
  Thus every quotient transition and every differential is present before
  localization or Rlim, also for inverse κ. strict_scalar and
  strict_scalar_inverse are equations of maps of whole actual pullback towers,
  using scalarPullbackTower on good representatives with finite-Tor
  constructible realizations. strict_inverse_normalization fixes every inverse
  level map to kappaStrictLevel.inv. realization identifies kappaIntegral
  with DerivedCategory.Q applied to the Roos map of that exact whole κStrict,
  via integralDerivedPullbackComparison. No faithfulness of finite derived
  evaluations is used.
* field.rationalization is the actual scalar-localization image of the
  integral κ. rational_scalar is the finite-field-extension equation with
  rationalPullbackScalarComparison. common_stage gives the exact ofHom
  representative at EVERY common finite field L containing N.stage, using
  commonStagePullbackComparison and κ over Coefficient L. rational_geometric
  and common_geometric give the corresponding actual geometric square maps.
  The inverse transformations are the inverses of these specified natural
  isomorphisms, not independently selected maps.
* mixed.integral_coefficient_laws and rational_coefficient_laws state unit
  and successive-extension equations using sfIntegralScalarUnit/Comp and
  sfRationalScalarUnit/Comp. integral_simultaneous and rational_simultaneous
  spell out the two four-edge mixed routes KappaIntegralMixed and
  KappaRationalMixed. The common-stage representative characterization at
  every L transports these same equations to the pair category and its
  enlargement identifications.
* equivariant.equivariant_precomposition is the actual naturality chain
  κ_N ≫ φ_N ≫ z = H.map z ≫ κ_M ≫ φ_M under φ_N ≫ z = G.map z ≫ φ_M.
  finite_equivariant_transport and geometric_equivariant_transport give the
  exact comparison-inverse formulas from proof step 7. The definitions
  kappaFiniteEquivariance, kappaIntegralEquivariance,
  kappaRationalEquivariance and kappaCommonEquivariance reuse Mathlib's
  Endofunctor.Algebra.equivOfNatIso at those actual κ. They supply the forward
  and inverse functors on equivariant arrows, so identities, composition,
  and all finite diagrams are preserved. finite_pasting explicitly states
  the κ precomposition equality for each edge of a finite diagram with a
  natural G-structure. Comparison edges use the preceding actual square
  equations.
* equivariant.tensor_restriction is an equation about the actual section
  restriction M.obj.map along kappaRelativeFrobenius.hom.app V, and the
  actual ModuleCat.extendScalars.map at the actual quotient ring map. Its
  input is a generalized tensor generator b ⊗ x. Its right-hand value is
  b ⊗ r*(x), the module convention for the paper's r*(x) ⊗ b. V and M are
  arbitrary site objects and sheaves; this is not a constant-global-section
  or arbitrary-functions assertion, and the two expressions are different
  routes. The relative site map is the one from the recorded canonical
  absolute-Frobenius trivialization.

Dependency declarations used (all in namespace WeilConjectures unless stated):

* Sheaf.Paper.PurityFiniteSetting: PurityFiniteSetting.
* Sheaf.SixFunctors.SchemeGeometricFrobenius:
  PurityFiniteSetting.schemeGeometricFrobeniusComparison,
  frobeniusDerivedComposition, schemeGeometricFrobenius_factorization,
  frobeniusFiber, frobeniusMap, frobeniusGaloisMap and frobeniusSchemeMap.
* Sheaf.Paper.PurityTateDatum:
  Purity.finiteReductionSchemeGeometricFrobeniusComparison. Its generic
  CondensedStrictWeilDatum is not misrepresented as supplying the missing
  integral/rational/common-stage κ maps; those are constructed in the new
  stage-map module.
* Sheaf.Paper.BasicOperationsCoefficientReduction:
  basicOperationsCoefficientReduction; the concrete component interfaces
  integralPullbackReductionIso, integralPullbackScalarComparison,
  rationalPullbackScalarComparison, commonStagePullbackComparison, and the
  actual finite reduction and coefficient-change functors.
* Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback:
  AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization_pullback.
  Its normalized ordinary compositor and relative-Frobenius pullback mate
  determine kappaOrdinaryFor. kappaOrdinary_derived identifies its exact
  derived image with the recorded finite κ.
* Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite:
  AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization, through
  the canonical trivialization's site components.
* Sheaf.Paper.IntegralOperationsWellDefined:
  integralOperationsPullbackTowerFunctor, integralOperationsGoodComplex,
  integralOperationsGoodLocalization, integralOperationsRoosFunctor,
  integralDerivedPullback and integralDerivedPullbackComparison.
* Sheaf.Paper.IntegralFinitePullbackComposition:
  integralFinitePullbackModel. Sheaf.Paper.IntegralPullbackComposition:
  integralComparisonConstructibleComposition and the single
  integralPullbackComparisonRealization_simultaneous system.
* Sheaf.Paper.IntegralComparisonSequenceSystems:
  integralComparisonSequencePullback, integralComparisonSequenceComposition.
  Sheaf.Paper.OrdinaryPullbackCompositionEvaluation:
  PullbackCompositionTransport.ordinaryEvaluation.
* Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients:
  GeneralAlgebraicallyClosedCoefficients.ofHom and the actual pair category;
  the existing commonStageDerivedPullback functor and its representatives.
* Mathlib.CategoryTheory.Endofunctor.Algebra:
  CategoryTheory.Endofunctor.Algebra.equivOfNatIso (used, not copied).

All recorded statement-dependency modules are public imports. The module also
imports all recorded proof-dependency modules; the main theorem docstring gives
the seven source proof steps, including actual ramified em→m transitions,
whole-system counits, scalar localization and finite pasting.

Edge cases read against the formulas: empty T₀; zero object and zero equivariant
arrow; m = P.level; positive quotient n+1 (n=0 is exponent 1, never a nonexistent
zero quotient); identity coefficient change and E=L; identity and successive
u₀; non-flat quotient maps (derived extension remains derived); ramification
index e>1 (the actual comparison em→m is retained and not inverted); inverse
κ; arbitrary weakly-etale V and zero tensor generators. No extra flatness,
smoothness, Cartesianity, nonzero-object or derived-evaluation-faithfulness
hypothesis is introduced.

Searches: msearch leanfinder for canonical Frobenius comparison on integral
quotient systems returned eight ring-Frobenius/perfection declarations, no
exact statement. msearch loogle for Endofunctor.Algebra.equivOfNatIso returned
the actual equivalence and four formulas; the equivalence is reused. msearch
grep for schemeGeometricFrobenius|kappaStrict|kappaIntegral|kappaSequence found
no Mathlib match. rg of lean/WeilConjectures and lean/Sheaf found the recorded
finite κ and its finite-reduction presentation; neither supplied its specified
strict integral, rational or common-stage extension. DAG grep and
blueprint_refs.py search kappa found the parent and generic comparison nodes,
which are reused. The new nodes retain the msearch records, including the
queries and actual returned names. None of the new declarations is an existing
Mathlib or project declaration.

No STATEMENT-DISPUTED and no mathematical statement correction is claimed.
The final four-file scompile.py run passed with no errors or unexpected
warnings: library times 22.0, 16.7, 32.0 and 41.8 seconds, respectively.
Every file is within the 60-second limit. deliver2.py --no-push returned
OK: the delivery passes the server preflight and per-file compiles.
The sequence-site uniqueness construction uses the full named
KappaSequenceNormalization predicate and an explicit isomorphism result type
to avoid repeated expansion during elaboration. Diagnostic markers and profiler
options were removed; no time, heartbeat or transparency limit was changed.

## New nodes

* def-pur-kappa-coefficient-stage-comparisons owns PurityKappaStages.lean:
  the specified ordinary κ, its whole strict map, normalized completed
  descent, constructible lift, rational localization, common-stage descent
  and actual equivariant precomposition equivalences. Source: the item’s
  Returned Step 11, steps 1, 4 and 6. The searches above found the finite κ
  but no such normalized stage interfaces. Existing coefficient categories,
  functors and presentation changes are reused throughout.
* def-pur-kappa-geometric-compositors owns KappaGeometricComparisons.lean:
  specialized canonical geometric square maps for the base change of an
  actual u₀, coefficient comparison natural isomorphisms with prescribed
  existing components, whole sequence-site comparison, and the specified
  identity/composition maps. Source: Returned Step 11, steps 2–6. These are
  composites of existing canonical maps, not a second definition of derived
  pullback or scalar extension; searches found only those general maps.
* def-pur-kappa-mixed-comparison-equations owns KappaMixedCoherence.lean:
  explicit predicates for the two mixed routes and the finite, integral and
  rational scalar unit/composition equations. Source: Returned Step 11,
  steps 3, 5 and 6. These exact composite predicates did not exist; their
  definitions contain the full formulas, no arbitrary comparison inputs.

## Second reading by NM

This is a second self-audit; no separate reviewer or subagent is claimed. I
compared the returned counterexamples and the node with all four modules.

The old central-automorphism counterexample cannot instantiate the theorem:
there is no jG parameter. The Bool arbitrary-functions counterexample cannot
instantiate tensor_restriction: both restriction and scalar map are actual
project constructions. P and T₀ occur in every category and map. The changed
finite stage is P.finiteReductionSetting, the integral stage is its actual
strict-system descent, the rational stage is its actual scalar localization,
and common stages are quantified over every actual representative. Geometric
maps are built from actual u₀ and both Frobenius commuting equalities.

I also checked the composition order, the presence of finite-Tor hypotheses,
whole-system forward and inverse geometric/scalar equations before Rlim,
ramified tower indices, the non-reflexive tensor equation, and the seven proof
steps. The large proposition was separated into named groups for elaboration;
this does not replace any equation by a label or a duplicated conjunct. The
new node signatures and declaration lists were checked against all explicit
declarations in the final source. The item’s original mathematical statement,
proof and proof dependencies remain unchanged.
