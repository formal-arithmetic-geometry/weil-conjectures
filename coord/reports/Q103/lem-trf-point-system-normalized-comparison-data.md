## Worker report

The module `Sheaf.Paper.PointSystemNormalizedComparisonData` states
`WeilConjectures.PointSystemNormalizedComparison.point_system_normalized_comparison_data`.
Its conclusion is nonemptiness of the explicitly specified simultaneous comparison data,
not the choice of a free natural isomorphism. Both postponed proofs (`exact_products`
and the main theorem) are named, carry this node's blueprint tag, and contain natural
language proofs. All definitions and instance declarations have actual data.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum.{t}` supplies the finite field, its algebraic closure, their
  characteristic, and geometric Frobenius. The point is `Spec (.of D.k)`.
  `l : ℕ`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the coefficient-prime conditions.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` give the finite extension. Its recorded integral ring,
  coefficient ideals, and constant quotient sheaves supply R and B_n. Index `n : ℕ`
  denotes the paper's exponent n+1. The chosen uniformizer only determines these
  existing ideals; no extra choice or condition is imposed.
- `r : ℕ` and `_hr : 1 ≤ r` give the required positive iterate.
  `F` abbreviates the actual `pointRestrictionInverseImage` along
  `PointSystemTransport.pointPower D r`. Its completed scalar action is the recorded
  one, transported through `inverseImageCompletedCoefficientMap`.
- The input category is `coefficientSequenceModules l E (Spec (.of D.k))`, the
  existing ringed sequence site of strict quotient-linear coefficient systems.
  `U` is `coefficientSequenceRestriction`, `X` its termwise complex functor,
  `G` the already recorded `PointSystemTransport.pull`, `LA` the existing
  `coefficientConstantTowerLimit`, and `L` exactly `coefficientSequenceLimit = Rlim U`.
  These are transparent abbreviations of existing constructions, not replacement
  categories or replacement towers.
- `Data.coefficient` is a natural chain isomorphism from U(G_r M) to F_r^Tow(U M),
  natural on the category of entire unbounded complexes. Its sectionwise identity
  is `coefficient_sections`, quantified over every M, degree, level and site object;
  it fixes the original quotient-linear transitions. `coefficient_projection` is
  precisely pi_n c_hat = c_n F(pi_n), with categorical composition in Lean order.
  `finite_tensor_unit` uses the actual `inverseImageFiniteComparisonComplex`, whose
  definition is the sheafified x tensor 1 map of part (a); it is invertible without
  a flatness condition. The original inverse-image system is retained throughout.
- `T` is `pointRestrictionSections l E D.k none`, i.e. evaluation at the final object
  with the action restricted through constant integral sections. The existing
  `PointSystemTransport.sections` is definitionally U followed by postcomposition
  with T, retaining every transition. Thus its complex functor is exactly the
  Gamma_bullet used in `zeta_model`; no equality of unrelated functors is assumed.
- `exact_products` asserts additivity and exactness of F and T, invertibility of
  their canonical `piComparison` for every countable family, and exact countable
  products in both ambient module categories. The projection formulas are those
  of these concrete functors: reindexing evaluates at (V,h^r v), and T evaluates
  at (s,id). Module actions are inherited from the original definitions. The
  extra r=0 case of this auxiliary assertion expresses the same exact identity
  functor and is used only to provide uniform canonical exactness instances.
- H is the existing `CategoryTheory.roosF`, with product `roosP`, endomorphism
  `roosU` = 1 minus transition shift, and coordinates `roosχ`, ordered (b,a).
  Thus its degree p+1 coordinates are P^p plus P^(p+1), with the specified
  differential (-db-(1-s)a, da). There is no independently chosen cone model.
- `Data.theta` and `eta` are natural total-limit identifications on ALL ambient
  completed-module towers and ALL integral scalar towers. `theta_normalized` and
  `eta_normalized` require their derived units on every K-injective tower with
  injective terms to be exactly Q of a quasi-isomorphic inclusion whose coordinates
  are (0, tuple of the ordinary limit projections). Both inverse image and sections
  use this SAME theta, not independently selected models.
- `Comparison.product` and `product_projection` specify the canonical product map
  by every projection. `kappa` is a natural CHAIN isomorphism on the entire cone.
  `diagonal` specifies both projections in every degree, hence both product maps
  and zero off-diagonal terms. `Data.inverseImage` and `sections` supply this bundle
  for the two actual functors. For inverse image the requested target Y is read
  through `coefficient.inv`, as used in `a_model`.
- `Comparison.comparison` is a natural isomorphism on the ENTIRE ordinary unbounded
  derived tower category. `model` specifies it as theta inverse, kappa, Q(theta).
  `Data.a` and `zeta` are natural isomorphisms on the entire DERIVED SYSTEM category,
  with the displayed orientations. `a_model` and `zeta_model` are exactly the two
  conjugation formulas of the node, with all canonical localization factor isomorphisms
  visible. `systemRealization` is only their existing restriction-localization factor
  followed by theta; no arbitrary realization map is supplied.
- `Comparison.beta_projection` fixes every leg of the ordinary inverse-limit cone.
  Ordinary inverse limit is written termwise by `lim.mapHomologicalComplex` so that
  its universal derived unit is literally `rightDerivedFunctorUnitQ`.
  `resolutions` quantifies over EVERY pair of K-injective resolutions q and e, and
  requires the same comparison to equal Q(beta), the ordinary limit of e, and the
  two unit-normalized resolution identifications. This asserts independence of both
  resolution choices for the full map, not just after evaluation or on cohomology.
- `Comparison.augmentations` gives the actual (0,gamma) chain maps in source and
  target, with kappa carrying one to the other exactly. The localization model
  then says the same for the derived comparisons. Their shifted components are zero.
- `signedCoordinates` is the original cone chart followed by swap and the negative
  identity on the second summand. The identity natural chain isomorphism on the
  underlying cone therefore has coordinate expression J(b,a)=(a,-b). It gives H'
  by another coordinate presentation of the SAME complex. `signed_differential`
  states d'(x,y)=(dx,(1-s)x-dy); `Comparison.signed_diagonal` asserts the same
  product map on both summands after conjugation. Swapping (0,gamma) and negating
  its zero component gives (gamma,0), as the augmentation clauses specify.
- No input is required to be constructible, bounded, normalized, or complete.
  All quantified M, V, I, P, and derived-category objects have their unrestricted
  ordinary categories. Site universe t and coefficient universe u are independent;
  scalars use the existing `ULift.{t+1}` in `max u (t+1)`.

Dependency declarations used (read with signatures and docstrings):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions` and its finite coefficient
  conventions, reexported by PointSystemTransportDescent. No extra finite-type scheme
  is introduced for this point-only statement.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.schemeFrobenius` conventions and the recorded
  geometric Frobenius, used through `PointSystemTransport.pointPower`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the actual constant-to-completed action.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, for actual system
  categories and componentwise exactness, reexported by the recorded strict system API.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus` and the existing sequence realization
  `coefficientSequenceLimit`, retaining the ordinary unbounded system category.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `Scheme.isoSectionwiseInverseImage_equivalence` and module inverse-image exactness.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `inverseImagePullbackComparisonDerived`, reexporting the actual finite insertion
  `inverseImageFiniteComparisonComplex` and completed coefficient map.
- `Sheaf.Paper.CoefTowerCoaugmentation`: `WeilConjectures.CoefTower.adjunction` and
  `totalLimit`, with the genuine ordinary constant/limit cone.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `Scheme.ProEt.countableProducts_exact`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit` (proof import).
- Mathlib `Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, its factor and triangulated instances.
- `Sheaf.Paper.PointSystemTransportDescent`: existing `pointPower`, `pull`,
  `sections`, `derivedSections`, and their exactness instances. Its plain definitions are
  now owned by def-trf-point-system-functors, which replaces the transport theorem
  in stmt_deps as requested by L/H2 at 56bc8cb67643.
- `Sheaf.CategoryTheory.StrictRoosModel`: existing `roosF`, `roosP`, `roosU`, `roosχ`.
  Its landed definition node is added to stmt_deps. The new module imports no
  downstream whole-Roos or whole-square theorem, so these additions do not introduce
  a dependency or import cycle.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedFunctorUnitQ`, for the explicit resolution normalization.

Edge cases checked: zero systems and complexes; zero transitions (1-s=1);
constant identity-transition towers (1-s is the difference map); arbitrary negative
cochain degrees; the first positive coefficient exponent; r=1 and the auxiliary
identity r=0; and independent site/coefficient universes. At the level of coordinates,
J d(b,a)=(da, db+(1-s)a)=d' J(b,a), its inverse is (-y,x), and its augmentation is
(gamma,0). These computations also verify the order and signs of both comparisons.
No mathematical statement correction or disputed statement is needed.

Searches for an existing exact statement:

- msearch.py leanfinder: "Simultaneous coefficient system and normalized Roos comparison
  natural isomorphisms for exact inverse image and sections on unbounded module towers".
  Eight results concerned Profinite.NobelingProof.succ_exact, localCohomology diagrams,
  Dold--Kan comparisons and condensed modules; no exact match.
- msearch.py loogle: "piComparison, Functor.mapDerivedCategory, CochainComplex.mappingCone".
  Zero hits; the service reported unknown identifier piComparison.
- msearch.py grep: "normalized.*[Cc]omparison|point_system|roos". Zero Mathlib hits.
- rg of Mathlib and the project's WeilConjectures/ and Sheaf/ trees for piComparison,
  point_system, PointSystemRoos and normalized comparisons. Generic exact-functor,
  products and cone APIs were found and reused. The live PointSystemRoosTransport
  module (also read using scompile.py --source) contains the LATER whole-transport
  theorem, with additional restriction-square and transport laws; that conclusion
  is stronger than this item and is not recorded as an exact existing match. Its
  theorem is not used or imported. The current item ID has no upstream declaration.

The prior retry had no Lean files in this sandbox and attempted a stage-1 packet on
an already reviewed split node. This delivery instead supplies the actual stage-2
module and a changed lean record; no launcher or project tool is modified.

## Second reading by Q103

No second reading by a worker: the dispatched human instructions require direct
delivery without starting other agents. The maintainer's independent review reads
this statement and its clause correspondence.

Validation: the full module compiled in sandbox and library module modes within the
unchanged 60-second limit, without errors or warnings. The delivery dry run passed
server preflight and per-file compilation. The final generic helper also explicitly
names its four derived-localization universes; these remain independent.

## New nodes

`def-trf-point-system-functors` owns the nine unchanged definitions `pointPower`,
`reindex`, `sequenceRing`, `coefficient`, `pull`, `sections`, `complexSections`,
`towerDerived` and `derivedSections` in `Sheaf.Paper.PointSystemTransportDescent`,
using an `existing: true` record. Its source is the integral-model blueprint proof
(3), point-factor prerequisite. Its clauses respectively specify the recursive
Frobenius iterate, identity-on-index site reindexing, the existing ring sheaf,
the uniquely fixed inverse coefficient maps, the actual module pushforward,
scalar-restricted whole-tower point sections, termwise complexes, standard
whole-tower derived localization, and descended sections. Site and coefficient
universes are independent; r=0 and arbitrary unbounded systems remain included.
No transport transformation or descent-theorem witness is chosen. The coefficient
helper is an exists-unique specification with every component prescribed.

Ownership searches: msearch leansearch for inverse image of strict coefficient
sequences along Frobenius and termwise sections returned eight unrelated module,
Witt-vector and perfection results; loogle for `SheafOfModules.pushforward,
Functor.mapDerivedCategory` returned no hits (unknown second identifier);
msearch grep for `PointSystemTransport|coefficientSequenceModules|pointPower`
returned no Mathlib hits. The exact tool result summaries and declaration names
are recorded in the new node. Project/DAG rg found the published definitions and
theorem-node records only; blueprint_refs search for `point system` returned zero
matching blueprint nodes. Thus there is no existing definition owner, while the
Lean constructions themselves already exist and are reused without duplication.

## Returned delivery repair

L/H2 at immutable head `56bc8cb67643`: replaced the added statement dependency
`lem-trf-point-system-transport-descent` with the new definition owner
`def-trf-point-system-functors`. The theorem is not used to construct the data
in the statement. The reviewed Lean signatures and mathematical clauses are
retained. The existing `def-weil-strict-roos-model` citation is retained as requested.
The new node's primary `lean.statement` is verbatim the existing `pull` signature;
all nine declarations were read in their published module with their docstrings.
No statement correction or citer change is needed.

Self-check of the repair: the item differs from the current read-only base only
in `lean` and `stmt_deps`; its statement, proof, proof dependencies and sources
are verbatim retained. The theorem stmt_dep is absent and the new def stmt_dep
is present. All nine existing declaration names and the primary signature were
checked against PointSystemTransportDescent. The new statement cites exactly its
six construction dependencies. Its `pull` formula uses the canonical coefficient
map, sections are exactly `U` followed by towerwise `T`, and the derived codomain
is the ordinary derived category of whole towers. These are precisely the
objects used by the unchanged comparison statement.

Compile repair: repeated unmodified-file dry runs hit 60 seconds, although the
server confirmation sometimes passed in about 53 seconds. Diagnostic profiling
showed about 27 seconds of linter work expanding the dependent coefficient data.
The sole source change from the returned Lean file is a comment and
`set_option linter.checkUnivs false`, the optional universe-usage linter. No
declaration, binder, instance, definition body, field or theorem signature changed;
`autoImplicit false` remains enabled, and all universes were checked explicitly.
Both sandbox and library modes then compiled cleanly within the unchanged limit
(33.9 seconds and 41.3 seconds respectively). Temporary profiling options and
temporary alternative implementations were removed.

Dry-run metadata repairs: the new node now cites each definition ID in its own
bracket, and its `blueprint.from.via` includes
`lem-trf-rational-global-frobenius-powers`, as required by the current server DAG.
The saved item's unchanged metadata is replayed by deliver2 against current main;
only its authorized `lean` and `stmt_deps` delta is delivered.
