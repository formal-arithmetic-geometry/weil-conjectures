## Worker report

The module `Sheaf.Paper.RationalPurityExchangeEndpoints` states
`WeilConjectures.RationalPurityExchangeEndpoints.rationalPurityExchangeEndpoints`.
Its sole postponed proof is the whole proof of that theorem. All helper definitions
have real data: functor composition, whiskering, and ordinary associators; the two
records organize specified data and equations without choosing any object from an
unconstrained existence theorem.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum.{u}` contains the prime p, a >= 1, q = p^a, finite base
  field and its fixed algebraic closure. `C : D.CoefficientDatum` contains the
  coefficient prime ell, ell != p and its fixed algebraic closure. The simultaneous
  field index `AdicPurityScalarNaturality.Field D C` is the existing type of finite
  intermediate coefficient fields. Thus quantification over E,F,L includes equality
  and every coefficient tower, rather than just strict field extensions.
- Each of X,X',Y,Y' has its `Over (Spec (.of D.k))` instance and the locally
  finite-type, quasi-compact and separated structure morphism instances. These
  render exactly separated finite-type k-schemes. All four arrows have `IsOver`
  instances. `sq : IsPullback uMap f' f v` renders the Cartesian square, including
  its commutativity; no special model of the fibre product is required.
- `d : ℕ`, `[SmoothOfRelativeDimension d f]`, `[IsSeparated f]` render smooth,
  separated, pure relative dimension d >= 0. The remaining finite-type f instances
  are consequences of the stipulated k-scheme hypotheses, needed to call the
  published exceptional system. Neither u nor v has a smoothness hypothesis.
- The first four conjuncts `BaseConditions` assert Noetherianity, finite
  topological dimension and stalkwise invertibility of ell on all four schemes.
  The four `LatticeDomain` conjuncts assert that every raw rational object has an
  integral constructible representative with `finiteTorConstructibleIntegral`:
  the interval is quantified once before all positive reductions. The next
  conjunct `PullbackLattice v` asserts integral pullback
  of a representative and the actual rational derived-object isomorphism.
- The existential witnesses hSmooth,hSep,hLft,hQc establish the base-changed
  morphism's geometry, before it is supplied to the dependent exceptional and
  integral purity interfaces. They are conclusions, not added assumptions.
  The explicit instance lambda merely passes these proved witnesses to the types.
- `RCat`, `Q`, `T`, `alpha`, `unit` are the existing raw rational category,
  localization, exact coefficient extension, tensor associator and tensor unitor
  in `RationalScalarComparisonData` (the namespace remains
  `RationalScalarComparisonIdentification`). No Karoubi envelope is used.
  Integral and rational operations use `DerivedPullbackTensorHom`; twists use
  `IntrinsicCoefficientTwistsUnrestricted` through the recorded canonical source.
- The statement is universal in the two supplied exceptional systems S,S' and
  simultaneous integral purity families I,I'. These are precisely the families
  the node says to use, not arbitrary purity transformations. Their existence is
  the already recorded theorem `adicPurityScalarNaturality`. The conclusion
  provides R,R', their normalized rationalizations. `LocalizedFamily.hLocalization`
  and `hNormalized` impose the retained good-representative characterization
  `SourceLocalizationNormalization`; `gammaLocalized` identifies the rational
  purity map with Q(I.gamma), using the fixed exceptional localization comparison.
  Consequently these are the stated rational purity convention, not independently
  selected dualizing isomorphisms.
- The source `H` is the published `rationalSource`, with the shifted Tate line
  on the left of rational tensor. Its retained normalization is the canonical
  tensor symmetry and even-shift identification with D Lh*, where D(M)=M(d)[2d].
  `aCanonical` identifies each component with `sourceScalar`, whose definition is
  the tensor scalar comparison, followed by the scalar shift/Tate-line comparison
  in the first slot and `rationalPullbackScalarComparison` in the second. This is
  precisely D(p_h) q in those published coordinates; `aLocalized` additionally
  identifies it with the same integral a, through the normalized scalar bridge.
- The exceptional comparison is always the existing `b D C f S E F h`, never a
  variable or a conjugate by purity. `bMate` is its equality with
  `coefficientTranspose`: the adjoint transpose of inverse compact-support
  comparison followed by scalar extension of the old exceptional counit.
  `bLocalized` identifies it with the integral family's b.
- `LocalizedFamily.purity` is exactly (P), on every rational object, together
  with its inverse equation. Gamma and a are natural isomorphisms on the full
  rational categories, so their naturality includes all localized morphisms.
  `hLocalizationShift,gLocalizationShift,scalarLocalizationShift` retain the
  integral normalization of every localized shift.
  `aUnit,bUnit,aTower,bTower,gammaShift,aShift,bShift` render the localized unit,
  successive-extension and shift equations of that same family.
- `endpointA ... false/true` are respectively Lu* H_f and Lu* G_f;
  `endpointB ... false/true` are H_f' Lv* and G_f' Lv*. `comparisonA ... false/true`
  are r_A,beta_A and `comparisonB ... false/true` are r_B,beta_B.
  `compositeComparison` pastes the factors in precisely the displayed order.
  Its components are p_u followed by Lu*(a_f) or Lu*(b_f), and a_f' or b_f'
  followed by H_f'(p_v) or G_f'(p_v), respectively.
- `s` is whiskering of gamma_f inverse by Lu*; `tGamma` is whiskering of gamma_f'
  by Lv*. `EndpointEquations.squareA` is T(s_E) followed by r_A = beta_A followed
  by s_L; `squareB` is T(t_E) followed by beta_B = r_B followed by t_L. Lean's
  composition is in diagrammatic order, the reverse of the printed circle order.
  Both are literal equalities of natural transformations in K, including the
  evaluation of the L-purity map at T_Y K.
- `unitA/unitB` instantiate `UnitEquation` for both Boolean values, hence all
  four comparisons, using the existing tensor unit identifications. `towerA/B`
  instantiate `CompositionEquation`, again for both values, with exactly the
  existing `alpha` at X' and Y carried through the chosen endpoint functor.
  These are the node's displayed w_{L/E} alpha_in = alpha_out w_{L/F} T(w_{F/E}).
- `shiftA/B` compose the normalized pullback shifts from `fieldRationalPullShift`
  with the source or exceptional shifts already fixed by R,R' and S,S'.
  `shiftComparisonA/B` give all four w(K[1])=w(K)[1] equations (in fact their
  coherent integer-shift form). `shiftS/shiftT` assert the same compatibility
  for the endpoint purity maps. Together with squareA/B and the factor purity
  squares, the unit and tower equations express compatibility of (P),(A),(B)
  with these identifications: substituting the unit/tower equalities changes
  each side by exactly the same source and target maps. No new identification
  of b is introduced.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, and its imported
  `FiniteFieldDatum` and `CoefficientDatum` for the fixed geometry and coefficients.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  scheme fibre-product convention; `CategoryTheory.IsPullback` expresses an
  arbitrary Cartesian square with the named four arrows.
- `Sheaf.Paper.PbcRationalCategory`: `Scheme.PbcRationalCategory`,
  `pbcRationalization`, raw scalar localization of integral objects and tensor Homs.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `rationalPullbackScalarComparison`,
  `rationalDerivedTensor`, with their retained object and localization formulas.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the integral/rational Tate
  coefficients used by the canonical source, with positive, zero and dual twists.
- `Sheaf.Paper.PbcScalarExtension`: exact scalar extension and its tensor
  associators; the intrinsic presentation is the one already used by the
  recorded scalar-comparison-identification interface, including its actual T.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` (public data module):
  `Operation`, `System`, `FieldSystem.rationalComparison`,
  `FieldSystem.rationalizationComparison`, `FieldComparison.b`, counit normalization.
- `Sheaf.Paper.AdicPurityScalarNaturalityData`: `Data`, `source`, `target`,
  `scalar`, `scalarBridge`, `ShiftCompatibility` and `composeShift`; every supplied
  I has the prescribed finite reductions. Its existence theorem
  `adicPurityScalarNaturality` remains an existing proof input.
- `Sheaf.Paper.RationalSmoothPurityCanonical`: canonical `rationalIso` convention;
  `PuritySourceTransports.rationalSource/sourceScalar` are used through H and the
  source normalization in the already published scalar-identification interface.
- `Sheaf.Paper.RationalScalarComparisonData`: RCat,Q,H,G,O,T,b,
  coefficientTranspose,gLocalization,integralB,alpha,unit,h/g/t shifts,
  `SourceLocalizationNormalization`, `LocalizesComparison`, `PuritySquares`,
  `UnitEquation`, `CompositionEquation`. These definitions, owned by
  `def-pur-rational-scalar-comparison-data`, are the actual statement dependencies.
  `LocalizedFamily` records normalized data using these predicates; neither
  `Result` nor `rationalScalarComparisonIdentification` occurs in its signature.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`, owned
  by `def-weil-derived-complete-integral-detailed`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, through `FiniteTorAmplitude`:
  `finiteTorConstructibleIntegral`, owned by `def-weil-finite-tor-amplitude`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleLocalization`,
  owned by `def-weil-rationalization-karoubi`.
- `Sheaf.Paper.PuritySourceTransports`: `RationalSmoothPurityCanonical.sourceScalar`,
  owned by `def-pur-canonical-purity-source-transports`.
- `Sheaf.Paper.FieldWeilShriekShiftData`: `fieldRationalPullShift`, characterized
  by localization of the representative-normalized signed integral shift.
- Proof inputs imported privately: `RationalScalarComparisonIdentification`
  (its theorem is used by the natural-language proof plan), `RationalLatticeAdicDomain`,
  `IntegralOperationsPreserveConstructible`, and Mathlib's Etale/Smooth module
  for smooth dimension, separatedness and finite-type base-change permanence.

The added statement dependencies are existing definition nodes:
`def-pur-rational-scalar-comparison-data` for the normalized comparison predicates,
`def-zl-field-weil-shriek-shift-data` for the canonical pullback shift, and the five
owners listed above for the integral category, uniform finite-Tor predicate, raw
rationalization, canonical source scalar comparison and integral `Data` interface.
The identification theorem remains in `proof_deps` and is imported privately.
No new node, dependency module, or mathematical statement correction is needed.

Edge cases checked before writing: an empty X' still has dimension-d smoothness
(the chart condition quantifies over its points), so no nonemptiness, maximum of
empty chart dimensions, or dimension of the empty scheme is used. Empty other
schemes and zero objects remain permitted. d=0 uses the same unit Tate line and
zero even shift; no positive-dimension assumption enters. Torsion lattices are
included by `finiteTorConstructibleIntegral`, not replaced by torsion-free
lattices. Identity coefficient inclusions, equality inside either leg of a tower,
and arbitrary v are included. All schemes and finite subfields use the existing
common universe u; the pro-etale site's object/morphism and derived universes
are inherited unchanged. No additional site-universe equality is imposed.

Searches for an existing statement:

- `msearch.py leanfinder`: "Rational smooth purity scalar extension compatibility
  at inverse and direct purity endpoints of base change" returned eight generic
  smooth/base-change ring results, no purity endpoint equation.
- `msearch.py loogle`: `"purity", "scalar"` returned zero hits.
- `msearch.py grep`: `purity.*scalar|scalar.*purity`, Mathlib AlgebraicGeometry,
  returned zero hits.
- `msearch.py leansearch`: "Coefficient extension commutes with smooth purity and
  inverse purity in constructible derived categories" returned eight unrelated
  coefficient/perfection/smoothness and generic exact-functor shift declarations.
- `rg` in `lean/WeilConjectures` for the item id and purity/scalar combinations:
  no exact statement. `rg` in `lean/Sheaf` located the recorded integral and
  rational scalar-comparison families, canonical source transports, lattice
  domain and pullback shifts, all reused. `RationalPurityTraceCoherence` has
  geometric base-change source maps and a broader theorem; it does not state
  these four specified scalar endpoint comparisons with their full unit,
  tower and shift equations. No duplicate declaration was found.

Current source: read `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/_section.md`, `sk-thm-purity-transport.proof.md` and
`sk-thm-purity-transport-coefficient-change.proof.md`. The older source filename
in the DAG has been refactored in the current blueprint; the new documents
retain the integration-normalized adjoint, coefficient-change equations and
base-change conclusion. The node itself requires no mathematical correction.
No STATEMENT-DISPUTED issue was found for the stated endpoint equations.

Validation: the prescribed scompile.py server compile successfully elaborated the
optimized module: 59.2 seconds for its sandbox check and 53.9 seconds under its
library module name. There were no errors; the only warnings concerned temporary
profiling options, which are now removed. The final delivery dry run compiled the clean file without warnings and
reported OK: commit 20292b218f7 passed preflight; nothing was pushed by that check. An earlier dry run exceeded the per-file limit at 64.5 seconds;
explicit endpoint functor result types and local abstraction boundaries now avoid
repeated unfolding while elaborating the endpoint equations. The scalar functor
remains transparent while constructing the canonical pullback comparisons, and
is abstracted only after these constructions. A preceding server-connection
timeout occurred while building upstream overlays and was retried unchanged.
The initial heartbeat failure was repaired by retaining the existing operation
interfaces as abstract during record elaboration and disabling unused generated
record auxiliaries. Dependent Boolean choices use explicit pattern matching;
shift structures have the required instance-reducibility annotation. No runtime
limit was raised and transparency checking remains enabled.

## Second reading by NE

I reread the node and the complete module, including every normalization field,
the two component-composition orders, and the Boolean indexing of the four
endpoint maps. No extra smoothness hypothesis on v or u is introduced; f'
geometry is a conclusion, not an assumption of the final theorem. Unit and tower
maps use the published scalar functors, not arbitrary identifications. The
localized purity is pinned by both its source normalization and its equation on
integral objects, and b stays the fixed counit mate. The only source proof left
postponed is the main theorem. This is a self-reading, not a claim of another
worker's independent review: the dispatch brief forbids starting another agent
and specifies the maintainer's independent delivery review.

## Repair of returned delivery f12d8df79f36

H2: replaced the added theorem statement dependency
`lem-pur-rational-scalar-comparison-identification` with its definition owner
`def-pur-rational-scalar-comparison-data`. Changed the public import to
`Sheaf.Paper.RationalScalarComparisonData`. The theorem module is now a private
proof import, matching its unchanged place in `proof_deps`; `Result` is unused.
The declaration namespace remains `RationalScalarComparisonIdentification` because
that is where the data module defines its declarations. All declaration bodies
and signatures are identical to the returned delivery.

Advisory addressed: added direct existing definition-node dependencies and public
imports for `finiteTorConstructibleIntegral`, `sfIntegralConstructibleCategory`,
`sfRationalConstructibleLocalization`, `sourceScalar`, and the integral `Data`
module. Read their recorded signatures and docstrings; the ownership mapping is
listed above. Checked that every added node is recorded and that none reaches
this item in either dependency graph.

Compared the retained returned packet with the current shared main node: only
`lean` and the authorized additions to `stmt_deps` differ. The returned module is
not on current main, so its retained sandbox source is the repair baseline. The
delivery wrapper assembles this repair on current main. There is no mathematical
statement change.

Repair validation: the prescribed deliver2.py --no-push dry run succeeded on
resumption: `OK (dry run): commit a31382dcacc passes the preflight and compiles;
nothing pushed`. The repaired module compiled without warnings under the tool's
per-file limit. Its theorem signature still matches the node record verbatim.

Earlier attempts encountered upstream error 28 (no space left on device) and
cached copies of that tool failure; an initial server confirmation also exceeded
the file limit under those conditions. The successful clean dry run supersedes
those failures. Temporary profiling options were removed before validation.
No launcher script, compiler cache, shared-library source or runtime limit was
modified. H2 and the advisory ownership citations are repaired and validated.
