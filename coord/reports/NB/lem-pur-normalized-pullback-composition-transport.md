## Worker report

The module Sheaf.Paper.NormalizedPullbackCompositionTransport states
WeilConjectures.PullbackCompositionTransport.normalizedPullbackCompositionTransport.
Its proof is sorry, as required for stage 2. The only other postponed theorem is
the dependency's coefficientModulePullbackComposition_existsUnique. Definitions
contain actual functor, adjunction-mate, localization, cone, and composition data.

Hypotheses and clauses, matched against the node:

- The fixed prime and finite coefficient extension are l, [Fact l.Prime], E,
  [Field E], [Algebra ℚ_[l] E], [FiniteDimensional ℚ_[l] E]. Coefficient rings,
  their uniformizer and quotients are Padic.coefficientExtensionRing. Index n
  means exponent n+1, so exponent one is included. E : Type u and schemes in
  Scheme.{t} have independent universes. The small site remains object universe
  t+1 and morphism universe t.
- X, Y, Z, h : Z ⟶ X, f : X ⟶ Y render the composable scheme maps. _hX, _hY,
  _hZ assert that l is a unit in every structure-sheaf stalk, the assertion that
  l is invertible on each scheme. There are no smoothness, flatness, finiteness,
  boundedness, constructibility or Tor-amplitude restrictions.
- coefficientSequenceModules and coefficientSequenceDerived are the recorded
  actual strict semilinear systems and their ordinary unbounded derived category.
  All operations below occur there before applying coefficientSequenceLimit.
- C is an arbitrary object of coefficientSequenceDerived l E Y; _hC is precisely
  IsNormalizedCoefficientSequence l E Y C, not a chosen reduction tower.
  coefficientSequenceDerivedTransition is its actual transition. SZ's
  quotientCalculus defines coefficientSequenceTransitionAdjoint by transposing
  that transition through the canonical derived quotient adjunction. Thus it
  includes tau = Res(alpha) after eta; no canonical-unit transition is assumed.
- The whole-system compositor is the already recorded
  integralComparisonSystemComposition l E h f. It is the localization of
  integralComparisonSequenceComposition, whose unique characterization is the
  mate of the specified fibre-product-pasting direct image on sections. It is
  definitionally a compositor of PrimitiveCounit.pull, as checked by compilation.
- finiteComposition uses the finite constant ring ULift
  (Padic.coefficientExtensionRing l E (n+1)), the dependency's unique normalized
  ordinary compositor, and exact termwise localization. evaluation is derived
  from PrimitiveCounit.inverseEvaluation, uniquely fixed by its unit equation.
  SystemLaws.finite identifies evaluation of the whole compositor with this
  finite adjunction-normalized map. The inverse identification follows by
  inversion of this equation of isomorphisms; no unrelated finite iso is chosen.
- SystemLaws.transition and inverse_transition state every actual restriction
  transition square in both directions, for all q : n ≤ m. adjoint_transition
  and inverse_adjoint_transition give the corresponding extension-form squares
  for the actual transition adjuncts. The input need only be normalized.
- SY, SX, SZ provide the dependency's canonical reduction/total-limit adjunctions,
  with their K-flat quotient models, unit/counit projection normalizations and
  finite quotient calculus. They are presentations of the recorded operations.
- rf, rh, rhf are the primitive quotient-limit realization isomorphisms for f,
  h, h≫f. ρX, ρZ are PrimitiveCounit.RoosRealization, with their natural
  projection equations and K-injective resolution normalization. _hf, _hh,
  _hhf are the dependency's PullModel normalization on the actual quotient
  complexes, including the unit-normalized finite component maps. They express
  use of the specified actual quotient-model presentations, rather than adding
  an independent mathematical condition on C.
- betaSource is beta_P for P=F_(f h)(input C), namely pullBeta for h≫f.
  betaTarget is beta_Q for Q=F_h(F_f(input C)), namely completed h applied to
  beta_f followed by beta_h at F_f C. These are exactly the node's recursive
  formulas specialized to its two expressions. Inputs have identity comparison;
  this specialization requires no extra evaluator or duplicate tensor notion.
  The four IsIso hypotheses are exactly the supposed invertibility of beta_P,
  beta_Q, gamma_P, gamma_Q. No invertibility of arbitrary unrelated maps is assumed.
- gammaSource and gammaTarget are SZ.reduction.map beta followed by the SAME
  whole-system SZ.adjunction.counit. These render gamma=e R(beta) verbatim.
- completed is an isomorphism built as beta_P, then L(a), then beta_Q inverse.
  Its inverse is consequently beta_Q, L(a inverse), beta_P inverse, in Lean's
  left-to-right composition order. Both inverse equations are part of Iso.
- TransportLaws.reduction is R(completed.hom) ≫ gamma_Q = gamma_P ≫ a.
  inverse_reduction gives the inverse square. Both are whole-system equations.
  naturality asserts completed naturality for every morphism C→C' between
  normalized inputs with the same four invertibility conditions at C'. The
  whole-system compositor is already a natural isomorphism; the inverse and
  reduction squares inherit naturality by inversion and functoriality.
- strictComposition is the actual strict-complex compositor restricted to
  completed-coefficient towers. restrictionFactor and iteratedRestrictionFactor
  are the exact localization comparisons, preserving parentheses.
  RepresentativeLaws.forward and backward identify L(a) and L(a inverse) with
  the existing roosF.map of the strict compositor and its inverse. roosF maps
  use the product map on BOTH shifted cone coordinates (StrictRoosModel), and
  are normalized by ρZ.comparison. These equations cover every strict complex
  representing a normalized C, not just an initially chosen reduction tower.
  The PullModel hypotheses identify the actual quotient representatives with
  these restrictions. Thus the result keeps actual quotient transitions and
  actual completed models; it assumes no inverse-image/product interchange.

Dependency declarations read and used:

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and the imported coefficient constructions.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses:
  integralConstantToCompletionOfUniverses and the actual completed ring/projections.
- Sheaf.Paper.SemilinearDerivedSections: SemilinearSections.semilinearDerivedSections;
  its vertical sequence-site interpretation, exact operations and mate calculus.
- Sheaf.Paper.NormalizedDVRTower: NormalizedDVRTower, normalizedDVRRes and
  normalizedDVRQuotient; the equivalent whole-system normalization is the recorded
  IsNormalizedCoefficientSequence of the coefficient calculus.
- Sheaf.Paper.IntegralReductionTowerCanonical: canonicalIntegralReductionTower and
  its strict quotient model, used through the recorded reduction presentation.
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus:
  CoefficientDerivedSystemReduction, CoefficientDerivedSystemCalculus,
  coefficientSequenceTransitionAdjoint, coefficientFiniteQuotientDerived.
- Sheaf.Paper.CompletedPrimitiveCounitComparison: PrimitiveCounit.pull,
  inverseEvaluation, pullBeta, PullModel, RoosRealization and Comparisons.
- Sheaf.Paper.IntegralDerivedOperationsOnSlices: the reexported actual
  integralDerivedPullback and its quotient/Roos model.
- Sheaf.Paper.IntegralComparisonSequenceSystems: integralComparisonSystemComposition,
  integralComparisonSequenceComposition and their exact strict-system pullbacks.
  This already landed definition node is added to stmt_deps because the consumer
  uses its canonical compositor directly; no new node is introduced.
- Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition:
  Scheme.proEtaleConstantRingModulePullbackComposition, retained by the dependency
  module, and its generalized independent-universe unique mate construction.
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact and
  Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact: the exactness interface
  for finite constant-coefficient module inverse image.
- Sheaf.Paper.CompletedOperationExpressions: CompletedOperations.Expression;
  P and Q are its two pullback expressions as described above.
- Sheaf.Paper.NormalizedDVREffectivity: normalizedDVRTower_effectivity;
  Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients:
  ringedStrictTowerHomotopyLimitIndependentCoefficients. They are proof imports,
  not new hypotheses in the consumer.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  CochainComplex.IsKFlatIndependentCoefficients;
  Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: SheafOfModules.IsFlatOnSite;
  Mathlib.Algebra.Homology.BifunctorShift: CochainComplex.mapBifunctor.
- Proof imports: Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence,
  Sheaf.Paper.IntegralOperationsWellDefined. The proof-only system-model node has
  no recorded declaration, and its conclusions are not used to define any object
  or assumed as a replacement input; the six-step docstring states the direct
  scalar/transition construction to prove this item independently of that node.

Edge cases checked: m=n is included by q : n≤m; n=0 means coefficient exponent
one; identity scheme maps and either identity in the composite are allowed.
Empty schemes make stalk conditions vacuous correctly; zero complexes and
arbitrary unbounded complexes remain allowed. All transitions are actual system
transitions. There is no finite-dimensional restriction on C and no assumption
that a quotient map is flat. No statement correction or disputed statement.

Searches (2026-10-21): msearch.py leansearch, query "Canonical composition of
derived pullbacks on normalized coefficient systems commutes with coefficient
quotient transitions and completed realization": 8 results, including Over.pullbackComp
and SheafOfModules.pullbackComp, none with system/completion realization transport.
msearch.py leanfinder, query "Canonical composition of derived pullbacks on
normalized coefficient systems and its transport through completed realization":
8 unrelated formal-series and adic-completion results. msearch.py loogle, query
"CategoryTheory.conjugateIsoEquiv, SheafOfModules.pullbackComp": 0 hits.
msearch.py grep, query "pullbackComp|conjugateIsoEquiv" in CategoryTheory:
25 hits including mates and ordinary over-category pullbacks. Direct rg in Mathlib,
WeilConjectures and Sheaf for normalizedPullbackCompositionTransport and
PullbackCompositionTransport: no existing transport declaration. Direct grep of
WeilConjectures for the item id: no match. Concept searches of Sheaf found
IntegralComparisonSequenceSystems and its unique whole-system compositor, reused
instead of reconstructing it. That existing definition says only the system
construction, not the present finite-evaluation and completed realization theorem.

Validation: every delivered module is compiled separately with scompile.py, in
sibling dependency order. Both compile without errors; final clean check and
required deliver2.py preflight are recorded by the delivery wrapper.

## Dependency modules

lem-pur-proetale-module-pullback-composition: the old declaration takes both
Scheme.{u} and Λ : Type u. The consumer's coefficient extension and schemes have
independent universes, hence cannot instantiate it without an extra universe
restriction. Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition publicly
retains the old module and states precisely the same constant-ring
pullback-composition characterization on coefficientProEtaleModulePullback with
independent t,r. The right-adjoint comparison is specified on every module section
by the canonical fibre-product pasting map; conjugateIsoEquiv fixes the unique
left-adjoint isomorphism. Its definition selects that uniquely determined object.
The dependency node is changed only in lean, with a note; statement and source
are untouched. Its earlier recorded declaration is retained in lean.declarations.
No new definition nodes are needed.

## Second reading by NB

The dispatcher requires a single worker and prohibits starting other agents;
independent review is performed by the maintainer after delivery. This section
records the worker's own second pass, not an invented independent reviewer.
I reread the item and both complete modules. The first elaboration exposed a
missing exactness instance for the actual finite functor spelling; I supplied
explicit existing instances inside the definition bodies. I checked that the
PrimitiveCounit and IntegralComparison whole-system inverse images are definitionally
the same (a direct compiled test), and used the existing compositor rather than
an arbitrary system isomorphism. I added both inverse transition-adjoint equations
and the two explicit Roos representative equations after checking the node's
inverse and actual-transition clauses. I restricted SystemLaws and representative
assertions to normalized input objects to match the node's stated domain. I checked
the direction of all ≫ words against the node's right-to-left mathematical formulas,
the four IsIso hypotheses, and that PullModel fixes all three realization maps.
