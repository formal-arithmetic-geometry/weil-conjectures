## Worker report

The module `Sheaf.Paper.IntegralConstructibleCompletionBridge` states
`AlgebraicGeometry.ProEtale.integralConstructibleCompletionBridge`. Its sole theorem
has proof `sorry`. The node's statement, dependencies, proof and all other base fields
are unchanged; only `lean` is set. No definitions, dependency repairs or new nodes
are needed.

Source read: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.5.1,
Proposition 6.6.11, Definition 6.8.10 and Proposition 6.8.11(3), in the local PDF
(using pdftotext). Proposition 6.8.11(3) compares the completed category with bounded
cohomological scalar-model constructibility; the general-ring-object implication
uses the additional resolution argument in the DAG, rather than attributing that
extra assertion to the paper. I read all seven proof steps of this node. Their
argument is included step by step in the theorem docstring.

Hypotheses and clauses, in order:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The fixed algebraic closure is the existing
  `PadicAlgCl l`; `E : PadicAlgCl.FiniteIntermediateField l` is precisely a finite
  intermediate field in it. Its field, Q_l-algebra and finite-dimensional structures
  are the existing instances. The uniformizer `_π : PadicAlgCl.integers l E` and
  `_hπ : Ideal.span {_π} = IsLocalRing.maximalIdeal ...` explicitly retain the chosen
  generator. The construction used downstream chooses its own generator of the same
  maximal ideal, so powers of the two principal ideals and their quotients agree.
  There is no additional assumption about the choice of generator.
- `(Z : Scheme.{u}) [IsNoetherian Z]` is exactly compactness plus local
  Noetherianity: Mathlib's class extends `CompactSpace Z` and `IsLocallyNoetherian Z`.
  It is equivalent to a finite affine cover with Noetherian section rings, not a
  separation assumption. `_hdim : ∃ n : ℕ, topologicalKrullDim Z ≤ n` gives a finite
  bound on chains of nonempty irreducible closed subsets and includes the empty
  scheme, whose dimension is bottom. `_hinv : IsUnit (l : Γ(Z, ⊤))` says that ell is
  a unit everywhere: a global section is invertible exactly when its germs are.
- `ULift.{u} E.val` is just the finite field's canonical ring/algebra lift. It puts
  the coefficient carrier in the universe required by the recorded detailed
  integral interface. It neither restricts the scheme universe nor changes the
  small site's object universe u+1 and morphism universe u. The spectral extending
  absolute value is unique, hence agrees with the norm induced from the fixed
  algebraic closure. The recorded coefficient ring is its closed unit ball.
- B_Z is `AdicCompletion.ring l (ULift.{u} E.val) Z`, definitionally the pullback
  `condensedRingObj (DerivedNakayama.integerRing l (ULift.{u} E.val)) Z`.
  `DerivedNakayama.integerRing` is the underlying abelian ring object of the
  continuous-function ring sheaf of these integers. Thus this is the actual
  continuous condensed ring, not the discrete constant integer ring. The
  coefficient-limit identification is the existing projection-normalized one in
  `IntegralCriterionReductions`, based on the published integral-limit comparison;
  `CompletedCondensedCoefficients` supplies the same coefficient-limit convention
  for embedded fields. No new arbitrary isomorphism or completion map is chosen.
- The binder `K : DerivedCategory (AdicCompletion.Modules ... Z)` ranges over the
  entire ordinary unbounded derived category of internal B_Z-modules. There is no
  constructibility, boundedness, Tor-amplitude or completeness assumption on K.
- (i) is `boundedConstructible (AdicCompletion.ring ...) K`. This is the existing
  bounded t-structure predicate intersected with constructibility of every
  cohomology module. `IsConstructibleModuleObject` quantifies over finite scheme
  stratifications, with local finite presentations after pullback to each stratum.
  `IsLocallyFinitelyPresented` permits arbitrary finite matrices over the pulled-back
  ring, including torsion cokernels. On Noetherian schemes the locally closed
  strata are constructible subsets automatically.
- (ii) is `WeilConjectures.sfIntegralConstructible ...
  ((integralSectionDerivedEquivalence ...).functor.obj K)`. This uses exactly the
  recorded declaration of `def-weil-derived-complete-integral-detailed`.
  Unfolding it gives `IsSfDerivedComplete` and one existential interval a <= b
  containing the cohomological support of every positive derived quotient.
  `IsSfDerivedComplete` uses the canonical units and transitions in the Roos
  triangle; it is not existence of an arbitrary limit isomorphism. Each reduction
  satisfies `intrinsicFiniteTorsionConstructible`, i.e. classical constructible
  finite cohomology via the recorded finite-coefficient comparison. The recorded
  detailed-category and stratified-perfect comparisons identify this predicate
  with compatible etale-origin representatives; compatibility is with the fixed
  quotient transitions. The existing `integralSectionDerivedEquivalence` is the
  localization of the actual section-action functor followed by restriction along
  the uniquely projection-normalized coefficient isomorphism. It sends this very
  K to its other presentation and does not replace K by a completion. I read its
  definition, `integralSectionRingIso_existsUnique`, and the proof docstring of
  `continuousIntegralConstructible_iff_sfIntegralConstructible`, which explicitly
  compares the reduction units, transitions, finite constructibility and common
  interval. I also read `integralStratifiedPerfectDetailed` and its compatibility
  explanation.
- (iii) is `constantModelBoundedConstructible (DerivedNakayama.integerRing ...) Z K`.
  Its boundedness is the same ordinary t-structure predicate. Its cohomology
  modules satisfy `IsConstantModelConstructible`; the qcqs branch is a finite
  constructible locally closed stratification followed by pro-etale covers and
  `HasFiniteConstantLocalModel`. A finite presentation is chosen on the point
  before pullback. Its matrix entries are the scalar A, so its cokernel is exactly
  B_V tensor_A P for a finitely presented A-module P. This allows torsion and zero.
  No single stratification is shared with (i), or imposed across infinitely many
  degrees. Only finitely many degrees are relevant, and the existing finite
  refinement theorem supplies a common finite refinement when desired.
- The conclusion is `(i ↔ ii) ∧ (i ↔ iii)`, exactly equivalence of the three
  conditions. It contains no extra category equivalence, completeness hypothesis,
  clause restricting torsion, or claim about arbitrary coefficient sections.

Recorded dependencies used (module and declarations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with imported
  `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`,
  `coefficientExtensionRing` and `coefficientExtensionTransition`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and the
  imported continuous coefficient constructions. The actual concrete coefficient
  ring comes from the existing DerivedNakayama interface.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, and `upperStarFromPoint`. Imported through the recorded
  coefficient/comparison modules; no copy of the pullback is introduced.
- `Sheaf.Paper.CompletedCondensedCoefficients`:
  `AlgebraicGeometry.ProEtale.completedCondensedIntegral`, including its normalized
  quotient projections and constant finite coefficient comparisons.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  derived-category convention, using Mathlib's `DerivedCategory` for our ambient
  category, not a new localization.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`: its publicly
  retained general `AlgebraicGeometry.ProEtale.boundedConstructible` is the needed
  interface. The discrete constant-coefficient specialization is not used.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`,
  publicly imported by `IntegralCriterionReductions`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `IsConstantModelConstructible`,
  `IsFiniteConstantStratified` and `HasFiniteConstantLocalModel`.
- Mathlib `Topology.Defs.Filter.CompactSpace`,
  `AlgebraicGeometry.Noetherian.IsLocallyNoetherian` / `IsNoetherian`, and
  `Topology.KrullDimension.topologicalKrullDim`.

All already stated proof dependency modules are imported, non-public when used only
by the planned proof. For the Mathlib leaves these include
`CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished` in
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle` and
`TopologicalSpace.NoetherianSpace.isCompact` in `Mathlib.Topology.NoetherianSpace`;
the two Noetherian scheme leaves are already exported by `Mathlib.AlgebraicGeometry.Noetherian`.
The existing `IntegralCriterionReductions` comparison is reused without a new helper.

Edge cases checked before writing: the empty scheme is included by the dimension
inequality and has trivial module category; K = 0 satisfies all three conditions;
positive quotient index zero means exponent one, never the degenerate zeroth power;
A/pi^r in degree zero is permitted and has derived reduction amplitude [-1,0];
finite free A-modules are allowed without being torsion; unbounded K is a legal
input but does not automatically satisfy (i) or (iii). No perfectness of the
reductions over A/pi^n is imposed: that would incorrectly exclude torsion.
The two constructibility predicates quantify independently over their strata.

Searches actually run via msearch.py, group NV and this item (saved in searches.jsonl):

- LeanFinder: `equivalence bounded constructible integral completed category over
  pro etale ring object`. Eight hits, including BDeRhamPlus and generic condensed
  or pro-etale definitions; no matching comparison.
- Loogle: `Equiv _ _ boundedConstructible sfIntegralConstructible` returned no hits
  and an ill-formed-query diagnostic. This was not counted as a mathematical no-match.
  Corrected query `"boundedConstructible", "complete"` returned zero hits.
- LeanSearch: `Bounded constructible complexes of integral pro etale sheaves are
  derived complete`. Eight hits for scalar completion, DerivedCategory, and generic
  boundedness; none states this pro-etale integral comparison.
- Mathlib grep: `(constructible|Constructible).*(complete|Complete)|(complete|Complete).*(constructible|Constructible)`.
  Zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id found no declaration.
  Searches for integral constructibility, boundedConstructible,
  constantModelBoundedConstructible and the proposed declaration name found the
  existing definitions and comparisons listed above. The nearest statements,
  `integral_models` and `integralStratifiedPerfectCharacterization`, do not match:
  the former has finite-type-over-field hypotheses and already uses scalar-model
  constructibility; the latter compares completed and scalar-model categories
  without this general-ring-object condition (i). Thus no existing declaration
  supplies the entire requested statement. No duplicate notion is defined here.

Compilation: scompile.py compiled the module in both sandbox and library placement
with no warnings or errors (8.1 s and 6.8 s). No local build or direct git mutation
was run. All binders and universe variables are explicit with `autoImplicit false`.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
