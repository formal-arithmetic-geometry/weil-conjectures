## Worker report

The module `Sheaf.Paper.IntegralLineReductionRestriction` states
`WeilConjectures.IntegralLineReduction.integral_line_reduction_restriction`.
Its only postponed proof is that named theorem. All supporting declarations have
real data or are predicates specifying the comparisons in this node. The theorem
docstring gives the ten-step natural-language proof from the DAG, with its source
and proof dependencies. No new mathematical notion or alternative tensor operation
is introduced: the short names specialize the published constructions.

### Hypotheses and coefficient conventions

- A prime is `(l : ℕ) [Fact l.Prime]`.
- The finite extension is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring, chosen uniformizer, finite
  quotients and completed constant ring are precisely the recorded coefficient
  constructions, not additional arbitrary ring data.
- `X : Scheme.{u}` and `_hl : ∀ x : X, Invertible (l : X.residueField x)` give
  the scheme and invertibility hypothesis. As in the recorded full integral
  category, the coefficient field and scheme share a sufficiently large universe;
  the small pro-etale site still has objects in `u+1` and morphisms in `u`.
- `L : scalarReductionSource l E X` is a module sheaf over the completed ring.
  `[L.IsFiniteLocallyFreeOfRank 1]` is the existing coverwise rank-one condition.
- `_hfinite : FiniteReductions l E X L` says, for every positive quotient,
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses` with the predicate
  `fun M ↦ Finite M`. The models can vary with the covering object, as in the node.
- Every natural index `n` denotes the positive exponent `n+1`; no zero quotient
  or implicit exclusion of the first quotient occurs.

### Each conclusion and its maps

- `power` is exactly `coefficientTwistLine`: exponent zero is the unit, positive
  exponents are the existing iterated sheaf tensors, negative exponents are the
  existing internal Hom of the positive power into the unit. `finitePower` uses
  the same declaration over the finite constant ring and `line`, the recorded
  ordinary scalar reduction of L.
- `PowerComparisons` quantifies `∀ m : ℤ, ∀ n : ℕ` the isomorphisms from ordinary
  reduction of `power L m` to `finitePower L n m`. `PowerFormula` specifies the
  zero-power scalar multiplication, the identity at exponent one, recursive
  balancing for all positive powers, and exactly the negative dual map
  `φ ⊗ a ↦ (x ⊗ c ↦ residue(φ(x)) * a * c)`.
- `DerivedComparisons` gives natural isomorphisms of functors on the entire
  unbounded derived category; no completeness or boundedness hypothesis is used.
  Its two sides are ordinary tensor followed by derived reduction, and derived
  reduction followed by finite ordinary derived tensor, respectively.
- `DerivedFormula` fixes these derived maps on every admissible flat-term K-flat
  representative. `ChainFormula` is the actual balancing formula on total tensor
  generators. The derived equality uses the actual `scalarReductionCounit` and
  the published normalized tensor representative isomorphisms; it does not
  permit arbitrary natural isomorphisms. K-flat conditions here select a way of
  computing the maps, rather than adding any hypothesis on the input K.
- `powerTransition` is the ordinary quotient transition transported through the
  fixed power comparisons. `TransitionFormula` applies the actual quotient map
  to each finite tensor factor. The final square in `DerivedFormula` commutes
  strictly on representatives, hence asserts quotient compatibility of the
  derived comparisons. The balancing/dual formulas identify the transported
  line transitions with the usual finite quotient transitions.
- `Evaluations` and `EvaluationFormula` specify the ordinary opposite-line
  evaluation isomorphisms: scalar multiplication at zero and the actual
  functional evaluation in either sign. Together with the formulas for the
  comparisons, this renders preservation of evaluation under reduction.
- For every derived-complete K, the next conjunct asserts both
  `IsIso ((comparison L m).app K)` and
  `IsComplete ... ((ordinary L m).obj K)`. Here `comparison` is literally the
  whiskering of `integralLineComparison`, the published completion unit with
  `(c,0)` normalization. `completed` is literally `integralLineCompleted`,
  using the prescribed quotient-tower completed tensor.
- `PreservesIntegral`, included in `Restrictions`, asserts membership of both
  ordinary and completed tensors for every K in the existing full category
  `sfIntegralConstructibleCategory`. Its defining predicate contains derived
  completeness, finite-torsion constructibility of every derived reduction and
  a common bounded cohomological-support interval. Thus the finite constructible
  cohomology clause is explicit through this recorded predicate.
- The support conjunct additionally quantifies arbitrary K and every pair of
  integers `a z`. If every reduction has `proEtaleCohomologicalSupport` in
  `Set.Icc a z`, then every twisted reduction has support in that very same
  `Set.Icc a z`. No widening, Tor-amplitude interpretation, or bound on the
  original unbounded complex is substituted.
- `DerivedEvaluationFormula` identifies both ordinary inverse evaluation maps
  with the original sheaf evaluation on representatives. `OrdinaryRestriction`
  gives an equivalence of the full integral category with underlying functors
  naturally identified with the ordinary tensors at m and -m; its unit inverse
  and counit are exactly those evaluation maps after inclusion.
- `Restrictions` fixes the full-category comparison isomorphisms `c` by
  requiring `c.hom` to equal the actual completion comparison. In
  `CompletedRestriction`, the two underlying functors are the prescribed
  completed tensors, and the unit inverse and counit are explicitly the
  ordinary evaluations conjugated by those very `c` inverses. An actual
  `Equivalence` supplies the triangle identities, not merely an isomorphism
  of objects.

### Recorded declarations used

The original statement dependencies are retained, and the following recorded
interfaces are used (including their reexported supporting declarations):

- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`,
  `completedIntegralCommRingSheafUnrestricted`, `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingProjectionUnrestricted`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  as used by the finite coefficient sheaf construction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the concrete module categories are the existing `SheafOfModules` categories.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its
  quotient functor `DerivedCategory.Q`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionExtension`,
  `scalarReductionRestriction`, `scalarReductionCounit`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor`, `Good`, `Cx`, `D`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the sheaf tensor construction.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, as used by `coefficientTwistLine`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its
  full category `sfIntegralConstructibleCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`:
  `Scheme.proEtaleCohomologicalSupport`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, via the integral predicate.

Four already-recorded owning nodes are added to `stmt_deps` to document reuse:

- `def-coefficient-twists-detailed`: `coefficientTwistLine` from
  `Sheaf.Paper.CoefficientTwistsDetailed` (reexported by its recorded module
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`).
- `def-sf-integral-line-tensor-comparison-constructors`:
  `Sheaf.Paper.IntegralLineTensorComparisonDefinitions`, declarations
  `integralLineSingle`, `integralLineOrdinary`, `integralLineCompleted`,
  `integralLineComparison`, `integralLineComplex`, `integralLineRepresentativeIso`.
- `def-weil-proetale-locally-constant-sheaf`:
  `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`, declaration
  `Scheme.IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses`.
- `def-coef-ringed-tensor-hom-model`:
  `Sheaf.Paper.CoefficientRingedTensorHomModel`, declarations
  `CoefficientTensorModels`, `CoefficientTensorModels.iso`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`.

The finite derived tensor uses the existing `RingedSiteDualityModel` specialized
to the finite quotient. Its closed adjunction and representative normalization
determine its tensor up to the compatible canonical isomorphism. This is a
specialization of the existing universal construction, not the choice of an
arbitrary map or an unspecified tensor. The derivation counit is transported
from homotopy complexes using the existing quotient isomorphisms.

All available recorded proof-dependency modules are imported for stage 3.
The unrecorded line-tensor theorem and dual-tensor adjunction theorem are cited
in the natural-language proof; they are proof dependencies, not missing notions
needed to type this statement.

### Edge cases and source review

Checked m=0, m=1, m=-1 and all other negative exponents. The unit, identity and
dual formulas include these cases explicitly. Checked the first quotient n=1
(index zero), K=0, the empty scheme, and unbounded K. The support clause permits
any common interval with its original endpoints; an empty interval is not
silently excluded. The local finite-model hypothesis is coverwise, not a global
constant-model assumption. The full-subcategory restriction includes both
inverse orders and their actual maps.

Read the main-20261015 blueprint proof (3), final sentence, and Bhatt--Scholze
Definitions 3.4.10/3.5.2, Lemma 3.4.12 and Proposition 3.5.1. The node statement is
retained verbatim; no statement fault or STATEMENT-DISPUTED flag was found.

### Searches

- `msearch.py ... leanfinder` with query “Signed tensor powers of a locally free
  rank one sheaf commute with derived reduction and preserve derived complete
  constructible complexes”: eight unrelated hits (ordinary sheaf free maps and
  LightCondensed monoidal module results); no exact match.
- `msearch.py ... loogle` with query
  `SheafOfModules.homObj, IsLocallyFree, tensorRight`: zero hits; the search index
  did not recognize `SheafOfModules.homObj`.
- `msearch.py ... grep` with query
  `signedPower|signedTensor|integralLine|IsLocallyFree`: eleven hits, primarily
  Mathlib locally free module declarations; no theorem for this whole node.
- `rg` in the project's `WeilConjectures/` and `Sheaf/` for signed powers,
  coefficient twists, integral lines, tensor reduction and completeness found
  the generic `coefficientTwistLine`, the existing integral line comparison
  constructors, and specialized Tate-twist results. These generic definitions
  are reused. No already-declared theorem matches this generic signed-line node.
- Searching the item's ID in `lean/WeilConjectures` found no existing declaration.
- The existing DAG records and their source signatures/docstrings were read for
  all twelve original statement dependencies and the added owning nodes.
  A reachability check found no cycle from the added statement dependencies.

## New nodes

None. All basic notions already have recorded declarations. The auxiliary
predicates simply expose the formulas and coherence clauses of this node.

## Dependency modules

None. No existing dependency record needed a Lean-only repair.

### Validation

The prescribed `scompile.py NR lem-pur-integral-line-reduction-restriction`
compiled the final file both as a sandbox module and under its final module name:
25.6 seconds and 25.4 seconds, respectively, with no errors or warnings.
The small-site instances in the K-flat predicates have explicit universes.
The overly polymorphic imported `IntegralOnSlice.abLocallyBijective` instance
is disabled in this module; the standard generic sheafification instance is
used instead. This affects elaboration only and adds no mathematical hypothesis.
The file binds its universe explicitly, sets `autoImplicit false`, and contains
only the main theorem's single `sorry`.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
