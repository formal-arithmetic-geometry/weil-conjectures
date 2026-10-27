## Worker report

The module states `WeilConjectures.CompletedQuotient.completedComparisonQuotientRealization`.
Its proof is `sorry`. Helper definitions contain actual maps or predicates, never postponed data.
The only other postponed theorem, `sequencePullback_eq`, identifies the two published names of
one sectionwise geometric inverse image. Its docstring gives its source and proof.
It belongs to this node's comparison normalization; it is not a replacement pullback.

The node statement is unchanged. Return F1 is repaired by five existing:true definition
ownership nodes and the already landed def-pur-completed-operation-comparison-data.
The proof dependency list is exactly the union of the ten declarations used by the
proof steps below. The four former theorem-node names that now have definition-owner
records are statement dependencies only; no proof step uses them, so they are not
listed as proof dependencies. No source definition is duplicated.

Clause-by-clause reading:

- Prime and coefficients: `(l : ℕ) [Fact l.Prime]`, finite-dimensional field algebras
  `E,L` over `ℚ_[l]`, and `ι : E →ₐ[ℚ_[l]] L`. These implement the embedded finite
  extension by its inclusion, as the coefficient dependency does. Valuation rings,
  uniformizers, positive quotients and maps are the dependency's existing canonical ones.
- Schemes and composability: `h : Z ⟶ X`, `f : X ⟶ Y`; the three residue-field
  `Invertible` instances express invertibility of l. Empty schemes are allowed.
- Coefficients and limits: `scalarReductionSource`, `coefficientSequenceModules`,
  `pullbackTensorCalculus.reduction` and `coefficientSequenceLimit`. These use the
  small pro-etale site, whose object universe is u+1 and morphism universe u, not an
  equality between these two sizes. Fields and schemes use the common ambient u of
  the recorded canonical comparison, which can be chosen large enough for the data.
- M,N,H: `M : Fin 3 → sfIntegralConstructibleCategory l E Y` at indices 0,1,2.
  Its property is exactly complete, constructible finite reductions and one bounded
  cohomological interval. No finite-field or smoothness hypotheses are introduced.
- Every representative: `P : Fin 3 → (integralOperationsGoodComplex ...).FullSubcategory`
  and `φ : ∀ i, Q(P i) ≅ M i`. The good subcategory means K-flat with flat terms.
  Complexes are integer indexed and need not themselves be bounded.
- Actual quotient models and transitions: `quotient` is the ordinary reduction
  left adjoint lifted to complexes. `CoefficientReductionPresentation` fixes its
  exact finite quotient identifications, actual transitions and derived localization.
  This is an actual construction, not an existential replacement of P,Q,J.
- All finite well-typed expressions: reuse `StrictQuotient.Expression` and translate
  constructor for constructor to the shared expression syntax. `strictValue` uses
  the published strict tensor and pullback functors. `GoodExpressions` and the first
  conclusion assert system K-flatness, flat terms, every finite-level Good and
  `IsNormalizedCoefficientSequence`, including units, repeated inputs and composites.
- Same completed expression: `value` evaluates precisely `integralCompletedTensor`
  and `integralDerivedPullback`. `substitution` recursively uses the specified primitive
  tensor/pullback realizations and actual reconstruction unit. Its isomorphism
  assertion is a conclusion, not a hypothesis. `NaturalSubstitution` states its
  naturality for representative chain maps and arbitrary compatible derived inputs.
- T,U,V,W and strict c: `sourceExpression` is pull(tensor(input0,input1));
  `targetExpression` is tensor(pull(input0),pull(input1)). `comparison` is exactly
  `pullbackTensorSequenceCochain`, transported only along `sequencePullback_eq`.
  That recorded comparison is fixed by s tensor (x tensor y) mapping to
  (s tensor x) tensor (1 tensor y); its inverse multiplies the two scalars.
  These are isomorphisms of sequence complexes, so include every quotient transition.
- Both canonical completed maps: the two `transport = canonicalIntegralPullbackTensor`
  clauses identify the hom and inverse, respectively. `transport` is the explicit
  beta_source >> L(Q(c)) >> beta_target inverse, with both betas fixed recursively.
  `NaturalComparison` quantifies arbitrary ambient derived Hom sets, not only maps
  with chosen representative lifts. Since P and φ are universal, both equalities
  also assert independence of simultaneous representatives.
- Whole-system counit equation: `reduction β := R.map β >> counit.app _`. It is
  invertible for every expression. The all-v transport clause is exactly
  `R(transport v) >> r_B = r_A >> Q(v)` in `coefficientSequenceDerived`, hence includes
  the displayed gamma equation and every coherent finite reduction. Equality is not
  deduced from separate evaluations or cohomology groups.
- Coherence: `StrictCoherence` supplies the strong monoidal data with its generator
  normalization, the signed cochain braiding law, the adjunction-normalized composition
  law, and equalities identifying each tensor component with this very `comparison`
  for f,h,h>>f. `CoreMonoidal` includes reassociation and both action-unit laws.
  The StructuralMap clause supplies the unique completed constraint with its limit
  square and its whole-system reduction square, for associators, signed symmetries,
  unitors, composition and their inverses/contexts. Applying the functor L and
  cancelling adjacent beta inverses sends the strict commuting diagrams to the
  completed commuting diagrams; the preceding all-v equation supplies reductions.
- Scalar quotient expressions: `ScalarGenerated` is the least two-row closure under
  actual coefficient extension, units, tensors and the three allowed pullbacks.
  `ScalarGood` asserts system and finite K-flatness with flat terms and normalization
  in the appropriate coefficient row, so also covers mixed expressions.
- Balanced quotient association: `ScalarAssociation` retains direct quotient models,
  balanced local section formula and actual transitions. It uses the existing
  `CoefficientExtensionReductionData`, without assuming finite quotient-map flatness.
- Scalar realization: `scalarSubstitution` is the normalized scalar realization,
  followed by scalar image of this item's coherent reduction and the actual K-flat
  localization counit. `scalarBeta` applies `substituteInputs` at L to these leaves.
  `scalarTransport` conjugates the strict L comparison by these recursive maps.
- Scalar limit-image link (return F2): `ScalarLimitImage` existentially supplies
  normalized scalar models at X,Y, whole-system goodness of the scalar quotient
  expressions and invertibility of `scalarBeta`. It equates the L transport of this
  item's `comparison` with `canonicalIntegralPullbackTensor` at scalar-extended inputs.
  For each of this item's `scalarLeft` and `scalarRight` routes, it states that the
  image by Q then total limit, conjugated by `scalarSubstitution` of the E source
  beta and the inverse L target beta, equals BOTH completed composites: alpha_F,
  pullback of alpha_T, gamma_L; and scalar image of this item's E transport,
  alpha_T, tensor of the two alpha_F. Thus this is a relation on this item's maps,
  not an imported scalar theorem or a copied type_of% assertion.
- Strict scalar routes: `scalarLeft` uses kappa, pullback of sigma and this item's
  `comparison` at L; `scalarRight` uses scalar image of this item's E `comparison`,
  sigma and the tensor of kappa. Their equality as chain isomorphisms includes the
  inverse and all transitions. The normalized primitive maps fix the two tensor
  generator formulas. Identity and successive extensions retain actual scalar
  unitors and scalar associators (`ScalarIdentity`, `ScalarComposition`).
- The redundant `ScalarRealization` / `RealizesScalar` restatement was removed.
  The new normalized `scalarSubstitution` and `ScalarLimitImage` supply the actual
  quotient/limit link; model existence is a conclusion, not a main-theorem hypothesis.

Dependency declarations read and reused (their publicly reexported helper declarations
are used where the main recorded theorem is not itself an object constructor):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `None`, `None`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`.
- `def-weil-integral-reduction-tower`: `Sheaf.Paper.IntegralReductionTowerCanonical`, `WeilConjectures.canonicalIntegralReductionTower`.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`, `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `def-pur-integral-derived-operations`: `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, `WeilConjectures.IntegralOnSlice.completedTensor`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `lem-pur-cochain-pullback-tensor-coherence`: `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`, `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`.
- `def-pur-completed-pullback-tensor-comparison`: `Sheaf.Paper.CompletedPullbackTensorComparison`, `WeilConjectures.canonicalIntegralPullbackTensor`.
- `def-weil-integral-scalar-extension`: `Sheaf.Paper.IntegralScalarExtensionUniverses`, `WeilConjectures.integralScalarExtensionOfUniverses`.
- `lem-pur-integral-operations-scalar-extension`: `Sheaf.Paper.IntegralOperationsScalarComparisons`, `WeilConjectures.scalarOperationsOrdinary_tower`.
- `lem-pur-quotient-expression-strict-kflat-towers`: `Sheaf.Paper.QuotientExpressionStrictKFlatTowers`, `WeilConjectures.StrictQuotient.quotientExpressionStrictKFlatTowers`.
- `def-pur-strict-quotient-expressions`: `Sheaf.Paper.StrictQuotientExpressions`, `WeilConjectures.StrictQuotient.Generated`.
- `lem-pur-completed-operation-tower-substitution`: `Sheaf.Paper.CompletedOperationTowerSubstitution`, `WeilConjectures.CompletedOperations.completedOperationTowerSubstitution`.
- `lem-pur-integral-coherence-tower`: `Sheaf.Paper.IntegralCoherenceTower`, `WeilConjectures.IntegralCoherence.integralCoherenceTower`.
- `lem-pur-scalar-extension-tower-coherence`: `Sheaf.Paper.ScalarExtensionTowerCoherence`, `WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence`.
- `lem-pur-coefficient-extension-reduction-model`: `Sheaf.Paper.CoefficientExtensionReductionModel`, `WeilConjectures.coefficientExtensionReductionModel`.

Proof-only dependencies are imported for the documented proof plan. The recorded
`Sheaf.Paper.NormalizedScalarComparisonRealization` source is unavailable both in
this checkout and through `scompile.py --source`; no statement type uses it.
The landed scalar-coherence and coefficient-reduction interfaces supply every
scalar notion needed here. Its absence does not change the DAG proof plan.

Searches performed before writing:

- msearch.py leanfinder, query `Simultaneous quotient realization of completed derived
  pullback tensor comparison diagrams and scalar extension`: eight unrelated hits,
  including AdicCompletion and Kaehler differential tensor naturality; no exact result.
- msearch.py loogle, query `Functor.mapIso, Adjunction.counit_naturality`: zero hits;
  the service reported unknown identifier Functor.mapIso (recorded as a failed query,
  not evidence that those generic operations do not exist).
- msearch.py grep, query `completed.*[Cc]omparison|[Cc]omparison.*[Qq]uotient`,
  Mathlib CategoryTheory: zero hits.
- rg/grep in lean/WeilConjectures and lean/Sheaf for the item id and
  `completedComparisonQuotient|CompletedComparisonQuotient`: no existing statement.
  Broader pullback, quotient, scalar and coherence searches found the interfaces
  imported here. No private duplicate of their coefficient systems or K-flat notions
  is introduced; the supplementary identity/composition and quotient-model predicate adapters use the
  exact existing theorem types. The missing own-map relation is stated independently
  by ScalarLimitImage.

Edge cases checked: zero representatives, repeated inputs, unit-only expressions,
integer-unbounded flat-term K-flat representatives, identity scheme maps and identity
coefficient inclusion, arbitrary successive extensions, empty schemes, and ramified
extensions with nonflat finite quotient maps. Every expression retains syntax and
parentheses. Strict maps and counit equations are on entire sequence objects.
No mathematical statement correction or disputed clause was found.
The current blueprint was read under literature/blueprint/latest/blueprint at
sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/
def-weil-derived-pullback-tensor-hom.md; the node's older source path has moved there.
The node is its representative refinement, not a verbatim blueprint unit.

## Second reading by Q128

This is a second worker pass over the JSON and module, not an independent reviewer;
the dispatched brief assigns independent review to the maintainer and prohibits
starting other agents. The clause mapping above was checked again against both files.
The pass found and repaired three potential omissions: it added both inverse and hom
identification, naturality of all expression substitutions, and explicit identity/
successive scalar equations. The structural clause retains the coherent counit square,
not just a noncanonical existence of vertex isomorphisms. Supplementary primitive-law adapters preserve the exact existing theorem types.
The missing own-map relation is now explicitly ScalarLimitImage and cannot be supplied
merely by those primitive-law adapters. The line-length warning was repaired.
All theorem proofs remain sorry; definitions are actual data, recursive maps or predicates.

Validation: scompile.py is used for every probe and delivered module. Final clean
compile and the prescribed deliver2.py dry-run results are recorded by the wrapper.

## New nodes

All five records are existing:true owners, with no copied Lean module. The logged
LeanSearch, LeanFinder and Mathlib grep searches are retained verbatim in each record.
DAG ownership searches found the notions only under theorem interfaces, and source
searches located the exact declarations in the modules listed here.

- `def-pur-strict-quotient-expression-data`: finite Expression syntax, its interpretation
  and SystemGood in Sheaf.Paper.QuotientExpressionStrictKFlatTowers. Source: strict
  finite-expression paragraph, Stacks 07A2/0G7E/0941.
- `def-pur-integral-coherence-data`: IntegralCoherence strict interpretation, normalized
  monoidal comparison data, signed symmetry and composition predicates in
  Sheaf.Paper.IntegralCoherenceTower. Source: strict coherence paragraph, Stacks 07A4.
- `def-pur-coefficient-reduction-presentation`: CoefficientReductionPresentation in
  Sheaf.Paper.CoefDerivedSystemEvaluationCalculus. Source: simultaneous normalized
  quotient models, Stacks 0941. This is the two evaluation/transition equations.
- `def-pur-coefficient-extension-reduction-data`: CoefficientExtensionSystems and
  normalized direct quotient/reduction model data in
  Sheaf.Paper.CoefficientExtensionReductionData. Source: scalar quotient paragraph.
- `def-pur-scalar-extension-tower-data`: ScalarExtensionTower scalar, pull, tensor,
  kappa, scalar unit/composition, normalized Comparisons, strict routes, TensorModel
  and its reduction normalizations in Sheaf.Paper.ScalarExtensionTowerCoherence.
  Source: scalar-association and normalized-limit paragraphs, Stacks 03EL/07A4/0941.

## Returned delivery repair

F1: the former theorem dependencies supply no theorem-constructed objects needed
by this signature. Their definitions now have the five ownership records above, and
CompletedOperations structural data uses the existing landed definition node.
Only declarations actually used by a proof step remain in `proof_deps`; the four
unused former theorem names are statement dependencies with their own definitions.
The item’s prose is unchanged.

F2: removed the standalone canonical scalar condition and copies of the landed
strict square from the theorem. Added own scalarSubstitution, scalarBeta,
scalarTransport, scalarLeft, scalarRight and ScalarLimitImage. The two limit-image
equalities explicitly involve this item’s E transport and recursively fixed L beta.
Both completed gamma/alpha routes are equated with the same strict-route image.
This supplies the missing relation even though the primitive identity/composition
and normalized quotient-model facts are available in dependencies.

The repair is substantively different from returned sha e4da1948: the scalar
limit-image predicate and its actual maps occur in the main theorem, and new
ownership records replace the five theorem statement dependencies. The report and
lean.statement are refreshed to the repaired source, not merely rebased.

## Repair self-check by Q128

Read the node and repaired module together. All original non-scalar clauses remain:
quotient, substitution, hom and inverse normalization, whole-system counit equation,
structural limit/reduction square and both naturality predicates. The new
ScalarLimitImage is not type_of% of a dependency: it explicitly conjugates Q(v)
under the total-limit functor by scalarSubstitution of this item’s E source beta and
the inverse of its recursively defined scalarBeta at L. The two right-hand sides
use respectively its scalarTransport of c_L and its original E transport of c_E,
followed by the named canonical alpha comparisons. Its separate L transport clause
identifies gamma_L. Strict route equality as Iso also identifies inverses. The
scalar models are conclusions, not added assumptions. Identity and successive
extension predicates keep the exact dependency types as supplementary facts;
they do not replace this new limit-image relation. All actual scalar quotients
still derive from P, with no new representative choices and no quotient flatness.

F1 ownership was checked against each recorded signature. The five new nodes record
existing data and predicates, while the already landed completed-operation data
node owns StructuralMap. The proof plan uses exactly the ten declarations listed in
`proof_deps`; the four definition-owner modules are available through `stmt_deps`
and are not unused proof dependencies.
No direct edit or git mutation was performed in the shared repository. Temporary
compiler probes were removed from the delivery sandbox before final validation.

Compilation repair: coefficient units use Mathlib's explicit
HomologicalComplex.tensorUnit and the canonical sheaf/cochain monoidal instances
are prioritized to avoid repeated broad typeclass search. No timeout limit was
raised. All diagnostic commands and probe modules were removed. The main module
has two postponed named theorems, sequencePullback_eq and the main realization;
all constructions and predicates have actual data. Final validation is the
prescribed single-file server compile and deliver2.py preflight, followed by push.

## Statement corrected

No mathematical statement was corrected: the item's `statement` remains byte for
byte the base statement. The returned review identified a metadata fault: four names
were present in `proof_deps` without appearing in any proof step `uses` list. They
have been removed from `proof_deps`, which now equals that uses union exactly; they
remain available as statement dependencies through their definition-owner records.
A `statement_change` claiming a mathematical correction would be inaccurate, so none
is fabricated.
The following is the full citer audit requested by that diagnostic:

- `lem-pur-derived-pullback-tensor-iso`: holds true. Its integral representative
  realization, counit, strict coherence and mixed scalar-square uses remain exactly
  the same; ScalarLimitImage supplies the previously missing link to those maps.
- `lem-tw-lisse-scalar-comparison-coherence`: holds true. Its uses in simultaneous
  completed expression diagrams and tensor/pullback/scalar compatibility are
  preserved, with the actual quotient-limit scalar square now explicitly stated.

Preflight shape repairs add the now-required import_flags: [] to each new node,
copy the full CoefficientReductionPresentation signature through its outer :=
(previously a named argument := had truncated it), and separate the two K-flat/flat
notion citations into individual bracketed node references. These are record
repairs and change no mathematical meaning or Lean source.
