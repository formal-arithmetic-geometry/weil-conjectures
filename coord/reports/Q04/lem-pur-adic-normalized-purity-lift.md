## Worker report

`Sheaf.Paper.AdicNormalizedPurityLift` states
`WeilConjectures.AdicNormalizedPurity.normalized_purity_lift`, with ten explicit helper
composites. Its only postponed theorem is this node's theorem, with the seven-step proof
in its docstring. Every helper has real data and a source/blueprint docstring.

Hypothesis correspondence:

- Global finite field, prime different from the characteristic, fixed coefficient closure
  and finite extension: `D : FiniteFieldDatum.{u}`, `C : D.CoefficientDatum`,
  `E : IntermediateField (Padic C.l) C.Qbar` and `[FiniteDimensional (Padic C.l) E]`.
  `C.different` supplies the characteristic inequality. The valuation ring, chosen
  uniformizer, quotients and completed sheaves are the recorded coefficient constructions.
- Separated finite-type k-schemes: `X Y : Scheme.{u}` with `Over`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances on both structure maps.
- The k-morphism f, separated and smooth of pure dimension d: `f : X ⟶ Y`, `f.IsOver`,
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, `(d : ℕ)` and
  `SmoothOfRelativeDimension d f`. These include exactly the stated finite-type setting;
  d is nonnegative by its type.
- K in the integral bounded constructible finite-Tor category: `K` in the derived category
  of `scalarReductionSource C.l E Y` and `hK : finiteTorConstructibleIntegral ... K`.
  This predicate includes completeness, common cohomological bounds and uniform Tor bounds.
- Small pro-etale sites and actual coefficients: inherited from `scalarReductionSource`,
  `normalizedDVRDerived` and the original dependency constructions, retaining site object
  universe u+1 and morphism universe u. No site universe has been collapsed.

Conclusion correspondence:

- K_n is `scalarReductionDerivedExtension ... n |>.obj K`, with internal index n denoting
  exponent n+1. `purAdicSource` is the recorded integral pullback, twist and shift. The
  finite endpoints and g_n are the `left`, `right` and `hom` of `purAdicFiniteArrow`.
- The first conjunct asserts every specified finite g_n is invertible.
- The second conjunct asserts invertibility of rho^U (`purAdicFiniteSourceNormalization`)
  and rho^V (`exceptionalNormalization`) and the displayed quotient compatibility square,
  for every `h : n ≤ m`. The latter normalization is literally the finite exceptional
  comparison followed by exceptional image of `purAdicQuotientNormalization` of K.
  Its additional `HEq` says exactly that the actual exceptional transition is its adjoint
  under the recorded finite tensor/restriction adjunction and coefficient transport.
- `sourceSequence` is `(pullbackTensorCalculus ...).reduction.obj (purAdicSource ...)`.
  `targetSequence` is `(integralExceptionalSystem ...).obj K`; its limit is the existing
  definition of the integral exceptional inverse image. `sourceTower` and `targetTower`
  are the exact restrictions of those same systems to completed coefficients.
- The existential normalized-DVR-tower clause fixes U.tower and V.tower by equality to
  these actual towers. It fixes every M_n and evaluation map by `HEq` to the finite
  endpoints and `sourceEvaluation`/`targetEvaluation`. Source evaluation uses the actual
  reduction evaluation followed by b^U_n, target evaluation uses the canonical exceptional
  coordinate/site/compact-support mate comparison. It fixes every semilinear transition
  by `HEq`; `NormalizedDVRTower` already includes the identity, quotient cocycle, actual
  strict derived tower, and invertibility of the adjoint normalization.
- The fourth conjunct is the displayed adjacent-transition equation after restriction
  along R_X to B_n; the restricted transitions include the recorded composition comparison.
- The last conjunct gives a morphism G between the actual strict derived towers and asserts
  its exact finite evaluations, expressed without inverse choices by postcomposing with
  the canonical target evaluation. It asserts only existence of G.
- No uniqueness or natural choice of G, common stratification, or integral local model
  is included. No normalization or finite-purity property is moved into the hypotheses.

Recorded declaration interfaces read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and topology.
- `Sheaf.Paper.FiniteTorAmplitudeSites` (publicly importing `FiniteTorAmplitude`):
  `finiteTorConstructibleIntegral`, `finiteTorConstructible`, `finiteTorConstructibleEtale`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionDerivedExtension`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the intrinsic integral twisting
  object and functor (the actual source is the same recorded integralComplexTwist).
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: recorded
  `ConstructibleExceptionalCoefficients.System`; the actual exceptional system construction
  is reused through `integralExceptionalSystem`, without an arbitrary exceptional datum.
- `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap`.
- `Sheaf.Paper.AdicPuritySourceReduction`: `purAdicSourceReduction`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`.
  The coherent refinement used here is the published `pullbackTensorCalculus.reduction`,
  retaining its strict K-flat reduction model and evaluation comparison.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, canonical evaluation and
  transition, finite restriction and completed-coefficient restriction comparisons.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: generic site change of rings
  publicly imported from the existing construction.
- `def-pur-adic-finite-source-normalization`, with `existing: true` in
  `Sheaf.Paper.AdicPuritySourceFiniteness`, owns `purAdicFiniteSourceNormalization`,
  `purAdicFiniteSourceNormalization_existsUnique`, `purAdicFiniteSourceTransition`,
  `purAdicQuotientNormalization`, `purAdicQuotientRestrictionIso`, and their defining
  helpers. Only these constructions occur in the statement; the source-finiteness
  theorem is used solely in the proof.
- `def-pur-finite-reduction-root-charts`, `Sheaf.Paper.FiniteReductionRootCharts`:
  `PurityFiniteSetting.finiteReduction` and `finiteReductionAdjunction`.
- `def-pur-finite-reduction-comparisons`, `Sheaf.Paper.FiniteReductionComparisons`:
  `PurityFiniteSetting.finiteReductionExceptionalComparison`.
- `def-coef-ringed-sequence-site`, `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceDerivedRestriction`, `coefficientRestrictedEvaluationIso`,
  and `coefficientSequenceDerivedTransition`.
- `def-pur-completed-pullback-tensor-comparison`,
  `Sheaf.Paper.CompletedPullbackTensorComparison`: `pullbackTensorCalculus`.
- `def-pur-adic-exceptional-system-realization`,
  `Sheaf.Paper.IntegralExceptionalInverseImage`: `integralExceptionalSystem`.
- `def-pur-composition-comparisons`, `Sheaf.Paper.PurityCompositionCoherence`:
  `PurityFiniteSetting.compositionExceptional`.
- `def-pur-adic-exceptional-reduction` gives `purAdicExceptionalEvaluation`;
  `def-pur-adic-purity-objects` gives `purAdicSource` and `purAdicFiniteArrow`.
  No existing dependency record or mathematical statement changes.

The seven proof steps import their already recorded modules: AdicCoefficientDatum,
AdicPuritySourceFiniteness, FiniteExceptional, CoefficientSystemDerivedComparison,
EtaleCoefficientSystemAdjoint, ProEtaleConstructibleOrigin, SequentialTowerEvaluationFull,
SmoothPurityNaturality, FiniteCoefficientSmoothPurity, FiniteReductionOfPurity. Helpers are
composites in this owning node's module, not independent notions or new axiom packages.

Edge cases checked before writing: m=n (identity quotient), n=0 in the internal index
(exponent one), d=0, K=0, X empty, and the identity morphism. No nonemptiness, quotient
flatness, ramification divisibility, boundedness of arbitrary tower objects, or common
stratification has been added. The restriction maps use the actual tensor/restriction
adjunction even for nonflat quotients. All variables/universes are explicitly bound.

Searches, all through prescribed tools and read-only source searches:

- msearch LeanFinder, query “Compatible finite coefficient smooth purity isomorphisms
  between normalized reduction towers lift to a morphism in the derived category of strict
  towers”: eight unrelated normalization-diagram and formally-smooth lifting results.
- msearch Loogle, query `CategoryTheory.NatTrans, CategoryTheory.IsIso`: zero hits.
- msearch grep, query `normalized.*[Tt]ower|[Pp]urity|sequential.*evaluation`: three hits in
  Mathlib/FieldTheory/NormalizedTrace.lean, none concerning derived sheaf towers.
- rg over lean/WeilConjectures and lean/Sheaf for normalized purity, adic_normalized,
  normalizedPurity and the proposed names: existing normalized purity constructions and
  reconstruction nodes, but none states this node. grep of the exact node id in
  lean/WeilConjectures: no result. dag/lean_names_upstream.json also has no exact match.

Source check: the source filename in this older DAG is no longer present in the current
blueprint snapshot. Read the current sk-thm-purity-transport.proof.md (Step 1, quotient
compatibility), and sk-thm-purity-transport-coefficient-change.md/.proof.md, which explicitly
reference det-sp-tower-gamma, its finite evaluations and normalization. The delivery retains
the reviewed DAG statement and all seven proof steps; it makes no source-based correction.

Validation: scompile.py accepted both the sandbox module and its actual library module
path with no messages (28.7 s and 15.3 s respectively on the first successful run).
The initial elaboration error on a non-exposed restriction presentation was repaired by
using the actual system transition and stating its adjunction-transpose characterization;
no dependency was patched. Expected sorry use is confined to the one named theorem.
No statement dispute or mathematical statement correction is required. This repair adds the definition ownership described below; the original validation above predates the repair.

## Second reading by Q04

No independent worker reading: this dispatcher assignment prohibits starting other agents.
The maintainer performs the independent delivery review. Author self-check: every datum
and clause was matched above with the node and actual declaration signatures open; the
normalization identity is asserted for all pairs, the source and target tower objects are
fixed, their evaluations and transitions are fixed, the exceptional normalization is its
specified counit mate, and the lift is existential with every evaluation fixed. The source
comparison uses b^U_n, rather than an arbitrary isomorphism. No uniqueness or finiteness
condition beyond the statement is asserted.


## New nodes

`def-pur-adic-finite-source-normalization` owns the already published quotient
normalization and source-normalization constructions in
`Sheaf.Paper.AdicPuritySourceFiniteness`, using `existing: true`. Its statement defines
the direct quotient ring diagram, exact coefficient restriction, identity-on-sections
restriction comparison, the adjoint input quotient normalization, the finite source,
the equality-pinned source normalization, its unique existence, and its semilinear
adjoint transition. Its primary declaration is `purAdicFiniteSourceNormalization`;
its `lean.declarations` includes all ten supporting declarations through
`purAdicFiniteSourceTransition`, including the uniquely determining
`purAdicFiniteSourceNormalization_existsUnique`. This does not duplicate or move any
published declaration, and does not assert the source-finiteness theorem. The
existence theorem uniquely determines the composite, so its choice supplies real
canonical data under the project's rule for uniquely determined constructions.

Hypotheses are exactly the existing `D`, `C`, finite `E`, scheme and smoothness
instances, `K`, `hK`, and `h : n ≤ m` in the published signatures. `purAdicDirectQuotientRings`
is the actual quotient-factor diagram; `purAdicDerivedCoefficientRestriction` is exact
restriction on derived categories; `purAdicQuotientRestrictionIso` supplies J;
`purAdicQuotientNormalization` is the inverse Hom-adjunction image of the canonical
integral transition and J. `IsPurAdicNormalizationComposite` pins each factor and
its composite by HEq. `IsPurAdicFiniteSourceNormalization` specializes it to
`finiteReductionSourceComparison` and `compositionShiftedPullback` of the input
normalization. The uniquely determined choice is rho; `purAdicFiniteSourceTransition`
is its actual adjunct followed by J inverse. Equal indices, exponent one, dimension
zero, zero inputs and empty schemes remain allowed; no invertibility or finiteness
claim was added to this definition node.

Source: the current transport proof Step 1 (compatibility with finite reduction),
serving the integral reconstruction source-object argument. Searches were msearch
LeanSearch and LeanFinder for “Canonical quotient normalization of finite smooth
purity source and its tensor restriction adjoint transition”, and msearch grep for
`purAdicFiniteSourceNormalization|purAdicQuotientNormalization|purAdicQuotientRestrictionIso`.
The first two returned eight unrelated representation, scheme-normalization and
normed quotient results each; grep returned zero. Their full outputs are recorded
verbatim in the new node. Read-only rg of DAG nodes, WeilConjectures and Sheaf found
only the existing theorem node and its module; blueprint_refs search found no
owning definition node. Thus the declarations already exist, but the required
independent definition ownership did not.

## Repair of return at 9e093de28be7

H2: added `def-pur-adic-finite-source-normalization` as the existing-definition
owner and cited the six landed definition owners requested by the return. Their
modules are explicit public imports. Source-finiteness and finite-reduction purity
theorems remain proof dependencies. The accepted theorem signature and all helper
bodies are preserved.

## Maintainer citation correction

Server maintenance commit `21ff6c640be17584dde69f5bf8763abc50dc235f` corrected the
base node's definition citations and statement dependencies under the merge lock.
The finite exceptional comparison now cites `def-pur-finite-reduction-comparisons`,
and derived scalar extension also cites `def-pur-finite-reduction-root-charts`.
Only bracketed references changed; the mathematical prose, hypotheses, conclusions,
proof and proof dependencies were preserved. `statement_change` records the old
statement and dependencies and the sole citer, `thm-pur-adic-reconstruction`, whose
first proof step still applies without modification. The sandbox carries that
committed statement and audit record verbatim. Relative to this corrected base,
this delivery only sets `lean` and adds definition dependencies.

The previous repeated dry-run failures were caused by trying to remove a theorem
statement dependency while preserving its citation in the statement. The normal
delivery gate correctly requires a recorded correction for that removal; the
maintainer fixed the data rather than editing or bypassing the gate. The old retry
transcript is preserved in the maintenance `.bak` of this report.

H11 advisory: the second-reading section is an author's self-check. The maintainer's
independent review of the returned head accepted the mathematics clause by clause.
