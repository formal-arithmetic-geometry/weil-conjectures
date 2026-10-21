## Worker report

Item: lem-fix-compactification-completed-realization. Module:
`Sheaf.Paper.CompactificationCompletedRealization`, main declaration
`WeilConjectures.CompactificationCompletedRealization.completedRealization`.
The theorem has one `sorry`; every helper has actual data. No node statement,
dependency list, proof plan, or target has changed. There is no statement dispute.
No repair note exists for this item.

The existing `sfQcqsCompactSupportRealization` is used as the specified natural
isomorphism dc. It does not by itself include the present node's strict-tower,
constructibility and completed projection clauses, so this is not an existing
match. In particular, the theorem does not introduce an arbitrary realization
in place of that recorded dc.

Hypothesis-by-hypothesis rendering:

- The prime is `(l : ℕ) [Fact l.Prime]`; `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` is the finite coefficient
  extension. `completed l E`, `finite l E (n+1) (Nat.le_add_left 1 n)` and
  `reduction l E (n+1) ...` use its recorded valuation ring, uniformizer,
  standard quotients and completed coefficient sheaves. Index n denotes
  exponent n+1, so n=0 is the first positive quotient, not exponent zero.
- `(k : Type u) [Field k] (hl : IsUnit (l : k))` supplies the base field and
  invertibility. Instances `X.Over`, `Y.Over`, `LocallyOfFiniteType` and
  `QuasiCompact` on their structure maps say finite type over k; `f.IsOver`
  says f is a k-morphism. The separated, locally finite type and quasi-compact
  instances on f are properties already implied by the stated compactification
  between finite-type k-schemes, and match the existing compact-support API.
- `c : Compactification f` contains c.i = j, c.g = p, their factorization,
  open immersion and properness; `[QuasiCompact c.i]` retains the explicit
  quasi-compactness assumption on j. Its middle scheme c.Z is over k by
  c.g followed by Y's structure map, and is finite type by properness of c.g.
  No separatedness of X or Y over k is imposed.
- `scalarReductionSource.{u,u} l E W` is the actual completed-ring module
  category on `W.ProEt`, and `DerivedCategory` is its ordinary unbounded
  derived category. Pro-etale objects remain in Type (u+1), with morphisms
  in universe u. No site-universe equality or small-site substitution occurs.
- `K : sfIntegralConstructibleCategory l E X` and likewise L use exactly the
  recorded derived completeness, finite constructibility of every reduction,
  and one common finite cohomological interval. They impose no Tor bound.
- `hQ` and `_hV` say the displayed completed tensor argument on X and completed
  tensor source on Y belong to these same categories. Transport by dc gives
  the equivalent source condition using recorded compact support. The middle
  open tensor vertex is identified with extension of Q by the open tensor
  comparison; its constructibility follows from the universal first clause.
  Thus these binders express the node's tensor-domain restriction without
  strengthening it to a finite-Tor condition.

Clause-by-clause rendering:

- `image (completed l E) c` is exactly ordinary unbounded Rp_* after exact
  localized j!. The first universal conjunct asserts constructibility and
  derived completeness of both j!K and this image.
- `supportTower` is an alias of the very `Classical.choose` selected inside the
  existing integral compact-support definition, not a new tower chosen merely
  from matching evaluations. `supportEvaluation` aliases its already recorded
  evaluation comparisons. The explicit all-m,n transition conjunct is precisely
  `compactSupportRestrictedTransition`, including the identity case m=n.
- `strictReduction` is reduction into the actual derived varying-coefficient
  system followed by exact restriction into the derived category of strict
  completed-module towers. The natural isomorphism beta lives in this strict
  derived category, before taking any limit. Its evaluation equation gives the
  recorded scalar coordinates, and its total-limit equation is separately
  asserted; the latter is not deduced from faithfulness of evaluations.
- `coefficientConstantTowerLimit` is the actual total right-derived inverse
  limit of strict module towers. Gamma identifies the recorded compact-support
  action with the limit of the prescribed support tower, with its projections
  fixed by the existing scalar-adjunction mates of Roos projections. The
  displayed formula `dc = S.adjunction.unit ≫ Rlim.map beta ≫ gamma.inv`
  is the canonical completion-unit realization of that recorded dc.
- `SfQcqsCompactSupportRealizationSpec` retains the existing natural
  realization's prescribed scalar projection normalization. The following
  explicit reduction equation rewrites its middle factor as `orderedReduction`:
  first `properComparison`, then proper image of `openComparison`. The finite
  scalar and intrinsic-image coordinate isomorphisms on either side are the
  published ones, rather than freely chosen identifications.
- `OpenFactorCoherence.Tensor` and `.Pull` are existing normalized coordinates
  for the recorded completed operations. They retain the K-flat/quotient-chain
  tensor normalization and actual pullback completion augmentation. Their
  existence is in the conclusion, not an assumption. `argumentUnit` first
  inserts tensor completion and then completed pullback.
- `augmentedProjection` is the actual ordinary `projectionMap` from the
  proper/open counits, followed by the canonical target augmentation.
  The existence-and-uniqueness conjunct for pi characterizes its extension
  across actual `aY.chi`. The reflector unit's Hom bijection is exactly the
  characterization of the completed counit, so pi is the specified completed
  counit projection, not an arbitrary map with prescribed finite reductions.
- `FiniteProjectionEquation` compares that actual ordinary projection with the
  actual finite `projectionMap` via `scalarTensor`, `scalarPull`, the ordered
  coefficient comparison and target augmentation. All finite tensor models
  have their existing K-flat representative normalization.
- `strictProjection` is the reduction of that already defined counit map as ONE
  derived strict-system map. `strictSourceUnit` is the actual source completion
  map in the same strict category. The theorem asserts its invertibility and
  the equality `strictReduction.map pi = inv strictSourceUnit ≫ strictProjection`
  in the derived category of strict towers. Thus transitions are present before
  limit, not patched together from a family of finite morphisms.
- In the final conjunct rho is defined explicitly by applying total limit to
  this strict map, using beta on Q and gamma on its output. Its source coordinate
  is tensor of dc.inv on K with identity on L. The asserted square is
  `pi ≫ dc_Q = tensor.map (dc_K, id_L) ≫ rho`. This includes the specified source
  and target dc maps and is equality of the derived morphisms themselves.

Dependency declarations used (all recorded statement-dependency modules are
public imports; proof-dependency modules are retained as imports):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the extension coefficient constructions
  reexported there.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification`, its c.i, c.g and factorization.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the published completed sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: ordinary ringed
  pullback/direct-image/adjunction, used via the published PurCompactSupport API.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`, `SfQcqsCompactSupportRealizationSpec`;
  its reexports `sfCompactSupportFiniteIntegralFunctor`,
  `sfCompactSupportFiniteReductionIso`, `exists_compactSupportReductionTower`,
  and `PurCompactSupport.image`, `projectionMap`, `properComparison`,
  `openComparison`, `scalarTensor`, `scalarPull`, `finiteImageIso`,
  `finiteReductionIso`. Their full signatures and normalization docstrings were read.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`; the strict total limit
  here is the canonical rightDerivedFunctor presentation of the same limit.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `integralCompletedTensor`,
  `integralDerivedPullback`, their actual quotient towers and completion units.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`; its
  geometric projection is rendered with the concrete proper/open counit maps.
- Finite type and proper/open morphism properties are Mathlib's existing
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`, `IsOpenImmersion`.
- Further existing coordinate interfaces: `Sheaf.SixFunctors.OpenFactorTensorModel`
  (`OpenFactorCoherence.Tensor`, `Tensor.chi`, and reexported `Pull`, `Pull.unit`),
  and `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
  (`CoefficientDerivedSystemCalculus`, `.adjunction`, `.reductionEvaluation`,
  `CoefficientDerivedSystemCoherence`, `coefficientRestrictedEvaluationIso`).
  These are used as normalized presentation data for the original tensor and
  pullback notions. No downstream operation-reduction theorem is used or awaited.

The proof docstring follows all ten node proof steps and cites their actual
ingredients: the coefficient DVR and standard quotient perfectness, open interval
preservation and strict open reduction, proper-image strict tower, ordinary direct
image/limit comparison, integral constructibility, proper perfect projection,
constant/completed coefficient equivalence, strict tensor and operation substitution,
coefficient-restriction counit, reflector unit formulas, and completed projection
coherence. Their recorded modules are imported for stage 3.

Searches for an existing statement:

- `msearch.py ... leanfinder`: completed compactification strict quotient inverse
  limit without a Tor bound; results concerned HasCompactSupport and topological
  AbstractCompletion, not derived proper/open realization.
- `msearch.py ... loogle`:
  `WeilConjectures.sfQcqsCompactSupportRealization, WeilConjectures.PurCompactSupport.comparison`;
  unknown-identifier/no exact matches in the search index. Local declarations were
  then read directly; the first is the natural realization used here, not the
  additional strict projection coherence statement.
- `msearch.py ... grep`: `compactification.*realization|completed.*projection`;
  no Mathlib match for the combined assertion.
- `msearch.py ... leansearch`:
  `Completed compact support proper open realization finite coefficient tower projection counit`;
  eight unrelated results including CompHausLike locally constant counits, Pi.counit
  and coalgebra constructions.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for compactification,
  realization, completed projection and the item id: the existing Qcqs realization
  is the closest declaration; no exact combined assertion. The item id has no
  upstream declaration in `lean/WeilConjectures` or `dag/lean_names_upstream.json`.

Edge cases read against the definitions before writing and checked again:
zero K or L; empty X; identity open factor; identity proper factor; exponent one
(n=0); equal-level quotient m=n; longer quotient composites; torsion K; constructible
K without an assumed Tor interval; nonseparated structure morphisms; and tensor
expressions outside the constructible domain (properly excluded only from the
projection clause). Unbounded ordinary tensors are retained at augmentedProjection,
while their completion is the displayed constructible tensor. No assertion that
finite evaluations are faithful is made.

Validation: scompile.py compiled both the sandbox and actual module against the
live published build, with no errors or warnings. Every variable and universe is
explicit; no local/global lake build was run. Only the item's sandbox was written.

## Second reading by ND

A separate rereading of the node, source paragraph and full Lean module was done
by this worker. The dispatcher explicitly prohibits starting other agents; this
is not claimed as a second person's independent review. The maintainer's independent
review receives this delivery as requested by the brief.

The rereading identified and repaired three omissions in the intermediate draft:
explicit quasi-compactness of j, explicit prescribed all-level quotient transition
normalization, and the source dc tensor vertex of the final square. It also replaced
an attempted definitional identification of two total-limit presentations with a
projection-normalized gamma comparison; the original and canonical total-limit
functors are not definitionally equal. The final dc is still the actual recorded
natural isomorphism, with a separate total-limit equality and strict-tower map
identity. No definition was copied, no arbitrary map substituted, and no Tor
hypothesis added. The theorem's only postponed proof is the named main theorem,
whose ten-step proof docstring matches this DAG node.
