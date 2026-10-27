## Worker report

The module `Sheaf.Paper.TowerTracePurityComparison` states
`WeilConjectures.TowerTracePurityComparison.tower_trace_purity_comparison`.
This is stage 2: its sole theorem has proof `sorry`. All helper definitions have
concrete data; no morphism or functor is defined by choosing an unspecified
existence witness. Membership certificates use the already recorded adic
reconstruction theorem, and do not choose any object or arrow from it.

### Hypotheses and constructions

`Comparison` spells out the assertion. It derives `CompactSpace X`,
`QuasiSeparatedSpace Y`, and hence `QuasiCompact (j ≫ p)` from the standing
finite-type and separated structure maps before universally quantifying `S`.
It also derives `IsSeparated (j ≫ p)`, `LocallyOfFiniteType (j ≫ p)`, and
residue-field invertibility of ell on X and Y from the existing `purAdicResidueUnit`
theorem. None of these become additional hypotheses of the exported theorem.
The helper definitions accept this derived quasi-compactness instance; the main
theorem adds no such geometric hypothesis. These are proof instances, with no
object or morphism introduced by a statement-level let.

- The global datum is `P : PurityFiniteSetting.{u}`. Its `field` contains the prime
  characteristic, finite field cardinality and algebraic closure; `coefficients`
  contains the prime `l`, `different`, and fixed coefficient algebraic closure.
  The extra `extension` and positive `level` in this existing package never restrict
  the theorem's coefficient fields: `FieldShriekSystem.Index P` ranges over every
  finite intermediate field, and `base P` is the bottom intermediate field,
  canonically Q_l. None of the constructions use `P.level` to restrict a reduction.
- `X`, `Y`, and the compactification middle scheme `Z` are `Scheme.{u}`.
  Their `Over (Spec (.of P.field.k))` instances are the k-structures. Separatedness
  is the two `IsSeparated` structure morphism instances. Finite type is
  `LocallyOfFiniteType` plus `QuasiCompact` on those same morphisms. No properness
  of X or Y over k is assumed.
- `j : X ⟶ Z`, `[IsOpenImmersion j]`, `p : Z ⟶ Y`, `[IsProper p]` fix one arbitrary
  compactification, using `SpTowerGamma.factorization j p`. The morphism in the node
  is `j ≫ p`; its `IsOver` instance is explicit. `d : ℕ` and
  `[SmoothOfRelativeDimension d (j ≫ p)]` give smoothness and pure relative dimension
  including zero. Separatedness and finite type of this composite follow from the
  standing geometry. No change of compactification is used in the formulas.
- `S : ConstructibleExceptionalCoefficients.System ... (f := j ≫ p)` is the
  specified constructible exceptional system. It is an input, so the comparison
  does not silently choose a different exceptional adjunction. Its `ring.operation`
  supplies P, G, and the adjunction, and `S.ring.left` is the recorded normalized proper/open
  realization of compact support. `specifiedAdjunction` transports that left
  realization and fixes the comparison with the realized tower adjunction.
- All integral objects are the existing completed coefficient objects:
  `integralConstantCoefficientObject` is the degree-zero regular completed module,
  `PurUnitTrace.tateUnit` is the actual shifted Tate line, and
  `finiteTorConstructibleIntegralCategory` requires completeness, constructibility,
  uniform cohomological bounds and one common finite Tor interval for all reductions.
  The small pro-etale site's object and morphism universes remain those of the
  existing definitions; no universe equality is imposed on that site.
- `M`, `R`, and `A` are existential presentation witnesses, supplied by the theorem.
  `M : FieldShriekSystem.Models P` and `R : FieldExtensionTowers.Result ...` retain
  the actual canonical coefficient systems, whole-tower comparisons, realization,
  units, counits, and coefficient composition. `Stage` packages their domain
  certificates and canonical tensor coordinates; these are output data, not extra
  geometric assumptions. Its `normal` has the full finite Hom normalization.
  Its `tensorSource` is constrained by `IsJNormalized` on every K-flat representative,
  and its `unitIso` by `IsUnitNormalized`. The projection inverse uses exactly
  `adicProjection`, with proofs of invertibility, rather than a freely chosen map.
- `tower` is `m.sourceNormalization.exactSource.hom` followed by the existing
  `RealizedTowerPurity.component`. The latter is literally `realized` followed by
  `restrictedAdjunction.rightAdjointUniq ...`, so this is delta composed with Rlim
  of the actual strict-tower gamma, not a lift chosen from separate finite arrows.
  `m.sourceNormalization.exactSource` is normalized on K-flat representatives.
- `orientation` is `sourceUnitIso.inv ≫ tower(unit)`, the actual a^T_E. The first
  result conjunct records its prescribed finite reductions and invertibility.
- `counitTrace g` is `S.left.inv`, followed by `S.operation.F.map g`, followed by
  the specified exceptional counit. It is precisely epsilon P(g), expressed in
  the actual completed proper/open compact-support presentation.
- `extendedTrace t0` is the canonical twist-unit identification, then the existing
  `PurAdicScalarTrace.trace`, with the inverse support mate, ordinary derived
  completed-ring scalar extension, and the normalized coefficient-unit multiplication.
  `Stage.coefficients.normalization` identifies its support comparison with the
  actual `PurCompactSupport.comparison`. The twists and their shift comparisons
  are the published canonical `twistComparison`, not arbitrary theta maps.
- `tracePurity` uses the K-flat-normalized `tensorSource`, inverse `adicProjection`,
  `adicTraceTensor`, and `adicTranspose` for the specified adjunction. The published
  tensor coordinates put the Tate line first; their Koszul symmetry gives exactly
  the node's coefficient-second `(1_K tensor t_E) Pi`. The shift is the even integer
  `2 * (d : ℤ)` and is retained, not discarded.

### Conclusions, clause by clause

- The quantified `g0` is any isomorphism from the base Tate unit to the specified
  exceptional image of the completed coefficient unit. Its only additional
  hypothesis is `PrescribedUnitReductions ... g0.hom`. This predicate writes out
  the equality with `purAdicFiniteArrow` using `sourceUnitIso`, the recorded
  `scalarReductionDerivedExtension`, `finiteReduction`, and `purAdicSourceReduction`.
  It tests every `n : ℕ`, denoting uniformizer exponent n+1; thus every positive
  finite level occurs. `R` retains the cofinal ell-power presentation as well.
- `g0.hom = orientation ... (base P)` is the first required equality. Equality on
  homs is equality of the isomorphisms since the inverse is determined.
- For every finite E, the next equality is
  `extendedTrace (counitTrace g0.hom) = counitTrace (orientation E)`, exactly
  t_E = epsilon_E P_E(a^T_E).
- For every E and every K in the indicated full finite-Tor category, the next equality
  is `tracePurity (extendedTrace (counitTrace g0.hom)) K = tower K`. It is equality of
  actual integral derived morphisms, not only equality after cohomology or reduction.
- `rationalInput P E K` is the actual `Q_E K` through the specified field-stage
  rationalization. The rational conclusion now explicitly names
  `RationalSmoothPurityCanonical.rationalIso (atField P E) (j ≫ p) c S d (Q_E K)`;
  it is not an arbitrary arrow with a hypothesis identifying it with this delivery's
  own trace transpose. Its hom equals `rationalTowerComponent ... K`.
- `rationalTowerComponent` writes the required comparison word in full:
  `rationalSourceComparison.hom`, followed by `normalizedRationalSource`,
  `rationalTower`, `(S.fields.rationalizationComparison c stageE).b.hom.app`,
  and the specified rational exceptional functor applied to
  `eqToHom (representative_eq (atField P E) (Q_E K))`.
  `normalizedRationalSource` is literally the scalar localization of
  `A.tensorSource.inv.app K`, on the unchanged integral representative. Thus all
  source shifts, K-flat tensor normalization, counit-preserving target comparisons,
  and representative proof transports occur in the statement's concrete maps.
- For every further finite F containing E, the common-stage equality uses the actual
  `sourceScalar` followed by the recorded `rationalIso` over F on the scalar-extended
  input. Its other side is scalar extension of `rationalTowerComponent` followed by
  `(S.fields.rationalComparison c stageE stageF inclusion).b.hom.app (Q_E K)`.
  Both sides are mapped by `commonImage P F X`, namely the published small-field-model
  `modelScalar` followed by `commonInclusion`. This is exactly the source/exceptional
  square of `RationalSmoothPurityCanonical.rationalIso_scalar` and its common-stage
  image, the alternative explicitly requested in the return. It retains identity
  inclusions F=E and arbitrary larger common stages. The full simultaneous `R` retains
  the field-tower normalizations and cocycles used to identify these coefficient maps.

### Dependency declarations read and used

The module imports the recorded statement interfaces and the recorded proof plan.
The principal dependencies and their declarations are:

| Module | Declaration or interface used |
| --- | --- |
| `Sheaf.Paper.PurityFiniteSetting` | `WeilConjectures.PurityFiniteSetting` |
| `Mathlib.AlgebraicGeometry.Morphisms.Smooth` | `AlgebraicGeometry.SmoothOfRelativeDimension` |
| `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` | completed coefficients and their projections; `integralConstantToCompletionOfUniverses` |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | `sfIntegralTwistingFunctor`, actual integral Tate lines |
| `Sheaf.Paper.SfIntegralConstructible` | `sfIntegralConstructible`, `sfIntegralConstructibleCategory` |
| `Sheaf.Paper.FiniteTorAmplitudeSites` / `FiniteTorAmplitude` | `finiteTorConstructibleIntegralCategory` |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | `integralDerivedPullback`, `integralCompletedTensor` via their global recorded interfaces |
| `Sheaf.Paper.QcqsCompactSupportRealization` | normalized completed proper/open realization |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | `ConstructibleExceptionalCoefficients.System`, its `ring` operations and `fields` comparisons, units and counits |
| `WeilConjectures.Compactification.RefinementCategory` | the existing compactification category; the fixed object is `SpTowerGamma.factorization j p` |
| `Sheaf.Paper.ExchangeProjectionSuppliedDomains` | canonical projection formula via the recorded ringed projection construction |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | canonical realized proper/open comparisons |
| `Mathlib.CategoryTheory.Adjunction.Unique` | `Adjunction.rightAdjointUniq` in `component` |
| `Sheaf.Paper.IntegralAdjunctionBijection` | `SpIntegralAdjunction.Realization`, its actual realized adjunction |
| `Sheaf.Paper.SmoothPurityTowerGamma` | `SpTowerGamma.gamma` used by `component` |
| `Sheaf.Paper.PurAdicReconstruction` | `purAdicReconstruction`, source membership only in `sourceObject` |
| `Sheaf.Paper.SmoothPurityMap` | prescribed finite purity via `purAdicFiniteArrow` |
| `Sheaf.Paper.FieldExtensionTowers` | `FieldExtensionTowers.Result`, models, comparisons, rational scalar extension |
| `Sheaf.Paper.PbcRationalCategory` | existing raw localization, via `sfRationalConstructibleLocalization` |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | `rationalIso`, `rationalSourceComparison`, `representative_eq`, `rationalIso_scalar`, and finite-stage model transports |
| `Sheaf.Paper.AdicPurityScalarNaturality` | the trace-transpose integral representative family in the proof plan |
| `Sheaf.Paper.PbcQbarCategory` | actual common finite-stage category via `commonImage` |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | `SpIntegralOrientation.reduction_injectivity` (proof import) |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | `RealizedTowerPurity.realized_tower_purity_transpose` (proof import) |

`def-weil-scheme-morphism-properties` is a convention collector with no declaration;
its named Mathlib predicates are used directly. The Mathlib dependency
`det-sp-unique-right-adjoint` is its recorded `Adjunction.rightAdjointUniq`, not a
missing declaration. The helper modules `AdicUnitTraceConstruction` and
`TowerPurityRealizedData` are the already landed sources of the normalized source,
unit, scalar trace, and tower component interfaces, not private copies.

### Searches and edge cases

Actual search calls:

- `msearch.py ... leanfinder "The smooth purity map obtained by derived inverse limit
  of diagonal orientations equals the adjoint transpose of the scalar extended
  integral trace"`: eight results about integral algebraic traces, cotangent spaces,
  and smooth ring maps; none is the geometric comparison.
- `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Adjunction.rightAdjointUniq"`: the generic
  `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`; this supplies the comparison
  mechanism but not the geometric tower/trace statement.
- `msearch.py ... grep "purity|orientation.*trace|trace.*orientation" CategoryTheory`:
  zero Mathlib hits.
- `rg` in the recorded upstream `lean/WeilConjectures` for the item id and
  `TowerTracePurity`: no matches. The analogous exact declaration and namespace
  searches in `lean/Sheaf` found no existing comparison statement. Conceptual searches
  found the recorded unit-trace construction, tower realization, scalar-naturality,
  and orientation-injectivity interfaces, which this module reuses.

Edge cases checked before writing: d=0 retains the zero twist and shift and the
canonical tensor units; X empty is allowed for any d and introduces no nonempty
assumption; Y empty forces X empty but all formulas still type. Zero K is quantified.
Disconnected X is allowed: orientation injectivity uses all sections, not a chosen
connected component or a nonzero scalar. E=Q_l and F=E use bottom and identity
inclusions, with the actual scalar unit comparisons. All positive finite exponents
are tested, including the first; no division by a ramification index drops levels.
No faithfulness claim is made for finite evaluations on arbitrary derived morphisms.

No source statement correction, new DAG node, or dependency-record repair is made.
The existing resolved stage-1 repair note concerns the accepted split into the two
comparison lemmas; that split and the four-step proof are preserved unchanged.

## Second reading by NB

A separate review pass by this dispatched worker compares the source node and the
written signatures; no second agent was started, as required by the dispatcher brief.
The maintainer's independent review remains the independent reading of this delivery.
The checks focus on the arbitrary normalized base lift (not a selected reconstruction
lift), the specified exceptional system, the fixed compactification in every map,
the entire-tower definition of `tower`, the actual inverse projection and scalar
trace formulas, and both final rational/common-stage clauses. The helper data are
presentation outputs, with all object and arrow data written in full. Compile and
delivery-check results are recorded below.


### Returned-delivery repair

The maintainer returned immutable head `364f3c89b544` for H3+H4: the old free
`rho = rationalTrace` condition did not connect to the previously specified family.
That condition and its free arrow have been removed. The integral clauses and
presentation constraints are preserved, using `S.ring` of the full specified System.
The three concrete rational helper definitions and the explicit rationalIso/common-stage
square above repair the returned point. The theorem retains its single `sorry`.
The node's natural-language statement is unchanged; only its Lean record changes.
The sandbox node's non-Lean fields were compared to current main and agree verbatim.

Consumer check: `lem-pur-transport-rational-hom-counit` can now use the rationalIso
conjunct directly, with the specified counit comparison. Likewise
`lem-pur-rational-normalized-purity-diagrams` receives both the rationalIso equality
and the scalar/common-stage equation with the named source and exceptional maps.
Neither consumer is edited. The sources and full signatures of rationalIso,
rationalIso_scalar, rationalSourceComparison, representative_eq, and System were
read again for this repair. The d=0, empty X/Y, E=Q_l, F=E and every positive
exponent n+1 cases remain included, with no nonempty or strict-inclusion hypothesis.

### Validation

The repaired module passes the prescribed `scompile.py` standalone check:
37.1 seconds for the sandbox check and 36.4 seconds for the owning library module,
with no errors or warnings. The canonical scalar functor and the typed source/tower
composites are kept opaque during elaboration; the integral tensor and pullback
implementations are also not unfolded unnecessarily. No time or heartbeat limit was
raised, and no transparency-respect option was disabled. Temporary profiling options
and the optional diagnostic probe were removed. The final file has one `sorry`,
no debug commands, and maximum line width 99. The node's only delta from current
main is its Lean record, including the verbatim theorem signature.

The repair dry run returned `OK`: preflight and compilation passed for the
three-file packet (owning module, item node, and this report), with no source
statement or dependency-node changes.
