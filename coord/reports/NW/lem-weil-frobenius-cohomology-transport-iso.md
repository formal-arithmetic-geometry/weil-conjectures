## Worker report

The retained module is `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`.
Its two postponed statements together render the node:
`WeilConjectures.frobeniusCohomologyTransport_isIso` states invertibility;
`WeilConjectures.frobeniusCohomologyTransport_natural` states naturality.
Every theorem proof is `sorry`. No definition contains postponed data.

The saved packet's first dry run was performed before this repair. Its
preflight found a stale recorded signature and a missing parenthesized
blueprint tag in the declaration docstring. Both were repaired. The required
self-check also found that the saved statement omitted point transport at
algebraically closed coefficients, all separate exchange-isomorphism clauses,
and an explicit naturality statement. These have been supplied; the DAG's
mathematical statement is unchanged.

Hypotheses, individually:

* `D : FiniteFieldDatum.{u}` supplies `p,a,q,k₀,k`, primality, `a ≥ 1`,
  `q = p^a`, the cardinality of `k₀`, and its chosen algebraic closure `k`.
* `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` supplies the different coefficient
  prime. Invertibility on the geometric fibre and point is derived from `hl`.
* `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]`,
  `[QuasiCompact Y₀.hom]`, and `[IsSeparated Y₀.hom]` say separated finite
  type over `k₀`. There is no properness assumption on `Y₀`.
* `D.geometricFiber Y₀` is the stated `Y`, and its `.hom` is `a_Y`.
  `galois D Y₀` is its recorded geometric Frobenius. `frobeniusPointIso D`
  is the specified `g_s`.
* `Ω : Type v` with its `Field`, `Algebra ℚ_[l]`, and `IsAlgClosure` instances
  is the chosen algebraic closure; `v` is independent of the scheme universe.
  Each quantified `E : Type u` with `Field`, `Algebra ℚ_[l]`, and
  `FiniteDimensional` is a finite coefficient extension. An inclusion into
  the closure in the descended naturality square is the canonical
  `frobeniusCohomologyStageEmbedding` for each actual finite stage. The other constructions depend only on the coefficient extension,
  so do not require an embedding as an additional hypothesis.
* `(n : ℕ)` denotes the positive exponent `n + 1`, with `Nat.succ_pos n`.
  This includes every exponent allowed by the node, including exponent one.
* `K`, `K₁`, and the variables of the naturality theorem belong to precisely
  the recorded bounded constructible coefficient categories on `Y`. `Kp`
  and `N` belong instead to the corresponding categories on `Spec k`.
* `c₀` and `c₁ : Compactification Y₀.hom` retain the model compactification
  required by the compact-support construction. They are presentation data;
  independence is the already recorded compactification-coherence interface.

Conclusions, clause by clause:

1. Point transport: `IsIso (frobeniusPointTransportFiniteConstructible ... Kp)`,
   `IsIso (frobeniusPointTransportIntegralConstructible ... Kp)`, and
   `IsIso (frobeniusPointTransportRational ... Kp)` state clause 1 in the
   finite/integral/rational target categories. For each algebraically closed
   point object `N`, the first conjunct states `IsIso` of its own rational
   point transport after `frobeniusCohomologyCoefficientExtension` along its
   canonical coefficient-stage inclusion. This is the specified stagewise
   point transport realized in `D(Ω)`, with the canonical size transport.
   The rational clause also gives invertibility before this realization. The
   additional quantified `frobeniusPointTransportQbar D l hl Ω' N` clause
   states invertibility in the exact recorded `PointFdQbar` target too, for
   every closure model `Ω' : Type u`. The independent-universe realization
   does not restrict the universe of the initially specified closure.
2. Exchange: the five `frobeniusCohomology*Exchange` helpers expose
   precisely the exchange factors in the recorded transports. Their
   `IsIso` clauses apply separately to ordinary and compact support in
   each coefficient realization. The finite ordinary helper is the
   recorded `finiteExchange` at the actual structure map to `Spec k`;
   the compact helper is `finiteCompact` with precisely the retained
   compactification and middle Frobenius, conjugated by the recorded
   `openSquareDerivedPullbackModel` comparisons exactly as in the original
   compact transport. Thus it also uses the intrinsic derived-pullback
   coordinates of the statement. The integral/rational/common-stage
   helpers apply `modelExchange`, `modelRationalExchange`, and
   `commonStageExchange` to `frobeniusCohomologyDirectModel` or
   `frobeniusCohomologyCompactModel`. All these helpers have the actual
   `Spec k` as their base, matching the node's objects literally. They
   merely expose existing canonical factors; they do not construct a
   different mate or select an arrow. Finite-level `IsIso` is stated
   in the ambient category on the full constructible domain; a
   full-subcategory inclusion reflects isomorphisms.
3. Cohomology transport: both projections of
   `frobeniusCohomologyTransport` and its finite/integral/rational versions
   are asserted `IsIso`. For every `i : ℤ`, both projections of the
   corresponding `frobeniusCohomologyMap*` are asserted `IsIso` as well.
   `frobeniusCohomologyTransport_natural` states the commuting square for
   every finite, integral, and rational morphism, for both support choices.
   The five named functor/pullback helpers are literal compositions of the
   recorded operations, exposing their existing maps for these equations.
   They do not introduce new categories, operations, or selected arrows.
   The final conjunct now quantifies over arbitrary `f : K ⟶ L` with
   `K L : generalAlgebraicallyClosedConstructibleCategory l Ω Y`. It states
   the commuting square for the actual `frobeniusCohomologyTransport`,
   separately for `.1` (ordinary) and `.2` (compact support). Its horizontal
   arrows are `frobeniusCohomologyQbarMap` and
   `frobeniusCohomologyQbarPullbackMap`: these are the maps of the actual
   descended RΓ/RΓ_c functors and their composites with the recorded
   `commonStageDerivedPullback`, conjugated only by the explicit object
   equalities identifying their endpoints with the transport values.
   These are full Pair-category maps, including morphisms whose endpoints
   have different coefficient fields, rather than scalar images of one
   rational square. Applying H^i gives the induced degreewise squares.

Dependency declarations used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`.
* `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`.
* `Sheaf.SixFunctors.FrobeniusCohomologyTransport`: the four transport pairs,
  their degreewise maps, `frobeniusCohomologyModelMap`, both support models,
  `frobeniusCohomologyCompactification`, and the exact coefficient extension.
* `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteSections`,
  `pointIntegralFibre`, `pointRationalFibre`, and the stagewise point fibre.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, and `rationalDerivedPullback`.
* `Sheaf.Paper.SfCommonStageDirectImage`: the recorded common-stage
  direct-image interface, retained by the transport dependency's imports.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
* `Sheaf.Paper.CommonStageCompactWeilCohomology` and its public ordinary/
  compact interface: all coefficient cohomology interpretations.
* `Sheaf.Paper.FrobeniusGeometricExchange`: the finite/integral/rational/
  common-stage exchange wrappers; `Sheaf.Paper.FrobeniusSquareExchange`:
  `modelFunctor`, `modelRationalFunctor`, and their natural exchanges.
  `Sheaf.Paper.SystemOperationExchangeRealization` supplies the actual
  `finiteExchange` and `finiteCompact` factors, reused without change.
* `Sheaf.SixFunctors.FrobeniusPointTransportNatural`:
  `WeilConjectures.frobeniusPointTransport_natural`. This is a proof-only
  reference: its import is non-public, and it is absent from `stmt_deps`.
* The convention-only `def-weil-scheme-morphism-properties` supplies the
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` classes.

The exchange and cohomology-functor helpers install only inherited
prime-invertibility and scheme-over-base proof instances, using the same
terms as the recorded transport definitions. They introduce no new geometric
hypothesis and no selected categorical data.

Edge cases checked: exponent one (`n = 0`), all integer degrees (negative,
zero, and positive), empty schemes, zero objects, identity morphisms, repeated
coefficient stages, and morphisms represented after a proper coefficient-stage
enlargement. No nonemptiness or nonzero assumption is imposed. Scheme and
coefficient-closure universes are independent in both invertibility and the
realized naturality square. Only the finite small coefficient models use
`Type u`, as in the recorded coefficient-category construction.

Searches retained from the earlier packet:

* `msearch.py ... leanfinder "transport of cohomology along geometric
  Frobenius is an isomorphism"`: eight unrelated Frobenius/isocrystal hits;
  no matching cohomology-transport theorem.
* `msearch.py ... loogle "IsIso Frobenius cohomology transport"`: no hits;
  the service reported that `IsIso` was unknown.
* `msearch.py ... grep "Frobenius.*cohomology|cohomology.*transport"
  Mathlib/AlgebraicGeometry`: no matches.
* `rg` in upstream `WeilConjectures/` and project `lean/Sheaf/`: canonical
  transport definitions and unrelated actions; no invertibility theorem.
* Current targeted `rg` for point/cohomology naturality located the landed
  `FrobeniusPointTransportNatural` interface, now imported and reused.
  `OrdinaryCompactCohomology` has the existing objectwise section values;
  the new named functor compositions expose the maps already used by the
  transports, without replacing those values or their operations.

No `STATEMENT-DISPUTED` flag, new node, or mathematical statement correction
is needed. The canonical realization helpers belong to this item, as described below. The main docstring records all nine proof
steps of the DAG node; the naturality theorem records the pasted-square proof.


## Return repairs

F1 (H2): removed `lem-weil-frobenius-point-transport-natural` from the item's
statement dependencies and demoted its import to a proof-only `import`.
The item's `stmt_deps` now equals current main verbatim. The proof reference stays.

F2 (H3): replaced the final conjunct of
`frobeniusCohomologyTransport_natural`. It now quantifies over the entire
algebraically closed Pair category and directly uses both components of
`frobeniusCohomologyTransport`. `frobeniusCohomologyQbarFunctor` is uniquely
specified on objects and on every common-stage representative. Its realization
comparison is the composite of the localized integral operation scalar mate,
the recorded point-fibre scalar comparison, the balanced tensor tower, and the
recorded transition identification. Thus no arrow or natural isomorphism is
chosen without its canonical normalization. `frobeniusCohomologyQbarPullback`
is exactly the recorded common-stage geometric pullback. The two map helpers
conjugate these functors' maps by `frobeniusCohomologyQbarSourceEq` and
`frobeniusCohomologyQbarTargetEq`; these are the defining equality clauses,
not extra mathematical assumptions.

## Canonical realization helpers

The 21 realization helpers are in the item module
`Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`, together with the naturality
statement that needs them. The landed dependency module
`Sheaf.SixFunctors.FrobeniusCohomologyTransport` remains publicly imported,
and all transport values are retained. Its objectwise Q̄ℓ
transport supplied no RΓ/RΓ_c map on arbitrary Pair-category morphisms in the
independent-universe derived Ω-module target. The item module supplies precisely
that missing interface, preserving the literal source/target values by explicit
equalities. Its existence-unique specifications determine all data: balanced
pure tensors determine the ordinary size-compatible tensor tower; localization
of the original integral mate determines the rational operation comparison;
and the full representative formula determines each Q̄ℓ cohomology functor.
Theorems are postponed with proof plans, while definitions take their data only
from these unique characterizations or compose existing canonical maps.
The rational RΓ/RΓ_c helper is also in the item module, without a change of
mathematical data. No dependency node or dependency source file is delivered.

Additional searches: LeanFinder for "cohomology functor descent to common
coefficient stage with scalar extension to an algebraic closure" returned eight
group-cohomology results, none matching. Loogle for
"StageSystem.Morphism, mapDerivedCategoryCompIso, ModuleCat.extendScalarsComp"
returned no matches (unknown identifier `StageSystem.Morphism`). Targeted `rg`
in upstream and side sources found no `frobeniusCohomologyQbarFunctor` or
`frobeniusCoefficientTower`. The existing StageSystem, rational point scalar,
coefficient inclusion, and geometric pullback declarations were read and reused.

Self-check: coefficient fields may be repeated; identity inclusions use the same
balanced tensor formula. Different original stages and subsequent proper
extensions are covered by every common-stage representative in the defining
specification. No universe equality is imposed (`u` and `v` remain independent).
Every square uses the retained compactification, with no properness assumption
on Y. The finite, integral, rational, and invertibility clauses were retained.


## Saved-packet compilation repair

The required initial dry run failed in the saved helper module: the explicit-base
pure-tensor notation needed the `ChangeOfRings` scope, the derived tower comparison
needed the same explicit `HasDerivedCategory` instances as the original transport,
and stage realization needed an explicit target type and its small-field algebra
instance to prevent failed dependent instance inference. These are now supplied.
`frobeniusCoefficientLiftHom` names the existing ULift-conjugated ring homomorphism,
so the tensor normalization states the precise scalar actions on both sides.
The two equality projections are definitions of proof terms already specified by
the uniqueness theorem; their local `linter.defProp` setting permits these projections
without claiming a newly proved stage-2 theorem.

The self-check reread the returned F1/F2 obligations against the saved Lean:
`stmt_deps` equals current main and the point-naturality import is proof-only.
The fourth naturality conjunct binds every `K`, `L` and `f : K ⟶ L` in the full
`generalAlgebraicallyClosedConstructibleCategory`, independently of the finite
extension `E` bound in the earlier conjuncts. Both sides contain the actual retained
transport, for ordinary and compact support. The horizontal maps descend on every
common-stage representative, using normalized scalar comparisons and their
inverses, and the pullback is the recorded common-stage geometric pullback.
Consequently the square includes distinct original coefficient stages and arbitrary
further enlargements; it is no longer a mapped copy of one rational-stage square.
The item node differs from current main only in `lean`; the item publicly imports
the original transport module and retains all original objects.


## R1 repair: preserve the landed dependency binding

Applied the maintainer's option (b). Moved all 21 declarations from the saved
`FrobeniusCohomologyTransportFunctors` module into the item module, preserving
their signatures and bodies and assigning their docstring blueprint tags to
`lem-weil-frobenius-cohomology-transport-iso`. Added the public
`Sheaf.Paper.FieldDerivedScalarTower` import to the item. Removed the separate
helper file and the dependency-node override from the packet. The item's
`lean.declarations` lists both the 21 moved helpers and its original declarations.

The live dependency record remains NB's binding to
`Sheaf.SixFunctors.FrobeniusCohomologyTransport`, with
`WeilConjectures.frobeniusCohomologyTransport` as its principal declaration and
all 18 landed declarations retained. No source or record of that dependency is
changed, so its existing consumers `TraceFormulaLocalFrobeniusOperator`,
`FrobeniusExchangeDegreeZero`, and `CompactFrobeniusTransportComposition` keep
their original import and declaration interface.

Self-check: the item's mathematical statement, statement dependencies, both
concluding theorem signatures, and all helper bodies are unchanged. F1's
proof-only point-naturality import and F2's full Pair-category naturality
quantification, canonical scalar comparisons, HEq object pins, and recorded
`commonStageDerivedPullback` are retained. No new node or statement correction
is needed.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
