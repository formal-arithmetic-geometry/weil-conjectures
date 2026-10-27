## Worker report

The delivery states `WeilConjectures.sfCompletedMateDomain` in
`Sheaf.Paper.SfBcCompletedMateDomain`. Its proof is the sole `sorry` in the module.
There are two supporting real definitions, with no new choices:
`sfCompletedMatePushComparison` is `eqToIso` of the equality of the canonical
completed coefficient maps, and `sfCompletedFiniteProfile` expands the four finite
constructibility/vanishing clauses. They belong to the normalization and landing
assertions of this node; neither introduces an independent mathematical notion.

The source read is the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-functor-package.proof.md`, clause (4). The node's six proof
steps, including the refinements from its cited proper/smooth theorems, are reproduced
in the theorem docstring. No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, characteristic p | `D : FiniteFieldDatum.{u}` and its field `D.k`; the finite cardinality and algebraic-closure data are retained by that published structure. |
| Prime l different from p | `(l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)`. |
| Finite extension E/Q_l | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| Its valuation ring, uniformizer, and all positive quotients | The existing `pbcIntegralDatum l E`, using `PbcIntegralRing l E` (the canonical ULift of the valuation ring) and its uniformizer; `ProEtale.PbcQuotient ... n` is R/(varpi^(n+1)). No coefficient datum is replaced by an arbitrary ring. |
| Four separated finite-type k-schemes | The four structure maps `aX`, `aY`, `aX'`, `aY'` to `Spec (.of D.k)`, each with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. |
| Four separated finite-type k-morphisms | `f`, `g`, `g'`, `f'`, each with those three morphism properties; `_hf`, `_hg`, `_hg'`, `_hf'` are the four equations over k. |
| Chosen Cartesian square | `sq : ChosenCartesianSquare g' f' f g`. |
| Specified exchange, with completed coefficients and pullback | The actual `sbcExchangeApp l E (exchangeTransposeSquare sq)`, defined by the existing unit/theta/counit composite; its operations use the completed coefficient limit and strict-tower completed pullback. The transpose changes only square-label convention. |
| Proper f and derived-complete K | The first conjunct begins `IsProper f → ∀ K : PbcComplete l E X`. Completeness is membership in the published intrinsic full category, with no boundedness assumed. |
| Compatible bounded-below etale-origin witnesses | `PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum l E) K.obj`, retaining the actual witnessed tower and canonical transition normalization. |
| Ambient completed mate is invertible | `IsIso (sbcExchangeApp ... K)`. |
| Agreement with finite-level mates under the canonical comparisons | The `∀ n` equality uses `sbcReduction`, `sbcPushReduction`, `sbcPullReduction`, and `sbcFiniteExchangeApp`, with exactly the right-to-left square relabelling prescribed in proof step 2. |
| Agreement with the completed ordered derived-limit exchange | The next equality uses `sbcStrictSourceComparison`, `completedTowerRlim`, `sbcStrictExchange`, and `sbcStrictTargetComparison`. The following equality explicitly identifies this with `(pbcIntegralDatum l E).completedExchange sq K.obj`, conjugated by the existing resolving-counit-normalized `cbcDatumCompletedTransport` and the identity-coefficient-map direct-image comparison. Expanding `completedExchange` is precisely Rlim(towerH), then Rlim(towerV'), then inverse directImageRlimIso, in that order. These are specified comparisons, not existential endpoint isomorphisms. |
| Proper constructible landing for constructible K | The implication with premise `PbcIsBoundedConstructibleComplete X ... K.obj` supplies `hS` and `hT` for the actual two complete endpoints, and `IsIso (ObjectProperty.homMk ... (sbcExchangeApp ... K).hom)`. The same arrow and inverse are retained by the full subcategory. |
| Smooth g and constructible-complete K | The second conjunct begins `Smooth g → ∀ K : PbcIntegralConstructible l E X`. Its property already contains compatible bounded-below etale origins, so none is erased or replaced by a new bounded-origin assumption. |
| Every canonical reduction has bounded constructible etale origin | `∀ n, ∃ L : Etale.BoundedConstructibleDerivedCategory ... X, Nonempty (...)`. The isomorphism identifies canonical reduction with the published comparison inverse image followed by the canonical function-coefficient realization. This is the essential-image condition, not a claim that every arbitrary chosen bounded-below witness is bounded constructible. |
| Smooth ambient invertibility | `IsIso (sbcExchangeApp ... ((pbcConstructibleInclusion l E X).obj K))`. There is no finite-output-bound premise on this conclusion. |
| One interval a ≤ b for all four finite systems | `∃ a b : ℤ, a ≤ b ∧ ∀ n`, followed by the four `sfCompletedFiniteProfile` clauses at corners Y, Y', X', Y', for push f; pull g after push f; pull g'; push f' after pull g', respectively. The helper requires constructible cohomology in every degree and zero cohomology outside [a,b]. |
| Conditional smooth constructible landing and same isomorphism | Only the common-interval premise implies the final existential `hS`, `hT` and `IsIso (ObjectProperty.homMk ... (sbcExchangeApp ...).hom)`. |
| Smooth input/output corners and index shift | The transposed square has input X and output Y'; every `n : ℕ` denotes positive quotient n+1, exactly m ↦ m+1. |

The six-functor operation datum is used as the source's convention for the named
operations. No arbitrary operation functors or comparison isomorphisms are added as
hypotheses. Every displayed exchange is the canonical ambient complete mate.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`
  and its inherited finite-field conventions, especially `FiniteFieldDatum`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its chosen pullback and projections.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.exchange`; the
  completed specialization is the identical unit/comparison/counit formula in
  `sbcExchangeApp`, not a private exchange construction.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, its completed ring,
  projections and canonical reductions, reexported through the completed operations.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded module reexports the integral
  strict completed-pullback construction used here; this statement does not concern
  its Qbar specialization `pbcQbarCompletedPull`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` and its imported
  `Sheaf.Paper.RingedEtaleOriginWitness`: the retained bounded-below pair and canonical
  constant/function coefficient presentation. Compatible towers are the published
  `PbcHasCompatibleEtaleOrigins`, built from those witnesses, not new origin data.
- `Sheaf.Paper.IntegralUniformCoefficient`: the recorded
  `PbcIsBoundedConstructibleComplete` / `PbcBoundedConstructibleComplete`
  specialization. `PbcIntegralConstructible` specializes the same predicate to the
  canonical ULift valuation ring, as already used by the completed-operation theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the canonical fixed-scalar module
  realization; `ProEtale.comparisonUpperStar` is the actual etale-to-pro-etale inverse image.
- `Sheaf.Paper.SbcCompletedOperations`: `sbcPull`, `sbcPush`, `sbcExchangeApp`,
  `sbcReduction`, the finite operations/comparisons and
  `sbcCompletedOperations_linear_natural_exchange`, `sbcCompletedExchange_strictLimit`.
- `Sheaf.Paper.CompletedBaseChangeMap`: `AdicCoefficientDatum.completedExchange`,
  the exact ordered composite, and its proper-domain `completedBaseChangeMap`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`: `cbcDatumCoefficient_eq` and
  `cbcDatumCompletedTransport`, fixed by the universal resolving counit;
  owned by `def-sf-completed-pullback-presentation-transport`, which cites the
  strict-tower normalization node `def-cbc-completed-pullback-counit-transport`.
- `Sheaf.Paper.AdicSmoothBaseChange`: `sbcAdicFiniteCohomology`, owned by `def-sf-adic-finite-cohomology`, and
  `WeilConjectures.adicSmoothBaseChange` (proof dependency only).
- `Sheaf.Paper.ExchangeFunctoriality`: reuse only the already published real
  definition `WeilConjectures.exchangeTransposeSquare`, retaining the chosen pullback
  projections, owned by `def-sf-chosen-cartesian-square-transpose`; no theorem of
  that downstream package is assumed.

The remaining stated proof dependencies are imported without `public`: finite-type
geometry/fibre bound, Mathlib's proper pullback instance (the proper-base-change leaf's
`mathlib_match`), standard perfect quotients, complete pro-etale proper base change,
constructible complete proper base change, uniform reduction criterion and finite-ring
constructible derived origin. The scheme-conventions dependency defines no new object
and has no module. The already landed completed-operation and completed-base-change-map nodes remain
in stmt_deps. The completed-operation theorem is a genuine dependency: sbcPull/sbcPush
use its completeness result and sbcAdjunction/sbcTheta/sbcStrictSourceComparison are
chosen from its asserted uniquely normalized interfaces. In contrast, the adic smooth
and completed open-exchange theorems are no longer statement dependencies merely
because their modules contain definitions. Their needed helpers are now owned by the
three existing:true definition nodes listed below. The already landed
`def-cbc-completed-pullback-counit-transport` is also cited directly. The smooth theorem
remains a proof dependency (Step 6); the completed open-exchange theorem is unused.
No dependency record, node statement, proof or proof-dependency list is changed.
The transpose is cited through its new definition owner, following the explicit
alternative in the return; no functoriality theorem is assumed.

Edge cases checked before and during writing: empty corners are allowed (no nonempty
scheme or surjectivity condition); zero complexes and zero reductions satisfy the
profile; a=b is allowed; every positive quotient including varpi^1 occurs at n=0;
no degree-zero-only restriction is imposed; proper inputs can be unbounded and
nonconstructible; smooth ambient invertibility remains unconditional on the four
finite bounds; no assertion strengthens an arbitrary chosen etale witness; all
isomorphisms in the constructible categories have the same underlying arrow.
The site object universe is u+1 and its morphism universe u; coefficient modules are
in u+1. The helper's explicit standard `HasDerivedCategory` only fixes the published
localization instance and does not identify these two site universes.

Searches for existing declarations:

- msearch leanfinder: “Completed integral proper and smooth base change for the
  canonical adjunction mate with finite reduction normalization and conditional
  uniformly bounded constructible landing”: eight hits, led by scheme normalization
  and integral-morphism base-change facts; none states this assertion.
- msearch leansearch: “Completed proper base change for integral pro etale sheaves
  with compatible bounded below etale origins”: eight hits, properness stability,
  etale base change and related geometric facts; none states the completed mate theorem.
- msearch loogle: `CategoryTheory.Adjunction, "mate"`: twelve generic mateEquiv,
  unit/counit and pasting declarations; no geometric/completion/landing assertion.
  An initial query `CategoryTheory.Adjunction, IsIso` returned no hits because the
  short identifier IsIso was unknown; the qualified mate query above replaced it.
- msearch grep: `completed.*exchange|adic.*base.?change`: no Mathlib matches.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: completed-mate/exchange, this node id,
  and the three proposed declaration names. Existing completed exchange constructions
  and the individual proper/smooth theorems were inspected and reused; no existing
  theorem contains this precise joint domain, reduction, ordered-map, essential-image
  and landing statement. The three proposed names have no existing declaration.

Validation: scompile.py compiled the sandbox and final library-path module cleanly
on the server (8.7 s and 8.8 s); every theorem proof in this delivery is `sorry`.
An initial square-orientation elaboration was fixed by reusing the existing chosen
transpose, now cited through its definition owner. A universe ambiguity introduced by a broadly imported generic localization
instance was fixed by passing `HasDerivedCategory.standard _` explicitly in the
finite-profile helper. No source or launcher file was edited and no global build run.

## Second reading by Q58

A separate final pass reread the node and the final signature clause by clause using
the table above. It checked the direction of both transposed arrows and both ordered
comparison maps, the two full-subcategory endpoint binders and the underlying arrow,
the four smooth finite systems, the n=0/positive-level-one case, and the absence of a
uniform-bound premise on smooth ambient invertibility. This pass found and corrected
the initial misuse of `CommSq.flip` (which forgets the chosen Cartesian data) and
replaced it by the published chosen-square transpose. It also checked that the profile
helper fixes only a derived-localization instance, with no extra universe equality.
There is no mathematical statement correction or dependency-record repair. The
returned dependency-ownership defects are repaired by the three existing:true
nodes below. In this repair pass I reread their statements against the published
signatures and bodies: finite cohomology imposes no bound or origin condition;
the completed transport is exactly the Rlim whiskering of the uniquely normalized
strict-tower comparison; the coefficient equality retains all finite projections;
the transpose composes the chosen identification with symmetry and swaps both
projection equations. The added dependencies refer to these exact definitions,
not to their containing theorem statements. No additional module or private copy
is introduced. This is the worker's final rereading, not a claim that a second
agent was started; the dispatch brief prohibits other agents and assigns the
independent reading to the maintainer.


## New nodes

`def-sf-adic-finite-cohomology` owns the existing
`WeilConjectures.sbcAdicFiniteCohomology` in `Sheaf.Paper.AdicSmoothBaseChange`.
For a prime l, finite E/Q_l, any scheme W, n : ℕ and derived finite-coefficient J,
it is restriction of H^i(J) along `pbcLevelConstantComparison`, with no finiteness,
boundedness or origin assumption. This is the finite-output interpretation in the
current blueprint prop-functor-package proof clause (4), rendered by the published
helper at AdicSmoothBaseChange:60. Its definition dependencies explicitly include
the finite extension, adic datum, constant/function comparison and cohomology owners.
The three msearch queries recorded verbatim in the node ran on 2026-10-24:
LeanSearch returned condensed/cochain/continuous-cohomology constructions;
LeanFinder returned truncation/cohomology and differential constructions;
Mathlib grep of sbcAdicFiniteCohomology returned 0 hits. Local DAG and source grep
found this helper only under the adic smooth theorem; no definition node owns it.
Blueprint identifier search returned 0 matches. The existing:true record reuses
that exact definition and introduces no module or declaration.

`def-sf-completed-pullback-presentation-transport` owns the existing
`AlgebraicGeometry.Scheme.cbcDatumCompletedTransport` and helper
`AlgebraicGeometry.Scheme.cbcDatumCoefficient_eq` in
`Sheaf.Paper.CompletedOpenExchangeTransport`. For any adic datum and scheme morphism,
the coefficient identity is fixed by every finite projection. The transport is
`isoWhiskerLeft (completedReductionTower T d)` of the right whiskering of the
unique counit-normalized strict-tower comparison with `completedTowerRlim d S`.
The node cites `def-cbc-completed-pullback-counit-transport`, which owns
`cbcDatumTowerTransport` and its unique resolving-counit characterization, as
well as the adic datum, completed pullback and specified Rlim definition owners.
The source is clause (4)'s canonical completed comparisons (Stacks 099N) and the
published declarations at CompletedOpenExchangeTransport:433 and :566.
The three logged msearch queries ran on 2026-10-24: LeanSearch returned generic
pullback/adjunction comparisons; LeanFinder returned ring/module adic completion
lemmas; Mathlib grep of cbcDatumCompletedTransport|cbcDatumCoefficient_eq returned
0 hits. Whole DAG and project source grep found only the containing theorem node,
not a definition owner. Blueprint identifier search returned 0 matches. This
existing:true record retains the specified canonical construction, including its
coefficient normalization, instead of citing completed open-exchange invertibility.

`def-sf-chosen-cartesian-square-transpose` owns the existing
`WeilConjectures.exchangeTransposeSquare` in `Sheaf.Paper.ExchangeFunctoriality`.
For any chosen Cartesian square it swaps the two pairs of arrows and composes
the chosen pullback identification with `pullbackSymmetry`. Its projection proofs
are the original opposite projection proofs, so no chosen Cartesian data is lost.
The source is prop-functor-package clause (4)'s square relabelling and the same
relabelling in current fix-lem-exchanges clause (3), with the published constructor
at ExchangeFunctoriality:1343. Its only definition dependency is
`def-weil-pbc-cartesian-square`. The three logged msearch queries ran on 2026-10-24:
LeanSearch found generic `IsPullback.flip` and `Square.flip`, which do not return
this project's chosen-square structure; LeanFinder found scheme pullback-gluing
maps; Mathlib grep of exchangeTransposeSquare returned 0 hits. DAG/source grep
found only the containing fix-lem-exchanges theorem node as a record user, and the
published real definition. Blueprint identifier search returned 0 matches. The
existing:true record uses that exact definition and satisfies the return's explicit
alternative to changing the square orientation; no private transpose is introduced.

## Repair of immutable head 65aba07a0bb8

The initial required saved-packet dry run passed as c3945b8f2e0, confirming the
packet still compiles on the current published library. The independent return's
H2 findings still applied despite that mechanical pass; the saved packet was
retained and changed as follows, rather than rebased and repushed unchanged.

1. Retained `lem-sbc-completed-operations-linear-natural-exchange` as a genuine
   statement dependency, as the independent reader confirmed.
2. Replaced `sbc-thm-adic-smooth-base-change` in stmt_deps with
   `def-sf-adic-finite-cohomology`. The smooth theorem remains in proof_deps.
3. Replaced `lem-cbc-completed-extension-zero-comparison` in stmt_deps with
   `def-sf-completed-pullback-presentation-transport`, owning precisely the requested
   coefficient equality and completed comparison, and added
   `def-cbc-completed-pullback-counit-transport` as requested.
4. Chose the return's alternative of citing a definition owner for the existing
   `exchangeTransposeSquare`: added `def-sf-chosen-cartesian-square-transpose`.
   The `ExchangeFunctoriality` import therefore has a real cited definition owner.
   The old square binder and all exchange components remain unchanged.

The current read clone's item has the original eight statement dependencies and no
Lean record. Against that current base, the repaired packet only adds the needed
recorded dependencies and new definition nodes; it does not replace an intervening
landing. Delivery tooling performs the current-base commit construction and rebase.

Final self-check of the repair: the exact old and new Lean theorem signatures agree;
all source-backed hypotheses and clauses in the Worker report table still match,
including the proper unbounded case, smooth ambient conclusion before the optional
common interval, the four finite objects in order, and the positive quotient shift.
The new nodes' formulas were reread against the complete signatures and bodies of
the three published definitions and the coefficient-equality lemma. Each new node
has existing:true, no private copy, empty proof/proof_deps, explicit definition
citations and the required real search records. The transpose retains both chosen
projection equations; neither `CommSq.flip` nor an arbitrary isomorphism is used.
This is a self-check by the dispatched worker, with no other agent started.


Repair validation: scompile.py compiled both the sandbox probe (11.7 s) and the
library-path module (13.1 s) without errors or warnings. The three existing:true
nodes add no Lean files. The theorem signature is byte-for-byte the saved reviewed
signature; the only Lean source change documents the three definition owners.

The first repaired-packet dry run identified one metadata requirement absent from
the brief's field list: each new node must have import_flags. Added import_flags: []
to all three new records. Its advisory about the completed-operation theorem is
covered by the independent return's explicit PASS on that genuine dependency.
