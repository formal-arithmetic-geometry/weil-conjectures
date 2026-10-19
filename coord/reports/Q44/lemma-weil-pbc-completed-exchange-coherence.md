## Worker report

Group Q44, stage 2, 2026-10-16. Main module:
`Sheaf.Paper.CompletedExchangeCoherence`.

This worker refreshed the existing attempt against the current read-only DAG,
source modules and published source queries. The delivery contains twelve modules:
the coherence statement and eleven prerequisite interfaces. All twelve node copies
change only `lean`. There is no new definition node or statement correction.
No Lean source was changed during this refresh. Earlier attempt logs and the full
inherited report are archived under `scratchpad/`; the earlier independent second
reading is preserved below for provenance. The next reader must check the current
packet before delivering. Nothing is pushed by this worker.

Source: the blueprint's actual order-1348 page in chapter sec-proper-base-change,
unit sk-thm-properbasechange, and its order-1338 completed-map definition. The
blueprint explicitly supplies completed coherence beyond Stacks 09C9. Its seven-step
DAG proof is retained in the theorem docstrings: constant/completed comparison,
normalization of the strict tower mate, mate-pasting before applying Rlim, Rlim
functoriality, normalized intermediate comparisons, cancellation for identity and
pasting, and naturality for arbitrary morphisms. Derived evaluation is never
assumed faithful on morphisms.

Each hypothesis and clause is rendered as follows:

| Node ingredient | Lean rendering |
| --- | --- |
| Cartesian square of schemes | Explicit `Scheme.{t}` objects and all four arrows; `ChosenCartesianSquare g' f' f g` retains commutativity and the chosen fibre-product identification. |
| Commutative Noetherian adic datum, finite generation of I, additive torsion of A/I, finite perfect positive quotients | `A : Type (t+1)`, `[CommRing A]`, `d : AdicCoefficientDatum A`; the inherited `CompleteCoefficientDatum` fields and `quotientFinite` retain every condition. |
| Actual finite and completed coefficient sheaves | `d.finiteRing T n` reuses `reductionCoefficient T d n`; `d.completedRing T` reuses the actual `completedReductionCoefficient T d` limit of function coefficient sheaves. Constants and completed coefficients are distinguished. |
| Every positive exponent | Lean `n : ℕ` means exponent `n+1`, including the first positive level. Quotient actions remain in `d.reduction T n` until explicit restriction. |
| Small pro-etale site | Site objects remain in t+1, morphisms in t; coefficient/module size is t+1. No universe equality is imposed. |
| Properness and arbitrary base change | `[IsProper f]`; no extra restriction on g. Vertical pasting includes `[IsProper e]` for the other proper map. |
| Derived-complete K | `hK : d.TowerComplete X K`, namely invertibility of `d.completionUnit X K`. The quotient augmentation reuses `completedReductionTowerUnit d X`. `towerComplete_iff_intrinsic` retains the comparison with intrinsic Koszul completeness for every generating list and representative. |
| Retained etale-origin data at every finite level | `W : ∀ n, FiniteEtaleOriginWitness X (A ⧸ d.ideal^(n+1)) ((d.reduction X n).obj K)`. Each witness contains a bounded-below etale object and a specified comparison isomorphism after canonical exact coefficient transport. No uniform bound or inter-level witness compatibility is required. |
| The specified completed exchange | `completedBaseChangeMap` is precisely `completedExchange`: Rlim(h), then Rlim(v'), then inverse of `directImageRlimIso`. Its source identification is definitional; v' is the strict projection-formula realization, with its finite evaluation stated in `fourTowers_compatibility`. |
| Naturality in K | `completedExchange_naturality` binds arbitrary `k : K ⟶ H`, complete K and H and independent WK and WH. Source-functor(k) followed by Ex(H) equals Ex(K) followed by target-functor(k). |
| Identity with horizontal identity arrows | `completedExchange_identity_horizontal` equals the canonical completed identity comparison on Rf_*K followed by Rf_* of its inverse on K. |
| Identity with vertical identity arrows | `completedExchange_identity_vertical` equals the canonical right-adjoint identity comparisons on both sides of completed pullback. |
| Horizontal pasting | `completedExchange_horizontal`: `completedPullComp h g`, pullback of the first exchange, the second exchange at the intermediate pullback, then pushforward of inverse `completedPullComp h' g'`. |
| Vertical pasting | `completedExchange_vertical`: completed pullback of inverse `pushComp f e`, lower exchange at Rf_*K, pushforward of upper exchange, then `pushComp f' e'`. |
| Canonical associativity/unit maps | `pullComp` is the published canonical derived comparison with its actual coefficient transport; `pushComp` is its adjunction conjugate. `completedPullComp` and `completedPullId` are uniquely fixed by ordinary completion-unit equations. `modulePushId` is uniquely fixed on each section. |

The two pasting equations use the ambient extension `completedExchange` of the
same ordered construction at intermediate vertices. The outer input still has
properness, completeness and every retained finite witness. This avoids imposing
extra witness choices or their compatibility at intermediate vertices.

The dependency modules and their declarations are listed below. Further published
interfaces read and reused include:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `ChosenCartesianSquare`.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`, `AdicCoefficientDatum`, and
  `Sheaf.Paper.CompleteCoefficientDatum`, `CompleteCoefficientDatum`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`,
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedAdjunction` and their
  actual module functors and localization factors.
- `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`,
  `proEtaleAmbientRingedExchange`, `proEtaleCanonicalDerivedPullbackComparison`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`,
  `proEtaleConstantComparison`, `proEtaleProfiniteComparison`, and
  `proEtale_profinite_coefficient_inverse_image`, with all projection laws.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`, exact scalar
  restriction and the normalized pullback/direct-image comparisons.
- `Sheaf.Paper.CompletedTowerPullback`, `completedReductionTowerUnit`, and
  `Sheaf.Paper.IntrinsicCompletion`, `IsDerivedCompleteIntrinsic`.
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`, the specified counit mate.
- The published independent-coefficient K-flat, resolution and derived-change
  interfaces; they are imported unchanged.

Definitions have actual data, uniquely characterized maps, or universal derived
pairs. Every postponed theorem has `sorry`, a source/proof docstring and an entry
in its owning node's `lean.declarations`. The current published 686-line
`AdicCoefficientDatum` source was fetched using `scompile.py --source` and is
preserved verbatim as the prefix of the delivered 957-line module.

Edge cases checked: empty schemes; zero objects and maps; identity maps and both
identity square orientations; arbitrary chosen Cartesian identifications; zero
rings, I=top, and I=0 whenever the datum's quotient/perfectness conditions hold;
empty generating lists where applicable; arbitrary characteristic; unbounded K;
unrelated lower bounds and witness choices at different levels and for K and H.
There is no nonemptiness, connectedness, affine, scheme Noetherianity, uniform
bound or extra flatness hypothesis. No statement is disputed.

Fresh searches through the prescribed msearch.py wrapper:

- LeanFinder, “Completed pro etale exchange is natural in morphisms and compatible
  with identity squares and horizontal vertical pasting”: eight generic
  category/scheme hits, no completed coherence statement.
- Loogle, `CategoryTheory.conjugateIsoEquiv, CategoryTheory.NatTrans.naturality`:
  zero hits for the combined query.
- Mathlib grep, `completedExchange|completedBaseChange|exchange.*coherence`
  in CategoryTheory: zero hits.
- LeanSearch, “Completed base change exchange naturality identity and pasting”:
  eight generic hits including NatTrans.exchange, NatTrans.naturality and
  TwoSquare.lanBaseChange; none states completed coherence. This fresh search
  succeeded, superseding earlier service-unavailable observations.
- Direct rg in upstream WeilConjectures and side Sheaf sources: ordinary derived
  exchange and ringed tensor/exchange coherence only. Exact blueprint-id grep in
  upstream WeilConjectures found no occurrence.
- Current source queries report CompletedBaseChangeMap and
  CompletedTowerCompatibility unavailable. Both genuine unstated prerequisites
  are supplied here under the human's 2026-10-16 instruction. Existing published
  dependency interfaces were read and their required repairs are detailed below.

Static verification: all twelve copied nodes differ only in `lean`; every primary
signature occurs verbatim modulo whitespace in its owning source; all Lean lines
are at most 100 characters. Variables and universes are explicitly bound with
`autoImplicit false`.

## Dependency modules

`def-weil-pbc-adic-coefficient-datum` — `Sheaf.Paper.AdicCoefficientDatum`, primary declaration
`AlgebraicGeometry.Scheme.completedReductionTower`. Section 1(B), current-base repair: preserve every published AdicCoefficientDatum declaration and signature verbatim. Reuse its function coefficient sheaves, completed limit, datum-indexed strict reduction tower and scalar-extension pair. Add only universal-counit, normalized evaluation and derived quotient-normalization helpers needed by completed exchange. The previous packet used obsolete ideal-indexed signatures and would replace the published interface. Coefficients remain Type(t+1), site objects t+1, morphisms t.

`def-weil-pbc-completed-base-change-map` — `Sheaf.Paper.CompletedBaseChangeMap`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedBaseChangeMap`. Unstated existing prerequisite, supplied in the same delivery under the human instruction of 2026-10-16. The node has no usable lean record in the read-only checkout or published source. Its canonical objects and maps are constructed in this module, with no arbitrary replacement of canonical maps.

`def-weil-pbc-completed-pullback` — `Sheaf.Paper.CompletedPullback`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPull`. Section 1(B): retain CompletedTowerPullback by import and reuse its actual K-flat-normalized derived quotient unit. Supply the canonical exact ringed-adjunction presentation of tower pullback and its completion-unit comparison, needed to form adjunction mates and the ordered strict tower exchange. The coefficient structure map is the actual finite-projection limit map; its invertibility is a consequence of the published profinite comparison, not an extra hypothesis. Intrinsic completion is imported from the current published IntrinsicCompletion module.

`def-weil-pbc-derived-inverse-limit` — `Sheaf.Paper.CompletedDerivedInverseLimit`, primary declaration
`AlgebraicGeometry.Scheme.CompletedDerivedInverseLimit`. Section 1(B): the generic IsDerivedLimitTriangle is retained by import; supply its precise derived strict-tower evaluation and transition specialization, with the Roos object and triangle bundled. No cone functor or arbitrary chosen limit is introduced.

`def-weil-pbc-etale-origin-witness` — `Sheaf.Paper.RingedEtaleOriginWitness`, primary declaration
`AlgebraicGeometry.Scheme.EtaleOriginWitness`. Section 1(B): retain the general-ring witness module by import and expose its constant-ring-sheaf realization with a specified bounded-below object and isomorphism. FiniteEtaleOriginWitness is the same general witness after exact scalar restriction along the canonical constants-to-functions isomorphism to the current reduction coefficients. The general witness imposes no finiteness condition.

`def-weil-pbc-four-arrows` — `Sheaf.Paper.FourArrows`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows`. Section 1(B): the recorded properBaseChangeFourArrows uses the ProEtaleAdicCoefficientDatum presentation. Supply the same four canonical arrows over the current AdicCoefficientDatum reduction tower and normalized ringed adjunctions. The retained finite witness is transported by the specified constants-to-functions coefficient isomorphism. Only h, h-prime and v-prime have asserted invertibility; no rectangle is built into the structure.

`def-weil-pbc-four-corners` — `Sheaf.Paper.FourCorners`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`. Section 1(B): the recorded ProperBaseChangeFourCorners takes ProEtaleAdicCoefficientDatum and its adicDatum coefficient localization. Supply its canonical normalized ringed-adjunction presentation on the published AdicCoefficientDatum reduction tower. Use the published pbcLevelConstantComparison and scalar adjunctions; build the completed coefficient comparison by its finite projections. All quotient actions and ordinary rather than completed pullbacks are retained.

`lem-weil-pbc-tower-compatibility` — `Sheaf.Paper.CompletedTowerCompatibility`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourTowers_compatibility`. Unstated existing prerequisite, supplied in the same delivery under the human instruction of 2026-10-16. The node has no usable lean record in the read-only checkout or published source. Its canonical objects and maps are constructed in this module, with no arbitrary replacement of canonical maps.

`prop-weil-pbc-direct-image-limits` — `Sheaf.Paper.CompletedDirectImageLimits`, primary declaration
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`. Section 1(B): the current CompletedTowerDirectImage exports the actual completed-coefficient direct images and their derived comparisons, but not the strict normalized tower adjunction and reduction/pullback mate used by completed exchange. Supply that equivalent normalized ringed-adjunction interface, including the evaluation equation on K-injectives, the constant/pullback conjugate limit comparison, strict projection and its quotient/completion-unit compatibility. Reuse the existing coefficient objects and universal derived pairs.

`prop-weil-pbc-rlim-functoriality` — `Sheaf.Paper.CompletedRlimFunctor`, primary declaration
`AlgebraicGeometry.Scheme.completedRlim_computation`. Section 1(B): the current CompletedTowerDerivedLimitFunctor supplies the canonical total right derivation of inverse limit. Extend that same Mathlib rightDerivedFunctor construction to the explicit universal unit, actual derived projections and their specified Roos first arrow required by the direct-image comparison. No arbitrary functorial cone or unrelated inverse limit is selected.

`thm-weil-pbc-finite-level-proetale` — `Sheaf.Paper.FiniteLevelProEtaleBaseChange`, primary declaration
`AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange`. Section 1(B): the published finiteConstantRingedExchange_isIso is in constant CommRingCat coefficients after finiteOriginTransport of the RingCat witness. Supply its exact coefficient transport to the published continuous-function CommRingCat coefficients used by reduction. The same finite commutative ring, proper map, bounded-below etale witness and canonical ambient ringed mate are retained. No additional hypothesis is imposed.

## Current verification

The prescribed fresh dry run is recorded in
`scratchpad/worker-refresh-dry-run.log`; its final result is appended after completion.
All compiles run through the authorized scompile.py wrapper, one file at a time,
within the unchanged 60-second per-file limit. No global build or direct Git command
is run by this worker.

The following is the preserved independent reading from the earlier attempt. Its
compile hashes describe that attempt; the current verification above supersedes
its operational status. No new independent-reader claim is made by this refresh.

## Second reading by Q44

Independent reading of the current packet, 2026-10-16. This section supersedes
previous second-reading and verification sections above. I did not write the
worker's statements. I opened the main node, its direct dependency, every supplied
module and owning node, and the current published coefficient and dependency sources.
There are no new definition nodes and no mathematical statement correction.

The source inventory is the actual blueprint page at order 1348, its completed-map
page at order 1338, Stacks proetale.tex section-derived-completion-noetherian (099L),
lemma-naive-completion (099M), lemma-pushforward-Noetherian-case (099N), and
theorem-proper-base-change (09C9), plus sites-cohomology.tex
remark-compatible-with-diagram (0E48). The blueprint explicitly adds coherence to
Stacks' isomorphism theorem; 0E48 provides the projection/exchange rectangle, not
completed coherence itself. I checked the source's Noetherian ring, torsion modulo
I, perfect quotients, proper morphism, completeness and independent bounded-below
etale-origin reductions against the dependency signatures. The blueprint datum's
additional finite-set quotient hypothesis is retained.

The object/hypothesis/conclusion checklist, read against the final Lean, is:

| Node ingredient | Lean rendering and verdict |
| --- | --- |
| Schemes and the four arrows of the Cartesian square | `Scheme.{t}`, `g'`, `f'`, `f`, `g`, and `ChosenCartesianSquare g' f' f g`. Its inherited commutativity and projection-preserving `isoPullback` are the recorded chosen square. Pass. |
| The adic ring and ideal, Noetherianity, finite generation, additive torsion and every finite perfect positive quotient | `A : Type (t+1)`, `[CommRing A]`, `d : AdicCoefficientDatum A`, imported from `CompletedAdicCoefficientDatum` and its parent `CompleteCoefficientDatum`. No new field is added. Pass. |
| Completed coefficient sheaves and their module categories | `d.completedRing T` now abbreviates the CURRENT published `completedReductionCoefficient T d`: the actual limit of the continuous-function coefficient sheaves. `d.derived T` is their standard derived localization. Constant A is not identified with A_T. Pass after repair. |
| Every positive quotient and its action | `d.finiteRing T n`, `d.projection T n`, `d.reduction T n` reuse the current datum-indexed published coefficient and universal scalar-extension pairs. `n : ℕ` represents exponent `n+1`. Quotient actions are retained before exact scalar restriction. Pass after repair. |
| The small pro-etale site and coefficient sizes | Actual site objects remain in t+1 and morphisms in t; coefficient modules use t+1. I read the independent-coefficient derived-change theorem and the canonical ringed operations at these sizes. No site universe equality or field hypothesis is introduced. Pass. |
| Properness and arbitrary change of base | `[IsProper f]` appears on the domain of `completedBaseChangeMap`; g has no additional restriction. Vertical pasting also has `[IsProper e]`, as required for its second exchange. Pass. |
| Derived-complete K | `hK : d.TowerComplete X K` means invertibility of the actual completion unit. Its quotient augmentation now REUSES `completedReductionTowerUnit d X` from the published completed-pullback module. The separately stated `towerComplete_iff_intrinsic` uses the published intrinsic Koszul completion with every generating list and representative. K itself has no lower bound. Pass. |
| Retained witnesses at every quotient | `FiniteEtaleOriginWitness X (A ⧸ d.ideal^(n+1)) ...` is an abbreviation for the general `EtaleOriginWitness` after exact restriction along the specified constants-to-functions coefficient isomorphism. The general witness keeps its bounded-below etale `complex` and displayed `iso`; the general definition still permits arbitrary commutative rings. Bounds and choices at different n are independent. Pass after repair. |
| The particular completed exchange | `completedBaseChangeMap` unfolds to the same ordered `completedExchange`: Rlim(h), then Rlim(v'), then inverse canonical direct-image/Rlim comparison. The source identification is definitional. `towerV'` is the strict projection realization h inverse, v, h'; its finite evaluation is the canonical finite mate by `fourTowers_compatibility`. Pass. |
| Naturality in every input morphism | `completedExchange_naturality` binds K, H, both complete-input proofs, independent WK and WH, and arbitrary `k : K ⟶ H`. Its equation is source-functor(k) followed by Ex(H) equals Ex(K) followed by target-functor(k). No witness-level map is required. Pass. |
| Identity squares with horizontal identities | `completedExchange_identity_horizontal` binds any chosen square `(id X, f, f, id Y)` and gives exactly the canonical completed identity comparisons on Rf_*K and K. `push_complete` supplies completeness of Rf_*K. Pass. |
| Identity squares with vertical identities | `completedExchange_identity_vertical` binds any chosen square `(g, id U, id V, g)` and gives the two canonical right-adjoint identity maps. No special choice of square identification is imposed. Pass. |
| Horizontal pasting | `completedExchange_horizontal` binds both Cartesian squares and the outer square, with g,h and g',h' in their correct order. The equation starts with `completedPullComp h g`, then pullback of Ex(sq1), then Ex(sq2) at the intermediate pullback, then pushforward of inverse `completedPullComp h' g'`. These composition maps are fixed by their ordinary completion-unit equation. Pass. |
| Vertical pasting | `completedExchange_vertical` binds sq1, sq2 and the outer square. The equation is completed pullback of inverse `pushComp f e`, Ex(sq2) at Rf_*K, pushforward of Ex(sq1), and `pushComp f' e'`. `pushComp` is the conjugate of the canonical ordinary pullback composition. Pass. |
| Pasting domains | The outer K retains completeness and its witnesses. Intermediate terms use the ambient extension of exactly the same ordered construction, so no extra intermediate witness choice or compatibility is assumed. Pass. |

I checked all twelve surviving modules against their dependency nodes. The following
also records the current-base repairs rather than repeating stale claims above:

- `AdicCoefficientDatum`: the old packet would replace the newly published
  function-coefficient, datum-indexed interface by an obsolete ideal-indexed constant
  presentation, removing published declarations. The final file preserves the ENTIRE
  current published source as its prefix, with every original signature and body.
  Only absent universal-counit, evaluation and derived-normalization helpers are
  appended. The original scalar functor, quotient tower and coefficient limits are
  reused. This is a material H4/H13 repair.
- `CompletedDerivedInverseLimit`: remove the copied evaluation-step and sequence
  definitions because the current coefficient module already defines them. Reuse
  those exact definitions and bundle only the object and specified Roos triangle.
- `CompletedRlimFunctor`: retain the canonical total right derivation of ordinary
  limit, its universal unit, actual projections, K-injective computation, triangulation,
  resolution independence and Roos normalization. Rename its additive helper to avoid
  collision with the published completed-tower module. No arbitrary cone is chosen.
- `FourCorners`: use current function coefficient sheaves. Finite inverse-image maps
  are transported using the published `pbcLevelConstantComparison`. The completed
  coefficient map is the actual limit lift of its finite projections; its invertibility
  follows from the profinite comparison. Reuse `pbcScalarAdjunction` and
  `pbcDerivedScalarAdjunction` instead of restating these normalized adjunctions.
  The four objects and delta retain ordinary, not completed, pullback.
- `CompletedPullback`: import the current `CompletedTowerPullback` and reuse its
  specified quotient unit. Remove the copied ordinary/derived augmentation constructions.
  Keep the canonical exact ringed-adjunction presentation required by strict tower
  exchange. Import current `IntrinsicCompletion`; drop the entire duplicate independent
  intrinsic-completion module and its dependency-node repair.
- `RingedEtaleOriginWitness`: keep the general-ring realization/witness without any
  finiteness restriction. Supply exact finite coefficient restriction and its explicit
  retained witness abbreviation for the current reduction presentation. No witness is
  replaced by a mere existence assertion.
- `FiniteLevelProEtaleBaseChange`: transport the same canonical finite ringed mate
  into the actual function coefficients and its explicitly transported witness.
  The coefficient ring is finite; f is proper; the retained etale antecedent supplies
  the needed bounded-below property. The forward map is witness-independent.
- `FourArrows`: retain chi/counit adjunct for finite projection and exactly the three
  asserted isomorphisms h, h' and v'. The rectangle remains a later theorem.
- `CompletedDirectImageLimits`: retain the termwise direct image, canonical adjunction,
  unique K-injective evaluation normalization, conjugate direct-image/limit comparison,
  actual product/shift equations and both Roos squares. Strict projection, arbitrary-map
  naturality, finite evaluations, completion-unit compatibility and completeness
  preservation are unchanged mathematically and now use the published reduction tower.
- `CompletedTowerCompatibility`: four actual strict derived towers, all four evaluated
  arrows, the strict rectangle and endomorphism compatibility are retained. No assertion
  of faithfulness of derived evaluation is made.
- `CompletedBaseChangeMap`: same specified ordered composite and same precise domain.
- `CompletedExchangeCoherence`: all four clauses and both identity orientations remain;
  only coefficient/witness-interface references were updated. Canonical comparisons
  retain their section, adjunction or completion-unit normalizations.

The obsolete derived-change-of-rings dependency module and node copy were removed:
the CURRENT independent-universe theorem is imported unchanged. Its scalar helpers
already live in the published coefficient module and are reused there. The current
intrinsic-completion node is likewise used unchanged. Surviving dependency notes were
rewritten to identify the actual current interface difference, rather than claiming
that already landed modules were unavailable. All copied nodes are refreshed from the
read-only base with only their `lean` field changed. No target/unit statement changes.

The main docstrings retain the node's seven proof steps: pass through the
constant/completed equivalence; identify the specified strict tower mate; use strict
composition/unit and mate-pasting laws before Rlim; apply Rlim to actual tower
equalities; retain the normalized projection and direct-image/limit comparisons;
cancel intermediate comparisons for units and pasting; then apply the same naturality
calculation to every K-to-H morphism. There is no inference from equality of finite
derived evaluations to equality of strict derived tower morphisms. Every postponed
proof is a named theorem with source/blueprint/proof docstring and belongs to its
owning node's declaration list. Definitions contain actual data, a local-formula
unique map, or a universal derived pair. No theorem is proved in this reading.

Edge cases: the empty scheme and zero objects are allowed; there is no nonemptiness,
connectedness, scheme Noetherianity or affineness assumption. The zero ring, I=top
and I=0 are permitted whenever the datum's finite/perfect quotient conditions hold.
The tower index is the prescribed positive integers, with Lean n=0 representing the
first positive exponent. Arbitrary characteristic and additive torsion are retained.
The intrinsic comparison quantifies over all finite generating lists, including the
empty list when appropriate. K is unbounded; finite etale antecedents may have unrelated
lower bounds; k may be zero or identity; WK and WH may be unrelated choices. All
identity and outer chosen square identifications are permitted. No universe equality
was added to make an API apply.

Independent searches used wording different from the first worker. LeanFinder query
“Adic derived base change map respects units and composite pullback squares” returned
eight generic cotangent/differential base-change hits, not completed coherence.
Loogle `CategoryTheory.conjugateIsoEquiv` returned five generic conjugation declarations,
which are used as ingredients. Mathlib grep
`completion.*pasting|completed.*exchange|exchange.*completed` returned no match.
Direct rg on Mathlib, upstream WeilConjectures and side Sheaf sources found the upstream
particular l-adic weakly-etale base-change maps and ordinary ringed exchange. I opened
the latter and the current coefficient/pullback/direct-image interfaces; these are
reused or extended as described above. There is no exact existing completed coherence
statement. The prior LeanSearch service error remains recorded as unavailable.

Fresh compile, dry-run and delivery results are recorded below when complete.

Final static verification: all twelve surviving node copies differ from the current
read-only records only in `lean`; the project declaration parser regenerated every
primary signature and declaration list from the final source. Every Lean line is at
most 100 characters. The current published coefficient module is preserved verbatim
as the prefix of the delivery file. During compilation, the exact finite coefficient
transport required explicit local instances from the already recorded
`proEtaleRingRestrictScalars_properties`; these are now supplied when forming its
termwise derived functor. No exactness assumption is added to a statement.

Final prescribed dry run succeeded with exit 0:
`OK (dry run): commit ce7ef6536f passes the preflight and compiles; nothing pushed`.
All twelve delivered modules passed the wrapper's separate sandbox and library checks,
with no errors and no warnings beyond the permitted postponed-proof warnings. The
server preflight accepted the packet against the current newtargets-dag sources.
The earlier failed compile logs record intermediate elaboration errors, both repaired:
exactness instances are explicit and the derived transport has an explicit source
and target category. No Lean-source changes followed this successful dry run.
The second reader now invokes the prescribed delivery command for the same packet.


## Maintainer review repair of the witness interface

The immutable replacement primary `Scheme.EtaleOriginWitness` required `[CommRing Λ]`.
The owning node's dependency `def-weil-pbc-proetale-modules` instead includes all
finite discrete rings and left modules, including noncommutative rings. Importing
`ProEtale.EtaleOriginWitness` did not repair the narrower new primary declaration.
This was a delivery-errors H3/H13 mismatch; the preceding claims that the new
primary interface preserved the general ring convention were incorrect.

The complete replacement RingedEtaleOriginWitness.lean reuses the recorded
`ProEtale.EtaleOriginWitness` as a transparent primary abbreviation, with `[Ring Λ]`,
finite discrete coefficients and the bounded-below target. It retains the specified
etale antecedent and comparison isomorphism. Finite matrix rings are admitted.
The auxiliary `FiniteEtaleOriginWitness` retains the bounded-below etale complex
and its displayed comparison after exact constant/function coefficient restriction;
that auxiliary presentation is commutative because it is used for adic quotients.
All named declarations remain, and no coherence equation or adic hypothesis changes.
The historical dependency note's final sentence about an unrestricted general witness
is superseded by this correction: the primary now follows the recorded finite-ring
convention, while the auxiliary constant-ring realization still allows arbitrary
commutative rings. This is a lean-interface repair, with no statement_change.

The stage-2 merge tool's `refit_record` accepts the replacement, regenerates its
primary signature verbatim and retains the declaration list without refusals.
The replacement file compiled independently through scompile.py in sandbox and
library modes (5.8 seconds each), exit 0. Full-packet compiler evidence and the
independent mathematical checklist are recorded in review.md.


Maintainer compiler confirmation completed: the original immutable twelve-module
packet and the twelve-module packet using the replacement witness both passed
scompile.py with server confirmation, exit 0. The full fixed packet compiled the
witness in 3.3 seconds and CompletedExchangeCoherence in 3.6 seconds; all delivered
files and the exact side import closure stayed within 60 seconds per file. The
local mirror lacked two transitive artifacts, which the prescribed server
confirmation resolved. No Lean source changed after the successful fixed check.
Complete per-file evidence is recorded in review.md.
