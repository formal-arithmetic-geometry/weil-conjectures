## Worker report

This delivery states `AlgebraicGeometry.Scheme.HasTowerPreservation` in
`Sheaf.Paper.TowerPreservation`. It recovers the previously reviewed Q08
statement packet (immutable head 344da31d420d9c97069588db6641251c0746988e),
checks it against the current dependency interfaces, and rechecks the former
landing conflicts against the current published sources. The former reader's review is background evidence, not a second
reading of this delivery. No second-reading section is supplied by this worker.
No natural-language statement is changed and no new definition node is added.

The item and all seven direct statement dependencies were read, including their
recorded declarations and full signatures/docstrings. The source is blueprint
order 1353. The local shared checkout has no literature blueprint body; I opened
the actual server literature source with a read-only command, together with the
AMP, bounded-tower, direct-image-limits, and completed-pullback source files. The source note
explicitly distinguishes this blueprint predicate from the Stacks results.
Stacks 099N and 09C2 were opened: 099N describes completed operations on constant
coefficients, and 09C2 bounds a reduction tower of one constructible complex.
Neither substitutes for the universal tower-preservation quantifier here.

Clause-by-clause rendering:

- The schemes and four arrows are `X' X Y' Y`, `g' f' f g`.
  `sq : ChosenCartesianSquare g' f' f g` retains the chosen pullback
  identification and both projection equations.
- `A : Type (u+1)`, `[CommRing A]`, and `d : AdicCoefficientDatum A`
  retain Noetherianity, the finitely generated ideal, additive torsion of A/I,
  and finiteness and perfectness of every positive quotient. Index `n : ℕ`
  means the positive exponent n+1 throughout.
- The completed module and strict tower categories are the recorded
  `pbcModules T (pbcAdicCompletion T d)` and
  `pbcTowers T (pbcAdicCompletion T d)`. The four ambient operations are
  `completedTowerDirectImage f d`, `completedTowerDirectImage f' d`,
  `completedTowerPullback g d`, `completedTowerPullback g' d`, in exactly
  the four source/target directions displayed in the node. No inverse limit
  occurs in the preservation predicate.
- `PreservesBoundedConstructibleAdicTowers` quantifies over every
  `M : AdicTower S d` satisfying
  `IsUniformlyBoundedConstructibleAdicTower d M`. Its domain includes arbitrary
  normalized towers and all supplied quotient-linear level structures.
- The output is `N : AdicTower T d` with
  `Nonempty (N.tower ≅ F.obj M.tower)`. Its fields supply quotient-linear
  levels, scalar-restriction evaluation identifications, normalization
  isomorphisms, their actual transition equation, and the full quotient cocycle.
- `IsUniformlyBoundedConstructibleAdicTower d N` supplies one finite locally
  closed stratification, common integer bounds, covering sieves on its strata,
  and `AdicTowerLocalModel`s. These retain actual restricted coefficient rings,
  bounded complexes of adic-lisse finite-type terms, finite-lisse cohomology
  at every finite reduction, linear identification isomorphisms and their
  compatibility with normalization. These are the recorded dependency's data.
- `HasTowerAmplitudeCompatibleModels` quantifies over every nonnegative
  amplification bound c and every ordered integer interval [a,b]. When AMP
  holds and all supplied input levels have that interval, it tests the actual
  finite operations on `M.level n` and requires compatible output local models
  in [a,b+c] for direct image and [a,b] for pullback. The output N is chosen
  before these tests. `HasAdicLevelAmplitude` means vanishing of homology
  outside the interval; `HasConstructibleAdicTowerModels` reuses all the
  `AdicTowerLocalModel` fields with the specified window.
- `towerFinitePullback` and `towerFiniteDirectImage` use the canonical finite
  coefficient map and the recorded pro-etale operations on the supplied
  quotient-linear objects. No comparison of arbitrary completed tower
  evaluations with finite pullback is included. The separate dependency
  `completedPullback_reductionEvaluation` explicitly starts with the reduction
  tower, as the node requires.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.Paper.AdicCoefficientDatum`: the arithmetic `AdicCoefficientDatum`
  publicly reexported from `CompletedAdicCoefficientDatum`, the actual
  `AdicCoefficients.ringSystem/completedRing`, and the independently sized
  reduction construction and normalized universal derived counits.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` publicly
  reexports the general `proEtaleRingDerivedPullback`,
  `proEtaleRingModuleDirectImage`, and canonically normalized adjunctions.
- `Sheaf.Paper.BoundedConstructibleTower`: `AdicTower`, `AdicTowerLocalModel`,
  `IsUniformlyBoundedConstructibleAdicTower`, `pbcAdicRings`,
  `pbcAdicCompletion`, and the canonical scalar adjunction/restriction helpers.
- `Sheaf.Paper.CompletedTowerPullback`: `completedCoefficientMap`,
  `completedFiniteCoefficientMap`, `completedTowerPullback`.
- `Sheaf.Paper.CompletedTowerDirectImage`: `completedTowerDirectImage`,
  `completedFiniteDerivedDirectImage`, `completedDirectImageRlimIso`.
- `Sheaf.Paper.FiniteLevelAmplification`: `HasFiniteLevelAmplification` and
  its exact finite pullback and bounded constructibility interfaces.

The site object and morphism universes remain u+1 and u; coefficient modules
have universe u+1. There is no additional equality of universes, geometric
assumption on the square, properness assumption, or identification of completed
and constant coefficients. Choices of derived functors retain their universal
pair and K-flat computation. Isomorphisms used to construct maps are fixed by
section formulas or representative normalizations. All postponed theorems
have sorry proofs and proof-plan docstrings; no definition has sorry data.

Edge cases checked: n=0 is the first positive quotient, including the unit ideal
and zero quotient; identity morphisms are admitted; empty schemes allow empty
strata; zero modules and zero towers are included; all ordered integer intervals
are tested, including singleton intervals. Local complexes are independent of n.
Failure of AMP affects only the extra interval implication: unconditional bounded
constructible preservation remains required.

Searches made in this session:

- `msearch.py` LeanFinder: "tower preservation condition for cartesian square
  adic coefficient datum" returned eight adic-completion algebra results,
  including `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`;
  none defines this predicate.
- Loogle: "Tower, DerivedCategory, Scheme" returned no hits (Tower unknown).
- Mathlib grep: `tower.*preserv|TowerPreservation` returned no hits.
- LeanSearch: "Derived direct image and pullback preserve bounded constructible
  adic towers" was unavailable with Internal Server Error.
- `rg` in both upstream WeilConjectures and shared Sheaf for preservation and
  bounded-tower names found the recorded bounded-tower construction but no
  preservation predicate. The upstream item-id search likewise found none.
- Current-source probes using `scompile.py --source` found no published
  `TowerPreservation`, `CompletedTowerPullback`, `CompletedCoefficientPullback`,
  `CompletedTowerDirectImage`, `CompletedTowerDerivedLimitFunctor`, or
  `IntrinsicCompletion`. Read-only inspection of the delivery branches found
  the earlier Q08 delivery above; its definitions are reused in this sandbox.

## Dependency modules

The authorized unstated-dependency rule requires the two genuine missing direct
dependencies to be supplied here; no downstream result is assumed to introduce
these operations. The auxiliary repairs keep the same mathematical statements.
Only the `lean` fields of existing dependency nodes are changed.

- `def-weil-pbc-completed-pullback`: `CompletedTowerPullback.lean` constructs
  the canonical coefficient map from finite projections, ordinary levelwise
  module pullback, its universal total left derived pair, reduction-only
  evaluation, inverse-limit completion, and its normalized comparison unit.
- `prop-weil-pbc-direct-image-limits`: `CompletedTowerDirectImage.lean` gives
  actual section pushforward, strict levelwise right derivation, evaluation,
  canonical limit/product/Roos comparisons, completeness, the specified
  finite projection-formula mates, quotient compatibility and completion units.
- `def-weil-pbc-adic-coefficient-datum`: `AdicCoefficientDatum.lean` retains
  its existing coefficient construction and adds the independent coefficient
  universe reduction/tower interface. The same arithmetic datum is reused;
  the old interface ties A and T to the same universe, whereas the landed
  bounded tower uses A in the site coefficient universe u+1. Universal pairs
  and explicit tensor balancing fix the generalized constructions.
- `def-weil-pbc-derived-inverse-limit`: uses the exact existing
  `CategoryTheory.IsDerivedLimitTriangle` in
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`. Evaluated sequence
  and transition helpers live in the coefficient datum module. No separate
  derived-limit notion is introduced.
- `prop-weil-pbc-rlim-functoriality`: `CompletedTowerDerivedLimitFunctor.lean`
  supplies the total right derived ordinary strict limit in the same coefficient
  universe, with its constant-tower unit, triangulatedness, invariance under
  resolutions, and Roos property.
- `def-weil-pbc-intrinsic-completion`: `IntrinsicCompletion.lean` transports
  the existing explicit `IntrinsicCompletionCompleted` Koszul fiber through
  the canonical `pbcCompletedComparison`, by exact scalar restriction in both
  directions. The round trip is identity on sections and preserves the (u,0)
  completion unit; no new Koszul or fiber definition is introduced.
- `def-weil-pbc-constructible-direct-image-finiteness`:
  `ConstructibleDirectImageFiniteness.lean` packages the existing FIN scheme
  and coefficient conventions as a predicate, instead of external typeclass
  parameters. This permits testing AMP on an arbitrary square without adding
  geometric assumptions to TOW. Higher images and their vanishing are tested
  in the canonical fixed-coefficient presentation.
- `def-weil-pbc-finite-level-amplification`: `FiniteLevelAmplification.lean`
  packages those same conventions inside FIN and retains both direct images,
  both exact finite pullbacks and all ordered intervals, for every quotient
  with one common bound. The original externally parameterized API cannot
  express the AMP implication on arbitrary squares without this repair.

## Verification

Every delivered module is compiled separately through `scompile.py`, in its
private dependency overlay. The final `deliver2.py --no-push` result is recorded
below after all reported failures have been repaired. No global build or push
is performed by this worker.

The first compile exposed module-system visibility through an already published
bounded-tower interface: newly supplied `completedTowerDerivedSequence` and
`completedTowerDerivedStep` were not exposed by that module's older public
import. Modules using the added coefficient interface now explicitly publicly
import its owning `AdicCoefficientDatum` module. This is an import repair;
mathematical statements and constructions are unchanged.

Server confirmation of the complete eight-module packet succeeded with no errors
or unexpected warnings. Delivered-file times were 10.6 s (coefficient datum),
2.8 s (derived limit), 2.4 s (intrinsic completion), 5.6 s (tower pullback),
6.0 s (tower direct image), 1.6 s (FIN), 1.7 s (AMP), and 1.8 s (TOW).
All used nice 19, two threads, and the unchanged 60-second per-file limit.
The final dry run also checks the explicit direct-import repair and existing
upstream derived-limit declaration probe.

Worker dry run (before this second reading):
`deliver2.py Q31 def-weil-pbc-tower-preservation --no-push` printed `OK (dry run)` at commit `920f2e191d`: all delivered files and the
existing-declaration probe compile; preflight passes except for the independent
second-reading section, which is intentionally left to the second reader.
No duplicate-declaration rejection remains in this current-source preflight.
Nothing was pushed.

## Second reading by Q31

I independently read the item node and its source paragraph (blueprint order
1353), the AMP paragraph at order 1350 and completed-pullback detailed form at
order 1261, and the Stacks `proetale.tex` statements and surrounding discussion
for 099N, 09C1 and 09C2. The literature was read on the project server because
the shared mirror contains only its bibliography. In particular, 099N assumes
a Noetherian coefficient ring and an arbitrary morphism of topoi; 09C2 concerns
one constructible complex and assumes quasi-compactness of its scheme. Those
are context for this blueprint predicate, not extra geometric assumptions on
its square. Its own source explicitly introduces the preservation condition.

Clause list and comparison with `TowerPreservation.lean`:

| Node object, hypothesis or clause | Lean rendering | Verdict |
| --- | --- | --- |
| Four schemes and arrows with the specified orientation | `{X' X Y' Y : Scheme.{u}}`, `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` | Exact. |
| Chosen Cartesian identification and projection equations | `sq : ChosenCartesianSquare g' f' f g`; opened its structure, including `isoPullback`, `hom_fst`, `hom_snd` and inherited `CommSq` | Exact; not merely a commutative square. |
| Commutative Noetherian A, finitely generated I, additive torsion of A/I, finite perfect positive quotients | `{A : Type (u+1)} [CommRing A] (d : AdicCoefficientDatum A)`; opened `AdicCoefficientDatum` and `CompleteCoefficientDatum` and all inherited fields | Exact; no assumption that A itself is finite or complete. |
| Completed coefficient sheaves and strict tower categories | `pbcAdicCompletion T d`, `pbcTowers T ...`; opened their definitions and `AdicCoefficients.ringSystem/completedRing` | Actual inverse limits of the finite coefficient sheaves; strict inverse sequences, not sequences in a derived category. |
| Rf_*^Tow : X → Y | First `PreservesBoundedConstructibleAdicTowers` conjunct with `completedTowerDirectImage f d` | Exact source and target. |
| Rf'_*^Tow : X' → Y' | Second conjunct with `completedTowerDirectImage f' d` | Exact source and target. |
| Lg^*_Tow : Y → Y' | Third conjunct with `completedTowerPullback g d` | Exact; taken before inverse limit. |
| Lg'^*_Tow : X → X' | Fourth conjunct with `completedTowerPullback g' d` | Exact; taken before inverse limit. |
| Every uniformly bounded constructible adic input tower | `∀ M : AdicTower S d, IsUniformlyBoundedConstructibleAdicTower d M → ...` | Unrestricted quantifier over the recorded tower structure, including all level structures and normalization data. |
| Output is the actual functor image with quotient-linear levels whose scalar restrictions are its evaluations | `∃ N : AdicTower T d, Nonempty (N.tower ≅ F.obj M.tower) ∧ ...`; opened `AdicTower.level` and `.evaluation` | Exact up to isomorphism in the derived strict-tower category, which transports evaluations and transitions together. |
| Normalizations induce the output transitions and obey the quotient cocycle | `N.normalization`, `N.transition`, `N.cocycle` | All comparable pairs, including equal indices; no omitted cocycle. |
| Common finite locally closed stratification, covering sieves, common bounded adic-lisse finite-type local complexes and finite-lisse reduction cohomology | `IsUniformlyBoundedConstructibleAdicTower d N`; opened this definition and every field of `AdicTowerLocalModel` | Exact, including actual inverse-image coefficient rings and independence of the local complex from n. |
| Quotient-linear reduction identifications and compatibility with normalization | `AdicTowerLocalModel.identification` and `.compatible` | Exact semilinear adjunct formulation using the recorded scalar adjunction, not arbitrary abelian identifications. |
| Local models compatible with AMP amplitude intervals, using the actual finite operations | `HasTowerAmplitudeCompatibleModels`: `∀ c`, AMP implies `∀ a b`, `a ≤ b`, common input level amplitude implies finite-image amplitude and `HasConstructibleAdicTowerModels N a (b + growth c)` | Direct-image growth c, pullback growth zero. The same output N is chosen before these tests; each interval has common local models. |
| No arbitrary-tower evaluation formula for completed pullback; reduction towers are only the separately stated comparison case | No evaluation formula occurs in TOW; `completedPullback_reductionEvaluation` starts with `completedReductionTower Y d` | Exact. TOW's preservation quantifier is not restricted to reduction towers. |

I also opened the declaration interfaces of all direct dependencies, rather
than inferring their meaning from names. The bounded-tower module uses site
object/Hom universes u+1/u and module size u+1. The delivered coefficient
interface retains these sizes and publicly reuses the original arithmetic
datum. There is no equality imposed between site object and Hom universes.
The fixed coefficient-size convention does not exclude smaller rings, which
can be placed in this universe. No characteristic, properness, Noetherian
scheme or nonempty-scheme assumption is added to TOW.

Dependency-module reading:

- `AdicCoefficientDatum.lean`: finite coefficients reuse the existing
  `AdicCoefficients.ringSystem`; completion is its limit; quotient transitions
  are actual diagram maps. Scalar extension and its derived pair reuse
  `completedAdicChangeData` and `completedAdicDerivedChange`. The strict
  reduction tower is a derived functor into the strict tower category, with
  its universal counit and K-flat computation. Tensor formulas fix balancing
  and transitions uniquely. The published coefficient namespace is retained.
- `CompletedTowerDerivedLimitFunctor.lean`: `completedTowerRlim` is the right
  derived ordinary `lim`, not a choice of cones. The constant-tower unit is
  uniquely normalized on complexes. Triangulatedness, invariance under a
  universal derived pair, and the sequential Roos property are stated.
- `def-weil-pbc-derived-inverse-limit`: read the actual current source through
  `scompile.py --source WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
  `IsDerivedLimitTriangle` is exactly the distinguished triangle with the
  existing `towerTransitionEndomorphism`; it chooses no functor or cone.
- `IntrinsicCompletion.lean`: reuses `IntrinsicCompletionCompleted`'s actual
  Koszul fiber. The ring comparison is `pbcCompletedComparison`, scalar
  restrictions are exact, the round trip is identity on sections, and the
  completion unit is the transported (u,0) map. No alternate completion object
  is chosen from a bare existence assertion.
- `CompletedTowerPullback.lean`: `completedCoefficientMap` is the limit lift
  of its finite-projection components. Levelwise module pullback is inverse
  image then actual scalar extension. The derived pair is universal with
  objectwise K-flat computation; its comparison unit is normalized on those
  representatives. Reduction evaluation and intrinsic completion agree with
  the dependency statement; no invertibility of the completed coefficient map
  is imposed.
- `CompletedTowerDirectImage.lean`: section pushforward has the adjoint
  completed coefficient action. Its derived evaluation, canonical limit
  comparison, Roos/product comparison with 1-shift and connecting arrows,
  specified finite projection-formula mate, quotient compatibility and
  completion-unit composite are present. Choice-based maps have section or
  universal-derived normalizations; no arbitrary natural isomorphism is used.
- `FiniteLevelAmplification.lean`: repaired as described below. Its final body
  uses the exact published `AlgebraicGeometry.ProEtale.HasFiniteLevelAmplification`
  declaration. That declaration, in turn, uses the published FIN and the actual
  finite coefficient derived operations and strictly full bounded constructible
  predicates. Its additive/triangulated clauses are retained explicitly.

Mismatch found and repaired (H4): the worker's new FIN module and the AMP
module's fixed-coefficient helper predicates restated already published
notions. The published AMP API does require the Noetherian, finite-dimensional
and invertibility conventions as external parameters, so it cannot be applied
directly on arbitrary squares. This needs an interface wrapper, not a second
FIN construction. I replaced the AMP module with existential packaging of
exactly those convention parameters around the original AMP declaration.
The arithmetic proofs are supplied by d's existing fields. I removed
`lean/Sheaf/Paper/ConstructibleDirectImageFiniteness.lean` and its dependency
node copy from this packet, and removed the redundant AMP helper declarations
from its `lean.declarations`. No published file is edited and the original FIN
record remains in force. The main TOW file is unchanged. There is no item
statement correction or new definition node.

The existing `statement_change` on the Rlim dependency is inherited unchanged
from the base. I checked its corrected statement against the resolution
construction (all cochain complexes, not just sheaves in degree zero), and
opened its citers `def-weil-pbc-completed-pullback` and
`def-weil-pbc-completed-base-change-map`: both use the functor on arbitrary
strict derived towers and their maps, so their recorded `holds: true` remains
correct. This delivery changes only `lean` on every existing node; no inherited
correction is being introduced or altered.

Edge cases: n=0 indexes A/I, not A/I^0; the positive-natural indexing of the
published AMP is equivalent to n+1 with its quotient finiteness transported by
`Nat.succ_pred_eq_of_pos`. The zero ring, unit ideal, zero towers and complexes
are admitted. There is no nonempty hypothesis on schemes, strata or covers;
an empty finite stratification and the empty scheme remain available. Tower
indices are precisely the nonempty positive integers as the source specifies;
local covering families can be empty when the topology allows it. Integer
intervals include negative and singleton intervals. AMP failure leaves the
unconditional tower preservation requirement in force. Identity arrows and
identity coefficient restrictions are included, with the actual restricted
rings in local models.

Independent searches in this reading:

- LeanFinder: "A functor on inverse sequences of modules preserves bounded
  constructible normalized adic systems" returned eight algebraic completion
  and local-cohomology hits (`localCohomology`, `AdicCompletion`,
  `Hausdorffification`, `IsAdicComplete` and their lemmas), not this predicate.
- Loogle: `"Constructible", "Functor"` returned zero hits.
- LeanSearch: "An operation preserves all normalized adic towers with uniform
  constructible local models" returned Internal Server Error, recorded as
  unavailable rather than as a successful negative search.
- `rg` over Mathlib, upstream WeilConjectures and the project's Sheaf sources
  for preservation, normalized/constructible towers and the item id found
  the recorded bounded-tower module, adic-sheaf operations and ordinary
  constructibility results. The upstream adic-sheaf category and its lowerStar
  functor are not the strict derived tower category required here.
- Inspecting the published FIN and AMP files found the reusable declarations
  above, leading to the explicit reuse repair. No new node was needed.

All final definitions contain real constructions; all postponed theorems still
have `sorry` proofs and source/blueprint proof-plan docstrings. The main node's
`lean.statement` is verbatim its signature; the repaired AMP record has been
updated to its exact signature. All final modules use explicit universes and
`autoImplicit false`, and have no line exceeding 100 characters.

Second-reader verification: the final seven modules and the existing derived-limit
probe compiled cleanly through `scompile.py` as invoked by the delivery wrapper.
The earlier shortened check supplied only the coefficient, AMP and TOW files;
AMP compiled, while TOW correctly reported its omitted sibling direct-image
module. The full sibling packet resolves that packaging omission.
`deliver2.py Q31 def-weil-pbc-tower-preservation --no-push` then printed
`OK (dry run): commit d9255ef196 passes the preflight and compiles`.
No global build, compiler-timeout increase, or live-library edit was used.
