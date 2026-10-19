## Worker report

`Sheaf.Paper.CompletedProjectionCoherence` states
`CategoryTheory.AdicSites.ProjectionCoherence.completedProjectionCoherence`.
The only postponed proof is that theorem. All helper definitions have real data.
No object is selected from its existence assertion. The tensor presentation
records are existential conclusions, rather than additional hypotheses.

The module reuses the existing `CategoryTheory.AdicSites` notions from
`Sheaf.Paper.CompletionMateComparison`, publicly imported by the recorded module
`Sheaf.Paper.ProEtaleConstantReductionTower`. The already landed node
`lem-sp-completion-mate-comparison` was added to `stmt_deps` under brief-stage2
section 5 (landed nodes may be added). Its geometric square-exchange theorem does
not already state this item's tensor-projection and arbitrary-augmentation
assertion. Its canonical objects and comparisons are used without private copies.
No statement text was changed, no new DAG node was needed, and no dependency
record was repaired. There is no disputed statement.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative Noetherian A and ideal I | `(A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)` |
| Each positive quotient A/I^n is a bounded finite-projective A-complex | Existing `AdicSites.PerfectQuotients A I`, using `DerivedCategory.IsPerfectRingComplex` on the degree-zero module `A ⧸ I^(n+1)`; that predicate requires a bounded complex with finite projective terms and an isomorphism in the derived category. No uniform bound is required. |
| Topoi on small sites and morphism u | `{Y X : AdicSites.Site.{u}}`, `(f : Morphism Y X)`. The record supplies the actual inverse/direct sheaf functors, geometric adjunction, finite-limit preservation and canonical algebraic inverse image with its constant identifications. It imposes no extra geometric property. |
| Constant A-module sheaves and ordinary unbounded derived categories | Existing `Site.ring`, `modules`, `derived`; these are `ConstantCompletion.constant`, `Mod`, `D` and standard derived localization. |
| Exact inverse image, K-injective derived pushforward, canonical counit | Existing `f.modulePull`, `modulePush`, `moduleAdjunction`, `pull`, `push`, `adj`. `pull` is the exact derived functor, `push` the K-injective right derived functor. `TensorData` fixes its ringed edge to these constructions, including module and derived adjunctions and the exact localization comparison `epsilon_eq`. |
| Ordinary derived tensor and projection pi-o | `TensorData.modelY/modelX` are existing `RingedTensorModel`s on flat-term K-flat representatives. `comparison_eq` fixes the pullback tensor comparison to `RingedTensorEdge.tensorComparison`. `TensorData.projection` is the actual `f.adj.homEquiv` of tensor comparison followed by counit tensor identity. |
| Completion reflector, unit and Rlim quotient formula | Existing `Site.completion`, `unit`, `reflector`, `reflectorAdjunction`, `reduction`, `rlim`. Completion is definitionally strict reduction followed by total derived limit. |
| Completed adjunction C_X u* left adjoint to P | Existing `f.completePull`, `completePush`, `completeAdjunction`, whose specified Hom normalization is unit precomposition followed by the ordinary derived adjunction. |
| Completed tensor and its pullback comparison | `CompletedTensor.insertRight`, `pullInsert`, `comparison` with equations identifying them with images of the actual completion units. Completed tensor is `Site.completion` of the ordinary tensor. The comparison is fixed before the projection mate is defined. |
| Complete H and K | `(H : X.Complete A I) (K : Y.Complete A I)` throughout completed coherence predicates; these are the full subcategories for existing local `IsComplete`. |
| pi-c is the completed-adjunction projection mate | `CompletedTensor.projection` uses the actual `f.completeAdjunction.homEquiv`, its counit, the completed tensor comparison, and the inverse of the unit-induced second-factor comparison. |
| Displayed completion-unit equation | `CompletedTensor.UnitEquation`: `eta_M ≫ pi-c = pi-o ≫ P.map eta_N`. |
| This equation uniquely characterizes pi-c | `CompletedTensor.Unique`, quantifying over every arrow of the same type satisfying exactly that equation. |
| One strict quotient diagram with actual coefficient restriction transitions | Existing `Site.reduction` and `ConstantCompletion.quotientPresentation ... false` derive the actual `reductionTower` built from quotient ring homomorphisms. They are derived strict module-diagram objects, not independently chosen maps between localized levels. The existing diagram-site realization supplies the ringed-site interpretation. |
| Whole-diagram map whose total inverse limit is taken | `TensorData.towerProjection` is strict reduction of pi-o followed by existing `f.towerProjection` on N. The latter is the whole-diagram coefficient-exchange counit mate. Exchange/tensor coherence on the ringed diagram site identifies this arrow with coefficient comparison followed by the B-linear projection, before evaluation or inverse limit (proof steps 8 and 9). |
| Perfect-coefficient source comparisons | Existing `f.finiteProjection A I n H` and `f.towerProjection A I H`, both defined as coefficient-exchange counit mates. Their invertibility is asserted, rather than assumed, by the theorem's first two conjuncts. |
| Finite coefficient categories and finite tensor over A_n | `FiniteTensor.tensor : TensorData f (quotientRing A I n)` and existing `Site.finiteReduction`, `finiteRestriction`. The finite ordinary projection is `s.tensor.projection`. |
| Canonical tensor balancing | `ScalarTensor` fixes the identity geometric morphism, quotient ring map, extension/restriction functors, ordinary and derived adjunctions, and K-flat derived comparison. `Normalized` identifies its balancing with the existing representative-normalized edge tensor comparison. `FiniteTensor.targetBalancing` also inserts the canonical `f.finitePullIso`. |
| Finite source and target identification | `FiniteTensor.projection` composes source balancing, the actual perfect-coefficient source mate tensored with identity, the finite projection, and inverse target balancing. |
| Evaluations are the prescribed finite projection mates | `TensorData.FiniteEquation` compares evaluation of the whole strict arrow to exact scalar restriction of `FiniteTensor.projection`, using existing `evaluatePushIso`, `finiteEvaluationIso`, `finiteRestrictionPushIso`. All these comparisons already have canonical representative or adjunction normalizations. |
| pi-c equals the total derived inverse limit | `CompletedTensor.LimitEquation`: apply `Y.rlim` to the specified strict arrow and then `(f.directLimitIso A).inv` on its target. Its source is definitionally C_Y M and target P C_X N. |
| Canonical target direct-image/limit comparison | Existing `f.directLimitIso`, the conjugate of `constantPullIso` under the specified ordinary/tower/constant-limit adjunctions. This fixes the common-direct-image and counit normalization, not just its endpoints. |
| Transpose of every strict tower arrow after constant augmentation, including counits | `TransposeCompatibility f A` quantifies over M, whole strict derived towers Z,W, arbitrary `b : towerPull Z ⟶ W`, and arbitrary `j : delta M ⟶ Z`. The equation uses the ordinary and tower Hom bijections, delta/limit units, the actual constant/pullback comparison, and the inverse direct-image/limit comparison. Taking b to be a counit gives its compatibility. |
| Equality of specified transformations without reduction faithfulness | `CompletedTensor.Natural` states simultaneous naturality in both complete inputs. The ordinary and finite maps are natural by their functor/adjunction definitions. The limit equality is between these specified maps on the strict derived category; no faithfulness hypothesis or inference from finite-level equality is used. |

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`;
  its ringed tensor-corner, tensor-model and edge interfaces fix the ordinary mate.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`, with unit-induced
  Hom normalization; reused through the existing AdicSites completed adjunction.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`, with common-direct-image
  and evaluation normalizations.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`, including the vertical topology
  and exact diagram/module equivalence.
- Added landed dependency `lem-sp-completion-mate-comparison`, recorded module
  `Sheaf.Paper.ProEtaleConstantReductionTower`, declaration
  `CategoryTheory.AdicSites.OrderedExchangeInterface.completionMateComparison`.
  It publicly imports all original generic AdicSites interfaces in
  `Sheaf.Paper.CompletionMateComparison`: Site, Morphism, PerfectQuotients,
  finite/tower projections, canonical evaluation/scalar/pullback comparisons,
  completed adjunction and constant/limit adjunction. These are reused directly.
- `Sheaf.Paper.RingedExchangeTensorCoherence`:
  `SheafOfModules.ringedExchangeTensorCoherence` and the specified ringed edge
  tensor comparison fix the ringed diagram projection calculation.

All available proof-dependency modules are explicitly imported, including the
independent-coefficient K-flat theorem, generalized tensor pullback, general
pre-derived adjunction, right-adjoint preservation of K-injectives, K-injective
resolutions, total right derivation, strict tower homotopy limit, derived direct
image composition, projection arrows and finite totalization. The levelwise
abelian node is a Mathlib leaf (`Abelian.functorCategoryAbelian`) and its module is
imported. The closed-monoidal and RHom-complete proof nodes currently have no
recorded declaration; their uses remain explicit in the main proof docstring.

Edge cases checked before writing: n=0 means the first positive quotient A/I,
not A/I^0; I=0 gives identity coefficient towers; I=top gives zero quotients and
zero complete objects; the zero ring is included. Zero H or K and empty sites
are not excluded. Finite projective resolutions may have zero ranks and arbitrary
integer bounds; no uniform bound across n is required. Ambient complexes and
towers are unbounded. Quotients may be infinite and need not be flat over A.
The arbitrary-augmentation clause permits identity and zero augmentations and
all tower maps. No varying-coefficient evaluation-preserves-K-injectives claim
is made. All variables and the common universe are explicitly bound; no universe
equality with a coefficient localization universe is added.

Searches:

- `msearch.py leanfinder`: “Completion of derived tensor projection mate agrees
  with inverse limit of quotient coefficient projection formulas and preserves
  adjunction counits”; eight ordinary adic-completion algebra hits, no exact match.
- `msearch.py loogle`: `CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.Functor.IsRightDerivedFunctor`; zero hits.
- `msearch.py grep` in Mathlib CategoryTheory:
  `completion.*[Pp]rojection|[Pp]rojection.*completion`; zero hits.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf`:
  `completed.projection|CompletedProjection|completedProjection`; no exact match.
- `grep -rn` of this item's id in upstream `WeilConjectures`: no match.
- Further `rg` for `PerfectQuotients` and strict coefficient diagrams found
  `CompletionMateComparison` and its recorded reexport. It supplies the canonical
  constructions, so they are reused. Its conclusion is square-exchange coherence,
  rather than this tensor-projection assertion. There is no existing declaration
  for the complete combination of unit, uniqueness, strict finite projection,
  total-limit, and arbitrary-augmentation transpose clauses.

Validation: the module passed file-only `scompile.py` in sandbox and library
modes, without errors or non-sorry warnings. The final dry-run and delivery below
are the required independent preflight and per-file validation.

## Second reading by Q92

The dispatcher explicitly forbids starting other agents and specifies the
maintainer's independent review. This section records a second pass by this
worker, not a claim of an independent second agent. The node and final file were
read together, clause by clause, as tabulated above.

The pass replaced newly drafted duplicate tower/finite/completion notions with
the already published AdicSites constructions. It checked that both projections
are defined using their actual adjunction counits; uniqueness tests precisely the
unit equation; finite coefficients remain A/I^(n+1) throughout balancing; and the
strict arrow is specified before evaluation and limit. Canonical scalar-edge
normalizations fix the identity geometry, coefficient map, derived comparison
and both adjunctions. The transpose equation binds every tower arrow and constant
augmentation and uses exactly the same limit comparison as the projection limit.
No source clause was dropped or changed and no extra hypothesis is imposed.

## Maintainer fix (second reader NT-cc-Q92, 2026-10-18)

The delivered theorem bound the ordinary tensor presentation existentially
(`∃ (o : TensorData f A) ...`), so it asserted the coherence only for some
unspecified derived-tensor presentation. The landed ringed-topos tensor theorems
(`SheafOfModules.ringedProjectionMateExact`,
`SheafOfModules.ringedExchangeTensorCoherence`) take their `RingedTensorModel`s
and edges as inputs, and a citer must be able to apply this item to its own
tensor. The fix makes `o : TensorData f A` an explicit argument. The completed
comparisons `b` are still existential: their unit equations determine them, and
their existence is the invertibility of Step 1. The finite quotient
presentations `s` are also still existential. No other declaration changed. The
`lean.statement` is updated verbatim, and the module compiles file-only through
`nt_compile.py` with no errors or non-sorry warnings. The earlier sentence "The
tensor presentation records are existential conclusions" now applies only to
`b` and `s`.
