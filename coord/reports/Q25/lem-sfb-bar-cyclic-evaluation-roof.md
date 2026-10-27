## Worker report

Item: lem-sfb-bar-cyclic-evaluation-roof. Module:
`Sheaf.CategoryTheory.BarCyclicEvaluationRoof`, namespace
`CategoryTheory.BarCyclicEvaluation`. The primary statement is
`bar_cyclic_evaluation_roof`; `resolutionMap_quasiIso` is the separately named
quasi-isomorphism clause. Both proofs are `sorry`. Every other declaration has real
construction data, using the already landed action, bar and cyclic constructions.
No source statement correction, new definition node, or dependency repair is needed.

Hypotheses and objects, read against the complete node:

- The commutative condensed ring is `A : CondensedBar.Ring.{u}`, namely commutative
  monoid objects in abelian sheaves on `coherentTopology Profinite.{u}`. Its modules
  are the existing `CondensedBar.Modules A`, and its regular module is `Mod.regular A.X`.
  This includes arbitrary condensed rings, without a topological-ring presentation.
- `H : Type u` has `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`,
  `T2Space`, and `TotallyDisconnectedSpace`. The group is profinite in exactly the
  recorded bar-model sense. `v : Z.{u} →ₜ* H` is u in the informal statement;
  `Z` is the discrete lifted multiplicative integers and `generator` is positive one.
  No density, faithfulness, infinite order, or injectivity of v is assumed.
- `I : InjectiveResolution (CondensedDerivedRestriction.regularTrivial A H)` is ANY
  nonnegative equivariant injective resolution of the trivial regular module.
  `I.cocomplex`, `I.cochainComplex` and `I.ι'` give its natural-degree complex,
  extension by zero, and augmentation. There is no injectivity binder on its restriction.
- `M : BarModel A H` is the dependency's compatible bar model, and
  `b : BarNormalization M` is the inclusion-normalized identification of its invariants
  with the scalar invariants. `barNormalizationExist M` supplies this normalization for
  every model; this binder restricts no mathematical case.
- `K : TotalModel A PUnit` and `C : HasComparison A PUnit K` are exactly the existing
  cyclic model and theta-alpha=Qb normalization of the node. They are supplied by the
  signed-total and cyclic-row dependencies; the statement is for every such model.
  Residual PUnit is only the existing library presentation of the scalar total.
- The universe u contains every profinite parameter and H. Internal coefficient sections
  have size u+1. `BarModel` explicitly retains its existing u+2 localization, while
  `barEta` and the relative cyclic/scalar maps use the existing u+1 localization
  transport. No universes are identified or reduced in this delivery.

Every clause of the conclusion:

- `doubleComplex (barDiagram M) I.cocomplex` is the given D^{p,q}; its bar terms are
  `BarDiagram.term` and `InternalFunctions.internalHom`, with the internal free parameter
  `freeParameter A (power H p)`. `totalCochains` is its finite-diagonal total, with
  d_bar+(-1)^p d_resolution. These are reused, not reconstructed.
- `total K v I.cochainComplex` is K(VI). `input v` is exact cyclic restriction followed
  by the existing trivial residual inflation; forgetting residual PUnit restores the
  scalar module. `TotalModel.coordinates`, `.differential`, and `.maps` give the specified
  two coordinates, differential (dx,(T-1)x-dy), and diagonal maps without changing signs.
- The existential `E` is a COCHAIN MAP from the actual bar total to that total.
  `Coordinates M K v I E` specifies both projections on EVERY summand `(p,q)`.
  Its first clause is identity under the degree-zero internal-function identification;
  the second kills every positive-p summand in the first coordinate. Its third clause
  evaluates the p=1 summand at the constant map with value `v generator`; its fourth
  kills all p≠1 summands in the second coordinate. Therefore p≥2 contributes to neither.
  `value` uses the recorded `InternalFunctions.evaluate` equivalence on every S.
  By the free/internal-Hom adjunction this is precisely precomposition with the map
  sending 1 to [tau], not evaluation only on global sections.
- `Horizontal M v I` states `(d_h m)(tau)=tau*m-m` on every profinite S and every
  resolution term. The explicit `@id` only exposes the definitionally identical
  section-module carrier for the action; it changes neither the element nor its action.
- `invariantMap M I` is the extension of the EXISTING total invariant augmentation b_H.
  The two equations immediately after Coordinates say b_H E has first coordinate the
  given inclusion and second coordinate zero. The first equation is written at every
  nonnegative degree; negative source terms are zero by extension. Thus Eb_H=(inclusion,0).
- `RelativeCyclic.evaluation (barFunctions M) (barDiagram M) v` is epsilon from the
  existing owning node, including its identity, evaluation and zero-degree components.
  `barAugmentation ... I` is j_rep, defined by the coefficient augmentation in the
  resolution-zero row. The displayed cochain equality is j_rep ≫ E = epsilon ≫ k.
- `resolutionMap K v I` is k=K(Va), using the existing `trivialTotalIso`, the
  identity-underlying `regularIso`, the canonical single-complex comparison and `I.ι'`.
  `resolutionMap_quasiIso` asserts it is a quasi-isomorphism without requiring VI injective.
- `sourceIso M b I` is sigma: first invert the transported comparison b.invariants,
  then invert the canonical `scalarResolutionIso`. This is precisely the source
  injective-resolution identification A^{-1} alpha, not a freely chosen source isomorphism.
  Existing `barEta` is its inverse followed by Q(b_H), so the specified eta normalization
  is retained literally by use of that definition.
- `trivialCyclicMap C v` is the existing scalar c=lambda^{-1} beta. Its definition uses
  the same beta of the mate dependency, and the same all-complex normalized lambda of
  the row dependency, with the canonical source/target forgetting identifications.
  The penultimate equation is sigma ≫ c = Q(b_H ≫ E) ≫ inv(Q k), the precise roof formula
  under the canonical resolution identification. The final equation is
  Q(j_rep) ≫ eta.inv ≫ c = Q(epsilon). These are actual derived arrows.
- No clause asserts that beta or j is invertible, or that the underived bar is a derived
  model. The only inverse of a new cochain map is Q(k), justified by the separate theorem.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; Mathlib
  `CategoryTheory.Monoidal.Mod`: `Mod`, `Mod.regular` (ring and module categories).
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `inflate`, `Invariants`,
  the sectionwise action and its forgetful/additive structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`,
  `HasDerivedCategory`; `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `InjectiveResolution`; its integer-extension API is also used.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal` and Mathlib total complexes:
  `HomologicalComplex₂`, `ιTotal`, with the fixed sign convention.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `InternalFunctions`, `BarDiagram`,
  `cochains`, `doubleComplex`, `totalCochains`, `Model`, `TotalAugmentation`.
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`: `condensed_derived_invariant_bar`;
  `Sheaf.CategoryTheory.InternalBarRoofAdjunction`: `normalized_roofs` and its normalized
  bar model. These supply the compatible construction and its normalization.
- `Sheaf.CategoryTheory.RelativeRestrictionMateForgetting`: `beta_mate`, with the existing
  `RelativeDerivedInvariants.betaNormalization` and beta used by `trivialCyclicMap`.
- `Sheaf.CategoryTheory.CyclicRowDerivedComparison`: `cyclicRow_derived_comparison`,
  `cyclicRow_hasComparison`, and its normalization on all complexes;
  `Sheaf.CategoryTheory.CyclicTotalTriangulated`: signed cyclic total and its
  quasi-isomorphism preservation. These are also the stated proof dependencies.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: recorded sheaf Hom
  interface; for internal module objects the existing bar datum's `internalHom` identifies
  its functions with `Mod.ihom (freeParameter ...)`, the appropriate module-object encoding.
- `Sheaf.CategoryTheory.RelativeBarData`: `BarModel`, `barFunctions`, `barDiagram`,
  `barInvariants`, `barTotalAugmentation`, `BarNormalization`, `barNormalizationExist`,
  `barEta`, `scalarResolutionIso`, `barAugmentation`, `evaluation`, `trivialCyclic`.
- `Sheaf.CategoryTheory.RelativeTrivialCyclicMap`: `trivialInput`, `trivialTotalIso`,
  `trivialCyclicMap`. `Sheaf.CategoryTheory.RelativeCyclicTotal`: `TotalModel`,
  `HasComparison`. Their three ALREADY LANDED owning nodes are added to stmt_deps,
  as authorized for reuse of landed notions. No records of those nodes are changed.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`:
  exact restriction and `boundedBelowComputation` are retained as proof imports.

Edge cases checked before writing: degree zero has no second source term; degree one
has exactly the evaluation coordinate; all negative degrees of the bar source vanish.
The p=0 second coordinate is zero and p≥2 has both coordinates zero. At tau=1 the
horizontal formula gives zero, and no infinite-order assumption is used. Trivial H,
finite-order tau, the zero coefficient ring, arbitrary resolution and arbitrary compatible
bar/cyclic models remain included. An empty profinite test object has its unique section
formulas; nothing requires nonempty test objects. The signed differential gives a minus
on d_I in bar degree one, as in the node.

Searches made (2026-10-24):

- msearch.py leanfinder: `Evaluation from internal condensed bar total to cyclic mapping
  fiber represents derived restriction`. Eight results, principally condensed/discrete
  counit evaluations, no statement with this bar total, normalized mate and cyclic roof.
- msearch.py loogle: `"groupCohomology", "res"`. Twelve ordinary representation
  cohomology restriction/inflation hits; no internal condensed derived roof.
- msearch.py grep: `(bar|Bar).*(cyclic|Cyclic|evaluation)|(cyclic|Cyclic).*(bar|Bar)`.
  Zero Mathlib hits.
- msearch.py leansearch: `Condensed group cohomology bar evaluation at a cyclic generator
  and derived restriction`. Eight hits including `groupCohomology.resNatTrans` and
  `inhomogeneousCochainsIso`; these have ordinary Rep coefficients, no compatible
  injective internal-Hom total or normalized roof.
- rg of that bar/cyclic/evaluation pattern in `lean/WeilConjectures` and `lean/Sheaf`:
  found the existing RelativeBarData and RelativeCyclicRestrictionModel partial interface.
  Read both. The latter's `barEvaluation` gives ONLY the final derived identity; it does
  not assert existence and coordinates of E, the cochain augmentation square or the roof
  representative. Thus it is not an existing exact match for this full node.
- rg for the exact item in `lean/WeilConjectures`: no match. rg of `BarCyclicEvaluation`
  and `bar_cyclic_evaluation_roof` in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration/name collision.
- Read the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`,
  paragraph (3). The DAG explicitly labels the cyclic calculation an agent-extracted
  auxiliary input with combined reference WANTED; no different source claim is substituted.

No STATEMENT-DISPUTED issue found. The old CompactObject example module is now withdrawn;
its node points to the identical upstream module. This delivery follows the current module,
public-import and exposed-public-section convention rather than copying the withdrawn stub.

## Second reading by Q25

Performed a separate pass with the complete node and finished Lean source open. This is a
self-review: the dispatcher expressly prohibits spawning another agent and the maintainer
performs the independent review. Rechecked the above correspondence against the actual
signature, including every conjunct of Coordinates, Horizontal and the main theorem.

The first draft exposed three encoding errors: casts at the p=0 total summand, the identical
section-module carrier under the action, and use of a non-instance quasi-isomorphism when
constructing sigma. They were repaired by an equality transport, explicit carrier identity,
and the actual inverse scalar-resolution/invariant comparison, respectively. The last repair
also makes the canonical source normalization visible without selecting any new data.
The three long-line warnings were repaired. Qualified `RelativeCyclic.evaluation` to avoid
resolving the unrelated generic functor-category evaluation declaration.

Checked that the first coordinate kills p>0 and the second kills every p≠1, rather than
merely killing p≥2. Checked E b_H uses the recorded invariant inclusion, k uses I.ι',
and j_rep uses the SAME I, not independent resolutions. Checked sigma's domain is
Q(Gamma_model I) and codomain RGamma_H(R), so every factor of the roof and cancellation
has the stated domain and codomain. There is no normalization inferred from H-zero alone.
The comparison C retains theta alpha=Qb on every bounded-below complex. No statement
correction, missing hypothesis, hollow data or additional mathematical assumption remained.

Validation: every compiler call uses scompile.py in module mode; final clean compile and
mandatory deliver2.py preflight/dry-run results are recorded by the delivery wrapper.
