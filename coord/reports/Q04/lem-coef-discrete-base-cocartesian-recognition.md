## Worker report

The module `Sheaf.CategoryTheory.DiscreteBaseCocartesianRecognition` states
`SSet.Enhanced.DiscreteBaseCocartesianRecognition.discrete_base_cocartesian_recognition`.
Its only theorem has proof `sorry`. All four helper constructions and the hypothesis
structure have real data; nothing is selected from an unproved existence theorem.
No node statement or dependency record is changed, and no new node is needed.

Source read: https://arxiv.org/html/1312.3881v4, Theorem 4.21, proof, specifically
its componentwise homotopy-pullback calculation and two-out-of-three argument.
The additional intrinsic-fibre conclusion is the node's explicitly extracted six-step
argument. The theorem docstring carries those six steps and their named dependencies.

Clause-by-clause correspondence (names below are in the module's namespace):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small ordinary category C | `(C : Type u) [Category.{u} C]`; u is an arbitrary common containing universe. |
| Infinity category X and coherent p to NC | `(X : SSet.{u}) [Quasicategory X] (p : X ⟶ nerve C)`. |
| Each small infinity category D_c | `Data.D`, `Data.quasicategory`. |
| Coherent i_c with specified constant composite p i_c=c | `Data.i`, `Data.over`, the latter an equality of whole simplicial maps with `SSet.const (ComposableArrows.mk₀ c)`. |
| Every vertex is literally i_c(x) | `Data.vertices`, with equality, not merely essential surjectivity. |
| f_!x | `(Data.push f).app _ x`; the map `push f : D c ⟶ D d` retains its stipulated coherence in source morphisms. |
| Edge u_{f,x} with the specified endpoints | `Data.u f x`, a vertex of the existing fixed-endpoint `arrowMappingSpace`; its actual edge is `arrowUnderlyingEdge X _ _ (A.u f x)`. |
| All lifts over f and coherent in endpoints | `Data.lift : D c ⟶ (ihom Δ[1]).obj X`, `lift_source`, `lift_target`, `lift_vertices`, `lift_over`. These equalities hold on entire simplices, not just objects. |
| Identity objects and identity edges | `Data.identity_objects`, `Data.identity_edges`, with the degenerate edge `X.σ 0 ((i c).app _ x)`. |
| g_!(f_!x)=(gf)_!x | `Data.composition_objects`. Composition is Mathlib order `f ≫ g`. No strict equality of transport functors is imposed. |
| Specified compositional triangle over N(c→d→e) | `Data.triangle`, `triangle_first`, `triangle_second`, `triangle_composite`, `triangle_over`. The three ordered edges are 01,12,02, and the base simplex is `ComposableArrows.mk₂ f g`. These families retain source endpoint simplices in every degree. |
| Isomorphisms lift to equivalences | `Data.isomorphisms`, using `IsIso f` and the dependency's `IsEquivalenceEdge`. |
| Actual map Map_Dd(f_!x,y) → Map_X(i_cx,i_dy)_f | `Data.comparisons`, with domain `comparisonSource`, target `component`, and its normalization through `componentInclusion` equal to `comparisonLongEdge`. |
| That actual comparison is an equivalence | `IsWeakHomotopyEquivalence q` in `Data.comparisons`. |
| Comparisons coherent in endpoint morphisms | They are forced by the canonical triangle roof and the actual simplicial map `i d`; the inclusion equation is on whole simplicial maps. The inclusion is monomorphic, so this is not a freely chosen equivalence. The `lift`/`triangle` families retain coherence in the varying source endpoint as well. |
| All data fit fixed containing universes | Every D_c, X, NC and mapping object is formed in the common arbitrary universe u; the family of all such data is allowed to live in u+1. No nonemptiness or dimension restriction is imposed. |
| Every u is intrinsically p-cocartesian | First conclusion: `CocartesianStraightening.IsIntrinsicEdge p` of the actual underlying lift. |
| p admits a simplicial cocartesian representative over NC | Second conclusion: E,q,j, with `Quasicategory E`, `cocartesianFibrationOver q`, `IsFunctorEquivalence j`, and `j ≫ q = p`. |
| Canonical D_c → intrinsic fibre is an equivalence | Third conclusion: j into `fiber p (ComposableArrows.mk₀ c)`, its inclusion composite exactly `A.i c`, and `IsFunctorEquivalence j`. The final `pullbackCoreComparison` assertion for every test quasicategory identifies this strict model with the infinity-categorical pullback. |
| Intrinsic fibre, even without an initial inner-fibration assumption | No `InnerFibration p` binder. The universal mapping-core comparison is the dependency's intrinsic pullback test, rather than an assertion about an arbitrary unvalidated strict fibre. |

Details of the mapping comparison: use the recorded arrow mapping spaces, naturally
homotopy equivalent to the node's right-pinched spaces. The fixed-first-edge triangle
roof is `cocartesianPrecompositionSource`. Pull its equivalence projection to Map_X
back along `arrowSpaceMap (i d) (f_!x) y`; this is `comparisonSource`.
Consequently its second projection is an equivalence to Map_Dd(f_!x,y), and its long
edge is exactly h ↦ i_d(h)u_{f,x}. Requiring its long edge into the f-component to be
an equivalence says exactly that the node's actual composition map is an equivalence.
The component is constructed as a strict fibre after inclusion into Fun(Δ¹,NC),
but the image factors through the fixed-endpoint arrow space of NC, which is the
discrete Hom_C(c,d). It is the fibre/homotopy fibre over f of THAT discrete space;
we do not identify it with a homotopy fibre in the entire arrow category of NC.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `diagramVertex`, `evaluation`, `IsWeakHomotopyEquivalence`,
  `IsFunctorEquivalence`, and its coherent-natural-equivalence interpretation.
- `Sheaf.CategoryTheory.CocartesianStraightening`:
  `CocartesianStraightening.IsIntrinsicEdge`, `Statement.pullbacks` and
  `Statement.intrinsic_replacement` (the latter two explain the conclusion and proof).
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` (reexporting
  `InfinityFibrations`): `fiber`, `cocartesianFibrationOver`.
- `Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`:
  `cocartesianPrecompositionSource`, `cocartesianPrecomposition`,
  `infinity_cocartesian_mapping_criterion`.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `mapping_composition`,
  used by the proof plan's associativity and unit homotopies.
- `Sheaf.CategoryTheory.InfinityFullEssentialImage`:
  `fullyFaithful_fullEssentialImage`, used by the proof plan's fibre equivalence.
- Reexported `Sheaf.CategoryTheory.SimplicialCompositionSpine`:
  `spineRestriction`, `binaryArrowPair`, `arrowUnderlyingEdge`, `arrowSpaceMap`.
- Reexported `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `right_pinch_comparison`.
- Reexported `Sheaf.CategoryTheory.IsofibrationPullbackLimit`:
  `pullbackCoreComparison`.
- Mathlib `CategoryTheory.nerve`, `ComposableArrows.mk₀`, `mk₁`, `mk₂`, and
  `CategoryTheory.Nerve.quasicategory` in the nerve modules.

Every recorded statement dependency is imported publicly. Every additional recorded
proof dependency is imported. No dependency interface repair or omission was needed.

Edge cases checked before drafting and reread after compilation:
empty C forces X to have no vertices by `vertices`, and the conclusions are vacuous;
empty individual D_c and empty mapping components are allowed; there is no inhabitance
binder. Identity f uses both stated normalizations. Noninvertible f is allowed.
Different g with the same gf stay separate summands in the proof; no cancellation or
faithfulness condition is assumed. Nontrivial base isomorphisms are included explicitly.
No inner-fibration hypothesis is added: the node's horn/spine argument derives it.
No notion is replaced by ordinary Hom sets, homotopy categories, or arbitrary maps.

Searches for an existing statement:

- `msearch.py leanfinder`: "Recognize a cocartesian fibration of infinity categories
  over an ordinary nerve from mapping space components and identify its intrinsic fibers".
  Eight hits, all ordinary nerve/strict-Segal declarations and nerve adjunctions.
  Read the Mathlib nerve and quasicategory-of-nerve signatures and docstrings; no match.
- `msearch.py loogle`: `"Cocartesian", "Quasicategory"`. Zero hits.
- `msearch.py grep`: `cocartesian|mappingSpace` in `AlgebraicTopology/Quasicategory`.
  Zero hits.
- `msearch.py leansearch`: "Cocartesian fibrations of quasicategories over a nerve
  characterized by mapping space components". Eight hits, ordinary categorical
  cocartesian arrows, Kan-fibration instances, and quasicategory-of-nerve. Read
  Mathlib's `Functor.IsCocartesian` and `IsStronglyCocartesian`: these use ordinary
  Hom-set universal properties and do not state this result.
- `rg` of the read-only upstream `WeilConjectures` for the item id, `DiscreteBase`,
  `discrete_base_cocartesian_recognition`, `IsIntrinsicEdge`, `comparisonSource`:
  no existing statement. `dag/lean_names_upstream.json` has no matching declaration.
- `rg` of `lean/Sheaf/CategoryTheory` for discrete-base recognition, mapping
  components and coherent lifts: found the existing criteria and the consumer
  `GrothendieckFibreLocalization`, whose proof cites this unstated item; no duplicate
  recognition theorem. The module path does not already exist in the shared source.

Validation: prescribed `scompile.py Q04 lem-coef-discrete-base-cocartesian-recognition
<module>` succeeded, both sandbox (3.1 s) and library-path (3.7 s) compiles, with no
errors or warnings. `autoImplicit` is explicitly false. All universes are bound.

No statement dispute, correction, new node, or dependency repair.

## Second reading by Q04

The dispatcher explicitly forbids starting another agent and provides the maintainer's
independent review as the delivery review. This section records a second direct reading
by the same worker; it does not claim an independent worker was started.

Reopened the node and module together and checked each row above. In particular:
`over` fixes all simplices; `vertices` is literal surjectivity; `u` has fixed endpoints;
`lift_over` fixes the whole base arrow, including isomorphisms; the three triangle faces
have the correct 01/12/02 order; strict composition is only on objects; both identity
normalizations are present; and `comparisons` fixes the actual long-edge map through a
monomorphism. The roof replacement changes the mapping-space model, not the hypothesis:
its second projection is an equivalence. The final j is fixed under the actual fibre
inclusion; `pullbackCoreComparison` certifies the intrinsic, rather than merely strict,
pullback. No initial inner-fibration hypothesis or extra conclusion was introduced.
All theorem proofs remain `sorry`; every helper definition contains real construction
data. No mismatch requiring a statement change was found.
