## Worker report

Added `lean/Sheaf/CategoryTheory/InfinityCocartesianEquivalenceLift.lean`, containing
`SSet.Enhanced.infinity_cocartesian_equivalence_lift`, with its sole proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The item node changes only in `lean`.

The previous worker's stale-assignment diagnosis confused stages: ND's 2026-10-17
13:56 merge, recorded in the ledger and ND report, supplies the stage-1 split.
The current item has status `split`, no Lean record and no Lean review. This delivery
leaves that split intact and supplies its missing stage-2 statement.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed sufficiently large universes; small quasicategories E and B | Explicit `universe u`, `{E B : SSet.{u}}`, `[Quasicategory E] [Quasicategory B]` in both conjuncts. Every pair of small objects can be placed in a common sufficiently large universe. |
| A simplicial map p : E -> B | `(p : E ⟶ B)` in both conjuncts. |
| p an inner fibration, for the first assertion | `[InnerFibration p]`, Mathlib's inner-horn lifting condition. |
| An edge u : x -> y | `(e : E _⦋1⦌)`; its endpoints are intrinsically `E.δ 1 e` and `E.δ 0 e`, so separate x,y binders and endpoint equalities are unnecessary. |
| That edge is p-cocartesian | `IsCocartesianEdge p (SSet.yonedaEquiv.symm e)`, using the recorded outer-horn predicate and the canonical Yoneda conversion from a 1-simplex to a map from Delta[1]. |
| p(u) is a base equivalence | `IsEquivalenceEdge B (p.app _ e)`, with exactly the recorded inverse-triangle definition. |
| u is an equivalence in E | `IsEquivalenceEdge E e`. |
| No existence of other lifts for the first assertion | The first conjunct assumes neither cocartesianFibrationOver nor IsIsofibration; its only edge assumption is for this e. |
| Consequently every cocartesian fibration between quasicategories is an isofibration | The second conjunct quantifies independently over E,B,p and states `cocartesianFibrationOver p → IsIsofibration p`. Its premise already includes InnerFibration p; no redundant extra instance or extra hypothesis is imposed. |
| Every equivalence p(x) -> b has an equivalence lift with source x | Unfolding the existing `IsIsofibration` gives the source equation `E.δ 1 e' = x`, equivalence of e', and the exact image equality `p.app _ e' = e`; the target is forced to lie above b by naturality. It also includes the required quasicategory and inner-fibration conditions. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`;
  Mathlib's `SSet`, `Quasicategory`, and `SSet.yonedaEquiv` are used directly.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`:
  `SSet.Enhanced.cocartesianFibrationOver`, publicly reexporting
  `Sheaf.CategoryTheory.InfinityFibrations` and its
  `SSet.Enhanced.IsCocartesianEdge`; `SSet.InnerFibration` is Mathlib's definition.
  The recorded generalized predicate has the same formula as
  `cocartesianFibration` on the quasicategories already assumed here.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`:
  `SSet.Enhanced.IsIsofibration`. Read the definition's full source, exact lifting
  conditions, and the recorded theorem's full signature and docstring.

All recorded proof-dependency modules are imported without `public`:
`Sheaf.CategoryTheory.RightPinchComparison` (`right_pinch_comparison`),
`Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`
(`infinity_cocartesian_mapping_criterion`),
`Sheaf.CategoryTheory.InfinityMappingComposition` (`mapping_composition`),
`Sheaf.AlgebraicTopology.RealizationWeakEquivalence`
(`realization_weak_equivalence_iff_kan_targets`),
`Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`
(`kan_homotopy_pullback_invariance`),
`Sheaf.AlgebraicTopology.KanPullbackPathComparison` (`kan_pullback_path_comparison`),
and `Sheaf.AlgebraicTopology.KanRealizationSerre` (`SSet.kan_realization_serre`).
The other two proof dependencies are already public statement imports.
All names above except the explicitly prefixed last name are in `SSet.Enhanced`.
The theorem docstring carries the five-step natural-language proof from the DAG,
including the homotopy-pullback comparison and the two-object cancellation argument.

Source checked: [HTT Proposition the project server](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
printed page 116, gives the cartesian equivalence criterion under exactly the inner
fibration and quasicategory hypotheses; its cocartesian dual gives the first clause.
Definition the project server, dualized, supplies lifts for the consequence. No change to the
node statement or proof route was needed.

Edge cases checked before writing: an empty total quasicategory has no edge or
vertex obligations, and no artificial nonemptiness assumption appears. An empty
base admits no nonempty total space mapping to it. Discrete quasicategories reduce
the equivalence condition to identity arrows. Degenerate/identity base equivalences
are included by `IsEquivalenceEdge`. The first assertion allows an inner fibration
that lacks cocartesian lifts for other edges. The second quantifies over every
outgoing equivalence at every prescribed source through the existing IsIsofibration,
with strict equality of its image, not an unspecified equivalent edge. Both clauses
retain arbitrary quasicategories and allow empty mapping spaces.

Searches performed on 2026-10-17:

- `msearch.py leanfinder`: "A cocartesian edge of an inner fibration over an
  equivalence is an equivalence in a quasicategory". Eight ordinary-category hits;
  closest is `CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso`.
- `msearch.py loogle`:
  `CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso`. One exact
  name hit. Read its full signature and docstring in
  `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean`, lines 340--354:
  the input is an ordinary functor and a strongly cocartesian ordinary morphism,
  not a simplicial inner fibration and horn-cocartesian edge, so it is not a match.
- `msearch.py grep`: `cocartesian.*equivalence|isIso_of_base_isIso|IsCocartesianEdge`.
  Two hits, the ordinary cartesian and cocartesian lemmas above; no exact match.
- `rg` in the upstream `WeilConjectures` source and project `lean/Sheaf`:
  `cocartesian.*equivalence|equivalence.*cocartesian|isEquivalence.*[Cc]ocartesian|isofibration.*cocartesian`;
  no existing declaration of this statement. Project hits are comments and
  different cocartesian constructions.
- Upstream search for the exact item identifier: no hits.
- `rg` in both source trees:
  `cocartesian_equivalence_lift|cocartesianFibration.*[Ii]sofibration|IsCocartesianEdge.*IsEquivalenceEdge|IsEquivalenceEdge.*IsCocartesianEdge`;
  only an unrelated relative-join signature with two separate hypotheses.

Validation: prescribed `scompile.py NC lem-coef-infinity-cocartesian-equivalence-lift`
compiled the delivered file successfully both in its sandbox and at its intended
module path, with no errors or warnings. All variables and universes are explicitly
bound; the only postponed proof is the named theorem matching this DAG node.
No mathematical dispute or dependency interface fault was found.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
