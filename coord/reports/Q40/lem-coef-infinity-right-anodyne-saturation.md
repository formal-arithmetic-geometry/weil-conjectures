## Worker report

The module `Sheaf.AlgebraicTopology.RightAnodyneSaturation` states
`SSet.Enhanced.weaklySaturated_cartesianPushoutProduct`. It takes a morphism property
`W` on simplicial sets and a hypothesis `hW : WeaklySaturated W`, where the latter is
the existing project definition in
`Sheaf.AlgebraicTopology.PushoutJoinSaturation`. It concludes two clauses: for each
fixed monomorphism `k`, the property on `i` consisting of `Mono i` and membership of
the canonical Cartesian pushout-product map in `W` is weakly saturated; and symmetrically
for each fixed monomorphism `i` and varying `k`.

The Lean rendering of the hypotheses is `(W : MorphismProperty SSet.{u})` and
`(hW : WeaklySaturated W)`. In the first conclusion, `k : K ⟶ L` and `Mono k` are
bound, and the class is
`fun {A B} (i : A ⟶ B) ↦ Mono i ∧ W
(Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i k).ι`.
In the second conclusion, `i : A ⟶ B` and `Mono i` are bound, and the class is
`fun {K L} (k : K ⟶ L) ↦ Mono k ∧ W
(Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i k).ι`.
The displayed `ofHasPushout` map is the canonical map from
`(A × L) ⨿[A × K] (B × K)` to `B × L` for the cartesian tensor, matching the node's
`theta_{i,k}`.

The existing declarations used are:

- `SSet.Enhanced.WeaklySaturated` module declaration in
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation` (the predicate itself is defined
  there and is reused rather than copied);
- `CategoryTheory.Functor.PushoutObjObj.ofHasPushout` from
  `Mathlib.CategoryTheory.Monoidal.PushoutProduct`;
- `CategoryTheory.MonoidalCategory.curriedTensor` for the cartesian tensor on `SSet`;
- `CategoryTheory.Mono` and `CategoryTheory.MorphismProperty` from Mathlib.

Edge cases checked against the statement are: an isomorphism in either variable (the
pushout-product map is an isomorphism), `K` empty (the map reduces to the product with
`L`), `A` empty and `B = Δ⁰` (the map reduces to `k`), zero-length transfinite chains,
and pushouts along non-injective attaching maps. These are included by the unrestricted
simplicial-set binders and the four closure clauses of `WeaklySaturated`.

Searches made:

- `msearch.py ... grep 'WeaklySaturated' CategoryTheory`: no Mathlib declaration of
  the combined weak-saturation assertion; hits were generic pushout-product and
  morphism-property infrastructure.
- `msearch.py ... loogle 'WeaklySaturated, MorphismProperty.IsStableUnderTransfiniteComposition'`:
  zero hits; the service reported `WeaklySaturated` as an unknown identifier.
- `msearch.py ... leanfinder 'weak saturation of a class of simplicial maps under pushout product'`:
  generic model-category and morphism-property declarations, no exact theorem.
- `rg` over `WeilConjectures/` and `lean/Sheaf`: no upstream theorem for this
  arbitrary weak-saturation assertion; the project definition of `WeaklySaturated` was
  found in `Sheaf.AlgebraicTopology.PushoutJoinSaturation` and reused.
- The node's recorded grep, Loogle, LeanSearch and LeanFinder searches were also read;
  all report no exact theorem and identify only generic pushout-product infrastructure.

The theorem proof is intentionally `sorry` at stage 2. No statement correction,
new node, dependency module, or `STATEMENT-DISPUTED` flag is needed.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module signature. The `W` binder is exactly a
`MorphismProperty SSet.{u}`, and `hW` is exactly the hypothesis that this class is
weakly saturated. The first universal clause fixes `k : K ⟶ L` and assumes `Mono k`;
its property binds arbitrary `i : A ⟶ B`, requires `Mono i`, and tests the canonical
Cartesian pushout-product map against `W`. The second clause fixes `i : A ⟶ B` and
assumes `Mono i`, then symmetrically varies `k : K ⟶ L` with `Mono k`. No hypotheses
or conclusion clauses were added or omitted. The canonical map is rendered by
`Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i k` in both clauses. The
proof remains `sorry` as required for stage 2, and the recorded signature now matches
the declaration text before `:=`.

## Second reading by Q40

I read the node `lem-coef-infinity-right-anodyne-saturation`, its source place (Kerodon
Proposition the project server, tag 0153), the dependency records, and
`Sheaf/AlgebraicTopology/RightAnodyneSaturation.lean` independently.

The node's objects and hypotheses match the Lean one by one. `W` is rendered as
`W : MorphismProperty SSet.{u}`, and the hypothesis that it is weakly saturated is
`hW : WeaklySaturated W`, using the existing `SSet.Enhanced.WeaklySaturated` definition
from `PushoutJoinSaturation`. The first conclusion fixes `k : K ⟶ L` with `Mono k` and
returns `WeaklySaturated` for the property
`fun {A B} i ↦ Mono i ∧ W (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i k).ι`.
The second fixes `i : A ⟶ B` with `Mono i` and symmetrically returns the property
`fun {K L} k ↦ Mono k ∧ W
(Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i k).ι`.
The `ofHasPushout` map is the canonical map from
`(A × L) ⨿[A × K] (B × K)` to `B × L`, so its orientation and objects agree with
`theta_{i,k}`. The `Mono` conjuncts encode exactly the node's restriction to classes of
monomorphisms; no additional hypothesis is introduced, and no conclusion clause is
omitted or weakened.

The source proof first identifies the pushout-product domain degreewise with the union
`(A × L) ∪ (B × K)`, then proves functoriality, closure under isomorphisms, arbitrary
pushouts, continuous small ordinal compositions, and retracts in each variable. This is
exactly the proof carried by the node's ten proof steps; the generalized arbitrary `W`
statement uses only the four closure clauses of `WeaklySaturated`. The empty simplicial
set, empty index factors, isomorphisms, zero-length ordinal chains, arbitrary attaching
maps, and the `A = ∅`, `B = Δ⁰` case are all admitted by the unrestricted `SSet.{u}`
binders and by the `Mono`/`WeaklySaturated` predicates.

I searched Mathlib and the project/source repositories with grep, LeanSearch, Loogle,
and LeanFinder using pushout-product, weak-saturation, transfinite-composition, and
Cartesian-product queries. I found only generic `PushoutObjObj` and morphism-property
infrastructure; no declaration states this theorem. The existing
`SSet.Enhanced.WeaklySaturated` definition is therefore reused, not copied. No repair
note applies, no new node or dependency module is required, and no mismatch was found
or changed. The required `scompile.py` check succeeds with only the permitted `sorry`.
