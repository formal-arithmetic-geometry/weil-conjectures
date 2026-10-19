## Worker report

The module `Sheaf/TraceFormula/TwoTermPerfectDeterminant.lean` states the determinant
data theorem for locally two-term perfect complexes.  It defines the two-term model
(including its differential and finite locally free ranks), its associated complex,
the dual-top-exterior determinant line, the identity/contractible model, the local
two-term property, the core groupoid, determinant values and comparison isomorphisms,
the zero object, normalized identity pullback and normalized derived composition lift.  The final theorem
`exists_twoTermPerfectDeterminantData` is stated with proof `sorry`.

The inherited hypothesis `[d : ∀ X : Scheme.{u},
HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]` fixes
the derived-category presentations used throughout; it imposes no geometric condition.
The final theorem's further hypothesis is the explicit family
`[∀ X : Scheme.{u}, ∀ U : X.Opens,
  HasDerivedCategory.{w} (SheafOfModules.{u}
    ((moduleRings X.toRingedSpace).over U))]`.
Its first conclusion clause is, for every scheme `X` and derived object `L`, the
equivalence between `isTwoTermPerfect X L` and `Scheme.IsPerfect X L` together with
vanishing of the homology of `L ⊗ (DerivedCategory.singleFunctor _ 0).obj M` in every
degree `i` satisfying `i < -1 ∨ 0 < i`, for every sheaf module `M`.  Its second
conclusion clause is `Nonempty (TwoTermPerfectDeterminantData.{u, w})`.  The structure
records invertibility, model membership, the exterior-power model comparison, the zero
comparison, normalized evaluation for `[E --id--> E]`, pullback preservation and
comparison, naturality, derived identity normalization, identity pullback, and
composition pullback coherence.

The statement dependencies used are:

* `AlgebraicGeometry.Scheme` — `AlgebraicGeometry.Scheme` (Mathlib).
* `WeilConjectures.AlgebraicGeometry.DerivedCategory` —
  `AlgebraicGeometry.schemeDerivedCategory`.
* `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` —
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
* `WeilConjectures.AlgebraicGeometry.Modules.Invertible` —
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` — `ExteriorAlgebra` and
  `exteriorPower`.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` —
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  public tensor-pullback declarations.

The model uses `HomologicalComplex.double` for degrees `-1` and `0`; rank zero is
allowed.  The identity model was checked at rank zero, and the zero object is included
for empty schemes.  Local ranks are permitted to vary by the open neighbourhood.
Pullback is the recorded canonical tensor pullback and the theorem allows arbitrary
scheme morphisms, including non-flat ones.

The saved `searches.jsonl` records the earlier attempt's successful searches: `leanfinder` for a determinant
functor on two-term perfect complexes, `leansearch` for determinant functors on two-term perfect complexes, `loogle` for determinant/complex declarations, and `grep` over Mathlib
for determinant functors/lines.  They found only ordinary `LinearMap.det`,
`LinearEquiv.det`, and unrelated complex-number determinant declarations; no matching
determinant-line functor exists.  Current `rg` searches of the upstream source, `lean/Sheaf` and the upstream-name index
for `twoTermPerfect|TwoTermPerfect|twoTermDeterminant|TwoTermDeterminant`, and the
upstream source for the exact node id, found no existing declaration
for this node.  No new node, dependency repair, or statement correction was needed.

The first compile repair uses `CoreHom.mk e'`, whose argument is directly an
isomorphism. The self-check also replaced the old arbitrary-adjunction identity and
composition by `tensorPullbackSectionId` and `tensorPullbackSectionComp`. The derived
comparison's hom is explicitly the universal lift of the original counits followed
by the normalized underived comparison. Its invertibility is included in the final
existence theorem, rather than selected from a bare existence theorem. Added the
available proof-dependency imports and a missing source docstring, and renamed the
zero-object helper to `twoTermDeterminantZeroObject` to avoid a generic global name.

The four additionally cited landed nodes provide the precise interfaces already used
by this statement: `def-pc-perfect-complex` (`Scheme.IsPerfect`),
`def-sc-sheaf-exterior-power` (`Scheme.Modules.exteriorSheaf`),
`def-pc-scheme-derived-tensor-structure` (`schemeDerivedTensorMonoidal`), and
`lem-pc-recorded-pullback-composition` (`recordedDerivedPullbackCounit`, its universal
property and the original additive tensor presentation). No new node or dependency
module is delivered.

## Clause-by-clause self-check

| Node clause | Lean rendering |
| --- | --- |
| Every scheme, with no regularity, separation, compactness or characteristic hypothesis | `X : Scheme.{u}` throughout; `g : Y ⟶ X` arbitrary |
| Objects in `D(O_X)` | `L : schemeDerivedCategory X`, using the recorded shared sheaf-module carrier |
| Locally a finite locally free two-term complex in degrees -1,0 | `isTwoTermPerfect`, `TwoTermDeterminantModel`, its `neg_free`/`nonneg_free`, and `HomologicalComplex.double` with indices `-1,0` |
| Equivalent to perfect with tensor Tor window [-1,0] | The first conjunct of `exists_twoTermPerfectDeterminantData`, using `Scheme.IsPerfect`, `singleFunctor _ 0`, derived `⊗`, `homologyFunctor` and `IsZero` outside the window |
| Functor on objects and derived isomorphisms | `TwoTermPerfectCore X := Core (isTwoTermPerfect X).FullSubcategory` and data field `functor` |
| Values are invertible modules and arrows are isomorphisms | Codomain `Core X.Modules`, with field `invertible`; a functor with all values invertible factors through the full invertible-module subgroupoid |
| Dual top exterior power tensored with degree-zero top exterior power | `TwoTermDeterminantModel.line` and `modelIso`; `dual` is the recorded internal sheaf Hom into `O_X` |
| Locally constant ranks | Ranks are arbitrary naturals on each model open; `isTwoTermPerfect` allows a different open/model at every point, with no global rank bound |
| Identity and composition of determinant maps | `Functor.map_id` and `Functor.map_comp` are part of field `functor` |
| Comparisons between models depend on the derived object | `twoTermDeterminantIso` applies the same functor to the actual derived isomorphism, then composes with `modelIso` |
| Zero and contractible identity-model trivialization | Fields `zero_mem`, `zeroIso`, and `acyclic`; the equality is exactly `modelIso.inv` followed by determinant of the unique comparison to zero and `zeroIso.hom`, equal to braiding followed by `dualEvaluation` |
| Arbitrary pullback preserves the object condition | `pullback_mem` |
| Module pullback versus derived pullback | `pullbackIso : (tensorPullback g).obj ... ≅ ... ((derivedPullback g).obj L)` |
| Naturality for isomorphisms of L | `pullback_naturality` |
| Identity pullback | `pullback_id`, with `twoTermDeterminantPullbackId = tensorPullbackSectionId`; `derivedId_normalization` fixes the corresponding derived identity |
| Composition pullback | `pullback_comp`, using `tensorPullbackSectionComp` and `derivedComp`; `derivedComp_normalization` fixes its hom to `twoTermDeterminantDerivedCompositionLift` |
| Restrictions and iterated restrictions | The same arbitrary-morphism naturality/composition fields specialize to open immersions and inclusions among opens |

The self-check reads the current six original dependency signatures and docstrings,
the four additionally cited interfaces, and Stacks `perfect.tex` 0FJX/0FJY and
`more-algebra.tex` 0FJI/0FJM. No statement correction or disputed claim was found.
The dispatcher's maintainer performs the independent delivery review.

## Second reading by NK

I independently read the item node, all ten statement dependencies and their recorded
interfaces, the Stacks source places 0FJX/0FJY/0FJI/0FJM, and the immutable Lean module.
The theorem quantifies arbitrary schemes and arbitrary morphisms, uses the recorded derived
category and tensor pullback, and has no regularity, quasi-compactness, flatness,
characteristic, or universe-equality restriction. `TwoTermDeterminantModel` has the two
terms, differential, rank naturals, and finite-locally-free hypotheses; `complex` places
these terms in degrees -1 and 0. `isTwoTermPerfect` gives the required local restriction
and derived isomorphism. The displayed line is exactly dual exterior power in degree -1
tensored with exterior power in degree 0. `TwoTermPerfectCore` is the core of the full
subcategory, so its functor maps only isomorphisms and supplies identity/composition laws.
The `modelIso`, `zeroIso`, and `acyclic` fields express the model formula, zero comparison,
and evaluation trivialization, including rank zero. `pullback_mem`, `pullbackIso`,
`pullback_naturality`, `pullback_id`, and `pullback_comp` cover arbitrary pullbacks,
restrictions, identity, and composition; the derived composition hom is explicitly the
universal lift of the recorded counits and normalized tensor comparison.

The final equivalence has the node's perfect predicate and vanishing outside degrees
[-1,0] for every degree-zero module, and the local-site derived-category instance is
explicitly bound. The module has source and `(blueprint: lem-trf-two-term-perfect-determinant)`
docstrings, real data in every definition, and only the final existence theorem is
`sorry`. Searches found no existing determinant-line functor. The immutable module compiled
through `scompile.py NK lem-trf-two-term-perfect-determinant ...` in both sandbox and
library paths, exit 0, with no diagnostics beyond the permitted postponed theorem. No
route-pivot machinery, live write, lake/global build, or branch mutation was used.

The original worker section only stated that no worker second reading took place; it was
therefore not a real second reading as required by check-brief2 step 7. This replacement
report preserves the worker report and supplies this independent clause-by-clause reading.
