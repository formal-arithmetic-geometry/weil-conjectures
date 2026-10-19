## Worker report

The delivery states `CategoryTheory.SmallObject.exists_cellular_factorization_of_isLocallyPresentable`
in `lean/Sheaf/CategoryTheory/PresentableCellularFactorization.lean`. Its sole proof is `sorry`.
No definitions, other DAG statements, dependency repairs, or statement corrections were needed.
The item's JSON copy changes only `lean`.

### Hypotheses and conclusions

| Node clause | Lean rendering and interpretation |
| --- | --- |
| Category with Hom sets in the fixed universe U | `{C : Type u} [Category.{v} C]`; U is `v`, while the object universe `u` is unrestricted. |
| All U-small colimits | `[HasColimitsOfSize.{v, v} C]`. This uses the dependency's Mathlib colimit/cocone interface. |
| Locally presentable for some infinite regular lambda in U | `[IsLocallyPresentable.{v} C]`. Its `exists_cardinal` field supplies `κ : Cardinal.{v}`, `Fact κ.IsRegular`, and `IsCardinalLocallyPresentable C κ`. `Cardinal.IsRegular` includes infinitude. |
| A U-small collection P of lambda-presentable generators, every object a lambda-filtered colimit of them | The preceding Mathlib class extends `HasCardinalFilteredGenerator C κ`. That class supplies an essentially U-small object property, whose `IsCardinalFilteredGenerator` fields are `le_isCardinalPresentable` and `exists_colimitsOfShape`. Essential smallness is precisely the availability of a U-small representative family; repeated/isomorphic representatives do not change generation. |
| Hom(P,-) preserves those filtered colimits | `IsCardinalPresentable P κ` is `(coyoneda.obj (op P)).IsCardinalAccessible κ`; this quantifies over all U-small `κ`-filtered indexing categories. |
| lambda-filtered and regular have the stated meanings | Mathlib `IsCardinalFiltered` supplies cocones for diagrams with fewer than `κ` morphisms; regularity is the regular infinite cardinal condition used throughout the presentability API. These are existing Mathlib notions, not new assumptions. |
| I is a U-small set of morphisms | `{ι : Type v} {A B : ι → C} (i : ∀ s : ι, A s ⟶ B s)` and `MorphismProperty.ofHoms i`. Indexing a set as a family is equivalent; repeats impose no restriction or extra conclusion. |
| Every f:X→Y | `{X Y : C} (f : X ⟶ Y)`. No restrictions on their presentability, on codomains of `i`, or on monicity. |
| There exist Z, j:X→Z, p:Z→Y | `∃ (Z : C) (j : X ⟶ Z) (p : Z ⟶ Y)`. |
| pj=f | `j ≫ p = f`, using Lean's left-to-right composition convention. |
| Right lifting against I | `(MorphismProperty.ofHoms i).rlp p`. Unfolding `rlp` asks for `HasLiftingProperty (i s) p` for every family member. A square with top `a`, bottom `b`, and equation `a ≫ p = i s ≫ b` has a filler `h` with `i s ≫ h = a` and `h ≫ p = b`, exactly the node's equations. |
| j is a small transfinite composition of pushouts of small coproducts from I | `MorphismProperty.transfiniteCompositions.{v} (MorphismProperty.coproducts.{v} (MorphismProperty.ofHoms i)).pushouts j`. There is no retract operation or lifting-only surrogate in this clause. |
| A small ordinal presentation, initial X, final Z, and composite j | `transfiniteCompositions_iff` unfolds the previous clause to a U-small well-ordered type `J`, with `LinearOrder`, `SuccOrder`, `OrderBot`, `WellFoundedLT`, and a `TransfiniteCompositionOfShape` witness. Its fields `F`, `isoBot`, `incl`, `isColimit`, and `fac` give the stages, initial identification with X, cocone to Z, final colimit identification, and composite j. |
| Successor transitions are pushouts of U-small coproducts of I-maps | The morphism-property structure's `map_mem` puts every nonterminal successor transition in the displayed `.pushouts` property. `pushouts` supplies an `IsPushout` square with a map in `coproducts.{v} (ofHoms i)`. `coproducts_iff` supplies a `T : Type v` and a colimit map over `Discrete T`, with every component in `ofHoms i`. These are precisely the indicated coproduct and attaching maps. |
| Continuity at every nonzero limit, including the final stage when it is a limit | The underlying composition structure has `isWellOrderContinuous : F.IsWellOrderContinuous`. This gives the colimit over `Set.Iio β` at every nonzero limit element. Its `isColimit` field supplies the final colimit when the indexing order has no greatest element. |

The well-ordered-type packaging is the existing Mathlib ordinal-composition notion, not a
restriction to countable chains or to successor ordinals. For a chain indexed below a limit
ordinal, `Z` is its final colimit. If the order has a greatest element, that stage is isomorphic
to `Z`, and one may use its position as the final ordinal. Thus the small well-order can be
reindexed by its small order type and, when necessary, have the final colimit adjoined. The
initial and final identifications are categorical identifications, which can be transported
to literal endpoints. Conversely, the node's continuous chain gives exactly this Mathlib
witness. Isomorphisms at endpoints and coproducts are the usual colimit identifications;
they do not add a retract or change the factorization's two maps.

### Dependencies and inspected interfaces

The sole statement dependency is `def-weil-pbc-category-colimit`. I read its full statement,
`lean` record, and `mathlib_match`, then inspected
`Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
`colimit.cocone`, `colimit.ι`, and the generated dual of `limit`. The statement uses
`HasColimitsOfSize`, while the cellular witness uses `Cocone` and `IsColimit`, from the same
Mathlib universal-property interface. `Mathlib.CategoryTheory.Limits.HasLimits` is a direct
public import.

I also read the actual Mathlib definitions and docstrings of `IsLocallyPresentable`,
`IsCardinalLocallyPresentable`, `ObjectProperty.IsCardinalFilteredGenerator`,
`IsCardinalPresentable`, `Functor.IsCardinalAccessible`, `MorphismProperty.ofHoms`, `rlp`,
`pushouts`, `coproducts`, `transfiniteCompositions`, both
`TransfiniteCompositionOfShape` structures, and `Functor.IsWellOrderContinuous`.

The stated proof dependencies are imported directly: object presentability from
`Mathlib.CategoryTheory.Presentable.LocallyPresentable` (public because it also occurs in the
signature); `HasCardinalLT.exists_regular_cardinal` from
`Mathlib.SetTheory.Cardinal.HasCardinalLT`; `WellFoundedLT.fix`/`fix_eq` from
`Mathlib.Order.RelClasses`; filtered-set colimit surjectivity and element equality from
`Mathlib.CategoryTheory.Limits.Types.Filtered`. The last three imports are proof-only.
The source blueprint paragraph and all eight DAG proof steps were read. The docstring
carries all eight steps, including the coherent recursion invariant, limit colimits,
smallness of all attaching squares, and the empty-family case.

### Edge cases

The generator index `ι` may be empty. Then right lifting is vacuous; empty coproducts and
pushouts of their initial-object maps are allowed. Attaching sets at individual stages may
also be empty. No `Nonempty ι` or nonempty-cell condition appears. Isomorphisms and identity
maps admit cellular presentations with no cells (for example the one-point indexing order).
Finite chains, infinite successor chains, and arbitrary U-small limit chains are covered by
the well-order formulation. The initial object and zero objects require no special assumption.
The category's object universe is independent of the Hom/colimit universe. There is no
assumption that all objects, all codomains, or the given `f` are presentable at the same
preassigned rank. The supplied local-presentability condition uses an existential regular
rank, exactly as the node does.

### Searches

All remote search calls used `msearch.py Q31 lem-coef-presentable-cellular-factorization`;
`searches.jsonl` retains their exact results.

- LeanFinder: `locally presentable category cellular factorization right lifting property`:
  eight hits, including `SmallObject.rlp_πObj`, `hasFunctorialFactorization`, and
  `MorphismProperty.IsCardinalForSmallObjectArgument`.
- Loogle: `CategoryTheory.SmallObject, IsLocallyPresentable, RelativeCellComplex`: no hits;
  the service reported the namespace was not an identifier. Repeated with the valid query
  `"HasSmallObjectArgument"`: eight hits, including the class and its retract characterization.
- LeanSearch: `In a locally presentable category any small set of morphisms has cellular
  factorizations`: eight hits; the local-presentability class, general factorization data,
  and model-category instances, with no exact whole-item match.
- Mathlib grep through msearch, query
  `IsLocallyPresentable|HasSmallObjectArgument|RelativeCellComplex` in
  `CategoryTheory/Presentable`: 14 hits for the existing local-presentability infrastructure.
- Mathlib grep through msearch, query
  `cellularFactorization|cellular_factorization|IsLocallyPresentable.*[Ff]actor|[Ff]actor.*IsLocallyPresentable`:
  zero hits.
- Direct `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib for local
  presentability, right lifting, transfinite composition, and small-object arguments.
  No whole-item declaration. The project `GeneratingSetCotorsionSmallness.lean` only cites
  this node in its proof docstring; it does not state its general result.
- Direct tag search for `lem-coef-presentable-cellular-factorization` in upstream:
  no declaration. Name searches for `exists_cellularFactorization_of_isLocallyPresentable`
  and `exists_cellular_factorization_of_isLocallyPresentable` in Mathlib, upstream,
  project Lean and `dag/lean_names_upstream.json`: no collisions.

I inspected `SmallObject/IsCardinalForSmallObjectArgument.lean` at the class, factorization
maps, `ιObj_πObj`, `relativeCellComplexιObj`, `transfiniteCompositionsOfShape_ιObj`, and
`rlp_πObj`, and `SmallObject/Basic.lean` at `HasSmallObjectArgument` and its consequences.
These provide the desired construction after a technical smallness assumption; they do
not state the arbitrary-small-family result under local presentability. Therefore none is
an exact `existing: true` binding. Their constituent definitions are reused directly.

No statement fault or STATEMENT-DISPUTED issue was found. No maintenance repair note for
this item was present.

### Validation

`scompile.py Q31 lem-coef-presentable-cellular-factorization
lean/Sheaf/CategoryTheory/PresentableCellularFactorization.lean` passed on 2026-10-16.
The wrapper compiled the sandbox and library paths separately in 1.5 s and 1.8 s, with no
errors or warnings. All universes and binders are explicit, and `autoImplicit` is false.
The required `deliver2.py Q31 lem-coef-presentable-cellular-factorization --no-push`
dry run printed OK (commit `a28af25602`): compilation and preflight passed except for the
independent second reading, which the second reader supplies. Nothing was pushed.

## Second reading by Q31

I independently opened the item node, its blueprint source place, the sandbox module,
and the recorded dependency `def-weil-pbc-category-colimit`. The source place is the
generic cellular refinement in proof paragraph 2 of
`prop-coef-integral-exceptional-adjoint.md`; it explicitly has no Stacks tag for this
whole statement. The node's clauses and their Lean rendering are:

| Node clause | Lean rendering | Verdict |
| --- | --- | --- |
| A category with Hom sets in the fixed universe and all fixed-universe small colimits | `{C : Type u} [Category.{v} C] [HasColimitsOfSize.{v, v} C]` | exact; `v` is the fixed Hom/index universe and `u` remains unrestricted |
| Local presentability at an infinite regular cardinal, with a small presentable generating family and preservation of filtered colimits | `[IsLocallyPresentable.{v} C]` | exact; Mathlib's class supplies an existential regular `Cardinal.{v}`, an essentially `v`-small filtered generator, presentability (hence Hom preservation), and the required colimits |
| A fixed-universe small family of arrows | `{ι : Type v} {A B : ι → C} (i : ∀ s : ι, A s ⟶ B s)` | exact; dependent domains and codomains allow arbitrary arrows and the empty family |
| Every `f : X ⟶ Y` admits `X ⟶ Z ⟶ Y` with composite `f` | `∃ (Z : C) (j : X ⟶ Z) (p : Z ⟶ Y), j ≫ p = f` | exact, including arbitrary `X`, `Y`, and `f` |
| The second map has right lifting against every member of the family | `(MorphismProperty.ofHoms i).rlp p` | exact; `HasLiftingProperty` gives `i ≫ h = a` and `h ≫ p = b` for every commutative square |
| The first map is a transfinite composite of pushouts of small coproducts of family maps | `MorphismProperty.transfiniteCompositions.{v} (MorphismProperty.coproducts.{v} (MorphismProperty.ofHoms i)).pushouts j` | exact; `coproducts` permits every `Type v`-small family and `pushouts` is the stated cobase-change property |
| Explicit ordinal stages, initial `X`, final `Z`, successor pushout cells, and continuity at nonzero limits including the final limit | the preceding Mathlib transfinite-composition property | exact up to the standard well-order packaging: Mathlib's `J : Type v` with `LinearOrder`, `SuccOrder`, `OrderBot`, and `WellFoundedLT` is order-isomorphic to a `v`-small ordinal, while `IsWellOrderContinuous` supplies all nonzero limit colimits and `isColimit` supplies the final colimit |

No hypothesis or conclusion was added, removed, weakened, or strengthened. In particular,
no presentability of `X`, `Y`, or the codomains of the generating arrows is assumed, and
no retract clause is present. Composition uses Lean's convention, so `j ≫ p = f` is the
node's `pj=f`.

The edge cases were checked directly. The index type `ι` may be empty; then the lifting
condition is vacuous and the coproduct/cell clauses allow empty families. Individual
attaching coproducts may also be empty. Identity and zero or initial maps are included by
the transfinite property. Finite, successor, and arbitrary small limit chains are covered,
and the object universe `u` is independent of the fixed Hom universe `v`. The cardinal
regularity supplied by `Fact κ.IsRegular` is the infinite regular cardinal condition used
by the node.

For the duplicate check I ran `msearch.py` LeanFinder, Loogle, and LeanSearch queries for
locally presentable cellular factorizations and small-object arguments, and searched the
source repository, Mathlib, project `lean/Sheaf`, and `dag/lean_names_upstream.json` with
`rg`. The only related declarations are Mathlib's `SmallObject` constructions, which
require the separate `IsCardinalForSmallObjectArgument`/`HasSmallObjectArgument` premise,
and the distinct DAG statement `lem-coef-presentable-small-object-factorization` about
functorial factorizations. None states this arbitrary-small-family existential cellular
factorization. The exact theorem name also has no collision.

I found no mismatch and changed no Lean declaration or node statement. The worker module
was recompiled with `scompile.py`; it has only the intended `sorry` proof warning and no
errors or other warnings. The dependency's recorded Mathlib colimit interface was used as
written; no dependency repair or statement correction is needed.
