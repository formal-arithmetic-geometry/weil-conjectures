# Q28 stage-2 delivery

## Worker report

This delivery states `SSet.Enhanced.Algebroid.algebroid_cocontinuous_base_change` in
`Sheaf.CategoryTheory.AlgebroidCocontinuousBaseChange`. It reuses the recorded
`Sheaf.CategoryTheory.CompleteAlgebroid` model throughout. Its only postponed theorem is
the named main theorem, with `sorry`; its docstring contains the current seven-step DAG
proof and all its citations. The four helper definitions have actual construction data. The returned step-3 split
child `lem-coef-cartesian-left-adjoint-transport` is also delivered here with its
statement-only theorem and `sorry` proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small universe is `u`; the containing universe is `max (u + 1) v`, with independent
  arbitrary `v`. `E` and `D` are the total monoidal quasicategories, with explicit
  `[Quasicategory E]` and `[Quasicategory D]`. A common containing universe is used for
  coefficient functors; no equality of unrelated site/object/morphism universes is imposed.
- The monoidal structures are `p` and `r` over `monoidalSimplexBase`, and `hp`, `hr` use
  the existing `IsMonoidalInfinityCategory`. Their underlying coefficient categories are
  precisely `monoidalUnderlying p` and `monoidalUnderlying r`, the fibers at `[1]`.
- Cocompleteness of V and W is `hV`, `hW : SSet.Presentability.HasSmallColimits ...`.
  This predicate uses arbitrary small simplicial indexing shapes, including the empty
  shape; it has no accessibility or local-smallness assumption.
- Separate tensor cocontinuity is `hVtensor`, `hWtensor`. For every binary tensor
  satisfying the existing `IsMonoidalTensorOperation`, every fixed object, and each
  `i : Fin 2`, `tensorWith tensor x i` preserves every small colimit. Thus the functor
  being tested is the actual active operadic tensor, not an arbitrary binary map.
  This is exactly the tensor condition in the recorded `IsPresentablyMonoidal`, with
  presentability replaced by the stipulated cocompleteness. It does not assert that
  colimits of algebras are computed on their underlying objects.
- The node's algebroid categories are the existing `total.{u,v} p` and `total.{u,v} r`.
  The first four conjuncts say these are quasicategories and have all small colimits.
  Quasicategory is the explicit rendering of the node's phrase "infinity categories";
  it is a conclusion, not an added hypothesis on the algebroid model.
- For every strong monoidal `F`, `hF : IsStrongMonoidalInfinityFunctor p r F` records
  its base equation, inert preservation, and preservation of cocartesian edges.
  `underlyingChange F hF` is the literal induced pullback map on the fibers at `[1]`.
  Its `PreservesColimitsIn` premise is exactly cocontinuity of the underlying F.
- The induced F_* is the actual map
  `postcomposeFamily universalFamily.{u,v}.hom F hF`. On a complete total-family
  simplex it leaves the object-space parameter unchanged and applies F to every value
  on every pulled-back relative-nerve simplex. All naturality and over-base equations
  are part of its construction. Inert preservation follows directly from `hF.2`.
  Thus this is composition of operadic algebras and their coherent transformations
  with F, not a chosen functor having only equivalent object values.
- The final `PreservesColimitsIn` conclusion quantifies over every small K, diagram A,
  and specified colimiting cocone t, and asserts that the actual
  `CategoryTheory.Spaces.mappedCocone` is colimiting. Its apex is F_*(apex t) and its
  transformation is postcomposition of all the legs of t. This is the cocone form of
  invertibility of the stated canonical comparison from colim F_*A to F_*(colim A):
  both source and target cocones are colimiting, and their comparison is the one induced
  by these legs. It asserts preservation of the specified cocone, not merely existence
  of some equivalence of its endpoints.
- Neither `IsSmall` nor `HasSmallColimits` nor `PreservesColimitsIn` imposes nonemptiness.
  The empty-diagram clause is therefore included. No `IsPresentable`, accessibility,
  completeness of enriched algebroids, or cocontinuity of an unspecified comparison
  is assumed. The theorem concerns Algd, not its full subcategory of complete objects.

Dependency declarations read and used:

1. `Sheaf.CategoryTheory.CompleteAlgebroid` (recorded dependency
   `def-coef-complete-algebroid`): `TotalSimplex`, `totalAmbient`, `totalFunctor`,
   `IsTotalAlgebra`, `totalForFamily`, `universalFamily`, `total`, and `tensorWith`.
   I read the full source/signatures and their source docstrings. The construction
   retains the universal family on all simplices. No copy of the algebroid definition
   or of its object-space universe is made.
2. From its recorded/transitive dependency `Sheaf.CategoryTheory.MonoidalInfinityCategory`:
   `monoidalSimplexBase`, `monoidalBaseVertex`, `monoidalUnderlying`,
   `monoidalFiberInclusion`, `IsMonoidalInfinityCategory`,
   `IsMonoidalTensorOperation`, `IsStrongMonoidalInfinityFunctor`.
   `Sheaf.CategoryTheory.InfinityFibrations.fiber` is `{b} ×_B E`, so the canonical
   fiber functor is the pullback lift retaining its first projection and applying F
   after its second projection. An initially unresolved pullback law was repaired
   by specifying the existing `pullback.condition`'s implicit `f` and `g` arguments.
3. From `Sheaf.CategoryTheory.PresentableInfinityCategory`:
   `SSet.Presentability.IsSmall`, `HasSmallColimits`, `PreservesColimitsIn`.
   These are the already defined general colimit predicates, despite the module name.
   Preservation uses `CategoryTheory.Spaces.mappedCocone` from
   `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`; it is actual postcomposition.
4. The already stated proof dependencies are imported non-publicly:
   `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus.enhanced_functor_cone_calculus`,
   `Sheaf.CategoryTheory.ParametricUniversalArrows.parametric_universal_arrows`, and
   `Sheaf.CategoryTheory.PointwiseCocartesianTransport.pointwise_cocartesian_transport`
   (their namespaces are `SSet.Enhanced`, not the module paths). I read their theorem
   signatures and proof docstrings. The split child
   `Sheaf.CategoryTheory.CartesianLeftAdjointTransport` states
   `SSet.Enhanced.cartesian_left_adjoint_transport`; it uses the recorded
   `InfinityFibrations` predicates and `ModelInfinity.CoherentAdjunction`. The other
   proof nodes have no recorded Lean declarations in the shared DAG inspected for this
   delivery and need no import yet.

Edge cases checked semantically before the final statement:

- Empty K gives the initial algebroid with empty object space. The smallness predicate
  allows K empty and the preservation conclusion tests its actual initial cocone.
- Identity F gives literal identity on each total-family value; a point-shaped diagram
  therefore has its identity comparison. The helper definitions make no Nonempty choice.
- Empty object spaces are present in the universal small-space family, and none of the
  definitions or hypotheses selects an object from them. The ordinary-operad replacement
  and free-extension argument remain in the retained DAG proof.
- Single-object algebroids include associative algebra examples. No underlying-object
  computation of arbitrary algebra coproducts is asserted.
- Different large coefficient sizes embed in a common arbitrary containing universe.
  The fixed u of small spaces and colimit shapes is retained in every colimit predicate
  and every occurrence of `total`; `v` has not been specialized to u or zero.

Searches made (all semantic Mathlib queries use the prescribed `msearch.py`; exact
returned records are retained in sandbox `searches.jsonl`):

- Retained Q28 LeanFinder query: "A colimit preserving strong monoidal functor induces
  a small colimit preserving change of enrichment on operadic infinity algebroids".
  Eight ordinary enrichment-transport hits, no operadic algebroid theorem.
- LeanSearch query: "Change of enrichment preserves small colimits in the infinity
  category of operadic algebroids without presentability". Eight ordinary enriched
  conical-limit/colimit-preservation hits; no matching statement.
- LeanFinder query: "A colimit preserving strong monoidal functor induces a colimit
  preserving functor on operadic algebroids in infinity categories". Eight ordinary
  Action and Monad colimit hits; no matching statement.
- Loogle query `"Enriched", "PreservesColimits"`: zero hits, both in the retained
  search log and on this repair run.
- Mathlib grep query `algebroid|Algd|postcomposeFamily|underlyingChange`, subdirectory
  CategoryTheory: zero hits. The retained `algebroid|Algd|changeOfEnrichment` grep also
  returned zero hits.
- Direct rg in the named upstream WeilConjectures tree, the shared lean/Sheaf tree,
  and `dag/lean_names_upstream.json`, for the node id and all new declaration names:
  no existing declaration. Broader algebroid/Algd/coefficient-change searches found
  the recorded CompleteAlgebroid definition and ordinary site cocontinuity material.
- I opened Mathlib `CategoryTheory/Enriched/Basic.lean` (class `EnrichedCategory`),
  `Action/Limits.lean` (mapAction colimit preservation), `Monad/Limits.lean`
  (`forget_creates_colimits_of_monad_preserves`), and
  `AlgebraicTopology/Quasicategory/StrictBicategory.lean` (`QCat` Cat-enrichment).
  They concern ordinary enriched categories/actions/monads or the Cat-enrichment
  obtained by homotopy categories of internal Homs; none is the required varying
  object-space infinity category or its cocontinuity theorem. No exact existing
  match or duplicate helper declaration was found.

Sources read online:
[Haugseng Observation 3.9](https://arxiv.org/html/2311.13362v1) and
[Gepner--Haugseng Proposition 3.6.10, Lemma 4.3.7, and Proposition 4.3.14](https://arxiv.org/html/1312.3178).
The cocomplete argument uses fiberwise colimits and cocartesian-arrow preservation;
Proposition 4.3.14's presentability formulation is not used to add that hypothesis.
No source archive was written outside the sandbox.

## New nodes

The retained current DAG already contains the stage-1 split child
`lem-coef-cartesian-left-adjoint-transport`, created for the former 2279-character
step 3. I copied that node unchanged and added only its `lean` record. Its module
`Sheaf.CategoryTheory.CartesianLeftAdjointTransport` states the Cartesian-fibration
criterion with simplicial restriction maps `R`, a coherent Cartesian transformation `τ`
identifying them with actual transport, and coherent adjunction witnesses `hR`. It
concludes cocartesian lifts with specified target `L x` and a triangle identifying them
with each specified adjunction unit. The module has no
additional definition and postpones only the named theorem. The child is cited by the
main node's existing step 3 and `proof_deps`; no dependency cycle is introduced.

## Dependency modules

The split child `lem-coef-cartesian-left-adjoint-transport` had no Lean record on the
shared DAG. I added its module `Sheaf.CategoryTheory.CartesianLeftAdjointTransport`
and the declaration `SSet.Enhanced.cartesian_left_adjoint_transport`. The module states
the child notion using the existing `SSet.Enhanced.cartesianFibration`,
`cocartesianFibration`, `fiber`, `IsCocartesianEdge`, and
`HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`; it does not copy or redefine
any dependency notion. Its `lean.note` records the repair: `τ` is a Cartesian
transformation over the base edge, so `R` is actual restriction; the conclusion includes
the specified unit and target. The recorded fibration dependency module
`InfinityFibrationsOverSimplicialBases` is imported and reexports the original interface.

## Repair of the returned long step

I compared the retained sandbox with the current shared node and its Q48 delivery
report. The current main node incorporates the Q48 repair of the returned old
2279-character step: the genuinely non-elementary Cartesian-to-cocartesian lifting
criterion is the split node `lem-coef-cartesian-left-adjoint-transport`, explicitly
cited in step 3. This delivery supplies that child's Lean statement. Step 4 separately
gives the three mapping-space equivalences for preservation of colimits, citing the
existing coherent-diagram adjunction and dual cocone criterion.

The current seven proof texts have lengths 639, 1206, 654, 1065, 1114, 1469, and
1009 characters. No non-elementary step exceeds 2000 characters. I preserve all seven
steps, their uses, the proof-dependency list, the statement, and the current metadata
verbatim. I do not reintroduce the stale long step or duplicate the already landed
general criterion. This delivery adds the missing stage-2 record and module for the
split child, as well as the main node's retained stage-2 record. The main statement is
unchanged.

The only theorem left for stage 3 in the main item is the main theorem; the split child
is likewise statement-only. Every definition has real data. No STATEMENT-DISPUTED
finding or node statement fault remains.

## Second reading by Q28

I reread the main node, the split child node, both Lean signatures, and every recorded
statement dependency named by the split child. The main signature binds independent `u`
and `v`, keeps both coefficient cocompleteness hypotheses and both separate tensor
cocontinuity hypotheses, and concludes quasicategorical total categories, their small
colimits, and preservation by literal postcomposition. The child signature binds a
Cartesian fibration `p`, its restriction map `R` for every base edge, the coherent
Cartesian transformation `τ` identifying `R` with transport, and a coherent left
adjoint witness for each restriction. It concludes cocartesian-fibration lifts for
every source vertex, with the target of each specified left adjoint and the given
adjunction unit as recorded by the triangle `z`. The source clauses are unchanged and the child is strictly the
transport criterion used by step 3, so it does not restate the main colimit theorem.
I checked the point base, a single interval edge, and an empty fiber in the child
statement, and the empty indexing diagram, identity coefficient map, and empty object
space in the main statement. The child module compiled independently; the main module
and the combined delivery compile through `scompile.py`.

## Review by Q28

The returned point is repaired by delivering the previously extracted split node's Lean
statement and by retaining the seven short main proof steps. The current main step 3
cites the child for the non-elementary Cartesian-to-cocartesian argument; steps 1, 2,
4, 5, 6, and 7 retain their recorded node citations. The main statement and its
`stmt_deps` are unchanged. No citer requires editing.

## Validation

All compilation goes through `scompile.py`; no local/global Lake build is run.
The saved packet passed the initial `deliver2.py --no-push` at dry-run commit
`4ee553cec2`. The required self-check then found and repaired the child interface
defects described below. Both final modules are recompiled using `scompile.py` and
the revised packet is checked by `deliver2.py --no-push` before the final push. The maintainer supplies the independent reading; this report
does not claim a second worker reviewed the delivery.

## Final self-check of the retained packet

The first dry run passed, and the existing seven-step proof split was retained.
Comparison with the shared main node confirms that only its `lean` field differs;
its statement, seven proof steps, proof dependencies, and all other fields are identical.
The main Lean signature/record is preserved. The split child also changes only in
`lean`. Its natural-language statement is retained verbatim. All seven main proof
steps remain below 2000 characters; step 3 cites the extracted transport criterion.

Reading the child's full signature against its statement found two semantic faults
missed by compilation: an arbitrary `R` was not connected to the Cartesian fibration,
and the required specified-unit clause had been omitted. The revised child binds:

- `p`, `hp`: the Cartesian fibration of quasicategories, in arbitrary containing `u`.
- `R α`: restriction from the target fiber to the source fiber.
- `τ α`: a coherent transformation from `R α` followed by the source inclusion to
  the target inclusion. `hτsrc`, `hτtgt` fix its endpoints; `hτbase` fixes the entire
  transformation over the constant base edge; `hτcart` says every component is
  Cartesian. These clauses express the node's word "restriction", with all coherent
  simplices retained, and exclude arbitrary maps between the fibers.
- `hR`: each such restriction has a coherent left adjoint. No presentability or
  completeness hypothesis is introduced.
- `cocartesianFibration p`: the first conclusion.
- The universal quantifiers over `α`, `L`, `adj`, and `x` express "any specified
  adjunction" and "any x". The edge `e` has source `x`, target `L x`, lies over `α`,
  and is cocartesian. Thus it represents the covariant transport by `L`.
- `z`: a 2-simplex whose initial edge is the given unit at `x` included into `E`,
  final edge is the specified Cartesian edge at `L x`, and long edge is `e`.
  Its image is the degenerate base triangle `(b,b,c)`. Under the Cartesian
  mapping-space equivalence, composition with that Cartesian edge is the equivalence's
  inverse. Hence `z` is exactly the homotopy identifying `e` with the specified unit;
  it retains this identification before passing to homotopy classes.

The proof docstring explains the unit construction and the local-to-global passage
of Kerodon 02FP, dualizing 02FN. Both source pages were reopened on this repair run.
No new definition or unnamed postponed theorem is used. The main module now also
imports this child's module as its stated proof dependency (non-publicly).

Additional edge checks: an empty base makes the edge clauses vacuous, while `hp`
still supplies the inner-fibration condition. An empty target fiber admits the unique
restriction from it, but `hR` cannot hold with a nonempty source fiber: there is no
left-adjoint map from that source into the empty fiber. Thus the false arbitrary-map
case is excluded by the actual adjunction condition. For a point base, the Cartesian
transformation identifies restriction with the identity up to equivalence. For an
interval base, the triangle is precisely the unit-composite lift in dual Kerodon 02FN.
The source and target of every component follow from the coherent endpoint equations.

The transport signature was compared with the existing
`Sheaf.CategoryTheory.InfinityTransportUniqueness.coherent_cartesian_transport_unique`
(the declaration's namespace is `SSet.Enhanced`). That theorem proves uniqueness of
restrictions via coherent Cartesian transformations; it neither constructs adjoints nor
states the present cocartesian criterion. Its endpoint/base/Cartesian interface confirms
the meaning of the repaired binders. The existing retained three-kind searches remain
applicable: no notion is redefined and the repaired child still has no exact Mathlib or
upstream match. The maintainer provides the independent review; this final self-check
is by Q28 and makes no claim to be an independent worker's reading.
