## Worker report

The module `lean/Sheaf/AlgebraicTopology/ConeEquivalenceSaturation.lean` defines the
relative right cone
`SSet.ConeEquivalence.relativeCone`, its canonical map on an arrow of `Over S`,
and the morphism property `SSet.ConeEquivalence.coneEquivalences`.  The cone is the
pushout `pushout a (Enhanced.rightJoinConeInclusion X)`, using the existing ordered
join `Enhanced.rightJoinCone` (whose degreewise ordered-concatenation construction is
in the dependency module).  The coherent realization of the induced map is passed to
`CategoryTheory.DwyerKanEquivalence`, which is exactly the conjunction of mapping
simplicial-set weak homotopy equivalences and equivalence on the `pi_0` categories.
`HasSmallFilteredGenerators` spells out a small set of arrows, contained in the
morphism property, and a filtered diagram in `Arrow (Over S)` with an isomorphism to
its colimit.  The theorem `cone_equivalence_saturation` states all requested clauses:
all isomorphisms, two-out-of-three, filtered-colimit closure, small filtered
 generation, and pushout closure along a monomorphism.

The theorem's hypotheses and clauses render in Lean as follows.

* `S : SSet.{u}` fixes an arbitrary input universe; there is no quasicategory or
  nonemptiness hypothesis on `S`.
* `MorphismProperty.isomorphisms (Over S) ≤ coneEquivalences S` is the assertion that
  every isomorphism over `S` belongs to `W_S`.
* `(coneEquivalences S).HasTwoOutOfThreeProperty` is the categorical two-out-of-three
  property for composable arrows in `Over S`.
* `(coneEquivalences S).IsStableUnderFilteredColimits` uses Mathlib's filtered
  colimit-of-arrows formulation, with `IsFiltered` (including cocones for the empty
  finite diagram).
* `HasSmallFilteredGenerators S` gives `W₀ ⊆ W_S` and, for every `W_S` arrow, a
  filtered `J : Type u`, a diagram `D : J ⥤ Arrow (Over S)`, every `D.obj j ∈ W₀`,
  and `Nonempty (f ≅ colimit D)`.  Colimits are those of the arrow category and hence
  are computed on both endpoints.
* The final universal quantifier binds `X Y X' Y' : Over S`, the arrows `f`, `i`,
  `j`, and `f'`; `IsPushout i f f' j` is the displayed pushout square, `Mono i.left`
  is degreewise injectivity of the attaching map, and the implication preserves
  membership of `f'` in `W_S` from membership of `f`.

The dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`, especially
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and the simplicial-set conventions.
* `Sheaf.AlgebraicTopology.PinchedCubeLatching`, especially
  `SSet.PinchedCube.rigidification` and the coherent realization map.
* The canonical ordered-cone map and its naturality are reused from
  `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison`:
  `SSet.Straightening.coneMap` and
  `SSet.Straightening.coneInclusion_naturality`.  This is an existing canonical
  construction, not a private replacement.
* `Sheaf.CategoryTheory.CoherentNerveComparison`, for
  `CategoryTheory.DwyerKanEquivalence`.
* Mathlib's `CategoryTheory.Over`, `Arrow`, `MorphismProperty` classes,
  `IsPushout`, `Mono`, `IsFiltered`, and `colimit`.

Edge cases checked before writing:

* `X` and `S` may be empty simplicial sets; the pushout and ordered join remain
  defined degreewise.
* The cone vertex is retained in every degree, including degree zero; no `n > 0`
  or nonempty-index assumption is introduced.
* Filteredness is the standard Mathlib predicate, so the empty finite diagram clause
  is included.  The selected generator set is explicitly a subset of `W_S`.
* The pushout clause uses `Mono i.left`, so it covers exactly degreewise injective
  maps and does not impose a stronger cofibration or quasicategory hypothesis.
* All constructions and the theorem are universe-polymorphic in `u`; no universe
  equality is assumed.

Searches made:

* `msearch.py ... leanfinder "relative simplicial cone categorical equivalence
  Dwyer Kan filtered colimit pushout monomorphism"`: no matching project notion;
  returned only unrelated Cech-conerve and arrow-colimit declarations.
* `msearch.py ... loogle "DwyerKanEquivalence, IsStableUnderFilteredColimits,
  HasTwoOutOfThreeProperty"`: the tool reported the identifier query as unknown;
  the declarations were checked directly in the imported project/Mathlib sources.
* `msearch.py ... grep "rightJoinCone|DwyerKanEquivalence|IsStableUnderFilteredColimits|IsPushout"
  AlgebraicTopology`: found the existing ordered-join, Dwyer--Kan, filtered-colimit,
  and pushout APIs, but no saturation theorem for this relative-cone class.
* `rg` over `WeilConjectures/` and `lean/Sheaf/`: found the canonical cone and
  coherent-realization declarations listed above, and no declaration of this node's
  `W_S` saturation statement.

No `STATEMENT-DISPUTED` issue or node fault was found.  The required theorem proof is
left as the single named `sorry` in the statement module.

## Second reading by N5

I independently read the node, both statement dependencies and their Lean records,
the existing cone and categorical-equivalence declarations, and the cited HTT text.
This is a repair of the Lean rendering; the informal node statement is unchanged.
No repair note for this item is present in `coord/repair-notes`.

Source check: this is an HTT result, not a Stacks result (the node explicitly says
that no Stacks tag states it). I fetched the author's IAS HTT PDF into the sandbox
scratchpad and read Definition the project server, Proposition the project server and its proof (printed
pp. 68--70), Remark the project server (p. 71), Definition A.2.6.12 and Corollary A.2.6.14
(p. 825). The section's standing assumptions are familiarity with model categories,
not fibrancy or a quasicategory assumption on S. Definition the project server and Remark
the project server (p. 25) give the coherent-realization interpretation of categorical
 equivalence. Proposition the project server(1)--(2), dualized by simplicial opposite, gives
exactly the perfectness and monomorphism cobase-stability clauses used here. The
node explicitly expands filtered closure to arbitrary small filtered categories;
its mappingwise proof covers these, as opposed to only posets.

The node's objects, hypotheses, and conclusions, matched individually:

1. Small simplicial sets and weak homotopy equivalences: `SSet.{u}` and
   `Enhanced.IsWeakHomotopyEquivalence` from `EnhancedDiagramsCones`. I opened
   its definition: geometric realization induces a bijection of path components
   and of every positive based homotopy group. Verdict: exact.
2. Coherent realization: `PinchedCube.rigidification` from
   `PinchedCubeLatching`. I opened `coherentSimplex`, its monotone direct-image
   maps, and `rigidification`: this is the colimit/left-Kan extension of the
   endpoint-containing subset-poset simplices, with union composition, not a
   freely chosen equivalent functor. Verdict: exact.
3. Component category and categorical equivalence: the existing
   `Enhanced.IsCategoricalEquivalence` unfolds to
   `Bergner.dwyerKanEquivalences (PinchedCube.rigidification.map f)`, then
   `CategoryTheory.DwyerKanEquivalence`. I read `PiZeroEquivalence` and
   `PiZeroEssentiallySurjective`: all mapping-set component maps are bijective
   and every target object has a two-sided inverse witness modulo components.
   Together with mappingwise weak homotopy equivalence, this is precisely an
   equivalence of the component categories. Mathlib `SSet.π₀` is the vertex
   quotient generated by edges; these classes equal the path components of
   realization, including empty mapping sets. Verdict: exact; no local Kan
   assumption is present.
4. Arbitrary small base S: the theorem binds `(S : SSet.{u})` and nothing else.
   Verdict: exact, no quasicategory or nonemptiness hypothesis.
5. Object a:X→S and relative right cone: the existing
   `Enhanced.coneExtension a` is literally
   `pushout a (Enhanced.rightJoinConeInclusion X)`. I read its signature and
   body in `ContravariantSliceModel`, `rightJoinCone` in `RelativeInfinityCone`,
   and `orderedJoinFunctor` in `PushoutJoinSaturation`: terminal augmentation,
   ordinal concatenation, and the left Kan extension yield the pure X block,
   apex, and mixed X_q blocks with q<r. Restriction/repetition acts on the
   surviving initial block; an empty initial block is the apex. Verdict: exact.
6. Canonical map on arrows over S: `Enhanced.coneExtensionMap f.left X.hom
   Y.hom (Over.w f)` uses identity on S, `orderedJoinFunctor.map (f.left, 𝟙 Δ[0])`
   on the cone, and `f.left` on the gluing domain. Its compatibility proof is
   ordinary naturality of the constructed join; it contains no sorry. Verdict:
   exact canonical map, not an arbitrary witness.
7. Class W_S: `coneEquivalences S` applies the existing categorical-equivalence
   predicate to exactly that cone map. Verdict: exact.
8. Isomorphisms: `MorphismProperty.isomorphisms (Over S) ≤ coneEquivalences S`.
   Verdict: every slice isomorphism is included.
9. Two-out-of-three: `(coneEquivalences S).HasTwoOutOfThreeProperty`.
   Verdict: all three implications for each composable pair, no extra hypothesis.
10. Small filtered-colimit closure in the arrow category:
    `IsStableUnderFilteredColimits.{u, u} (coneEquivalences S)`. I opened the
    Mathlib class and its underlying `IsStableUnderColimitsOfShape`: it tests
    a natural transformation with pointwise W_S maps and the induced arrow
    between its two colimit cocones. This is the arrow-category colimit,
    computed at the two endpoints. Verdict: exact; index object and morphism
    universes are explicitly u.
11. Small generating set contained in W_S: `HasSmallFilteredGenerators S`
    now begins `∃ W₀ : Set (Arrow (Over S)), Small.{u} W₀ ∧ ...` and requires
    `g ∈ W₀ → coneEquivalences S g.hom`. Verdict: exact after the repair.
12. Generation of every member: the next universal quantifier runs over every
    arrow f in W_S and produces `J : Type u`, `SmallCategory J`, `IsFiltered J`,
    `D : J ⥤ Arrow (Over S)`, all stages in W₀, and
    `Nonempty (f ≅ colimit D)`. Verdict: the set is chosen once before f; every
    member is generated up to isomorphism, as stated in the node.
13. Filtered means every finite diagram, including the empty one, admits a
    cocone: Mathlib `IsFiltered` includes `Nonempty J`, in addition to the
    common-successor and parallel-arrow conditions. Verdict: exact; an empty
    indexing category is excluded for precisely the reason the node excludes it.
14. Pushout square: the binders X,Y,X',Y' are all `Over S`, and
    `IsPushout i f f' j` asserts i≫f'=f≫j with the displayed pushout property.
    Verdict: the orientation agrees with X→Y, X→X', X'→Y', Y→Y'.
15. Degreewise injection and conclusion: `Mono i.left → coneEquivalences S f →
    coneEquivalences S f'`. In SSet a categorical mono is degreewise injective.
    Verdict: no condition on f being monic, no stronger cofibration hypothesis,
    and exactly the desired resulting arrow f'.
16. Each input universe: only u is declared and SSet, W₀ smallness, filtered
    closure, and generator indexing all use it. Verdict: no universe equality
    or extra size restriction on the input simplicial sets.

Edge cases: when X is empty, the cone is S disjoint union Δ⁰; when S is empty,
objects of the slice have empty source and their relative cone is Δ⁰. No
nonempty-simplicial-set hypothesis rules either case out. In degree zero there
are no mixed blocks, leaving exactly S₀ plus the apex. The empty generating
subset cannot generate an identity arrow via a nonempty filtered diagram;
that is correct. There is no ring, characteristic, scheme, or numerical n
hypothesis in this node. Arbitrary zero-dimensional inputs are included.

Independent searches:

- LeanFinder via msearch: `relative simplicial cone categorical equivalence
  filtered colimit pushout`. Eight Cech-conerve/horn-colimit hits; no match to
  this perfectness statement.
- Loogle via msearch: `"IsStableUnderFilteredColimits", "IsSmall"`. No hits.
- LeanSearch via msearch: `Coherent realization of a relative simplicial right
  cone detects a perfect class of arrows closed under pushout along
  monomorphisms`. Eight generic pushout and monomorphism hits; none states this
  theorem. Generic mono pushout stability concerns the mono class itself.
- msearch grep: `relativeCone|coneEquivalences|rightJoinCone|DwyerKanEquivalence`.
  No Mathlib match. Independent rg in Mathlib, slopmaster2/WeilConjectures, and
  the project's lean/Sheaf with `relative.*cone`, `cone.*pushout`,
  `cone.*equivalence`, `perfect.*class`, and `dwyerKanEquivalences` found the
  existing cone constructions and DK predicate. I opened their bodies; they
  are reused below. `contravariant_slice_model` itself states a model structure
  and fiberwise recognition, not the small filtered-generation assertion here,
  so it is not an existing declaration of this item. There is no exact existing
  saturation theorem to bind this node to.

Mismatches repaired:

- H3: the original `Set (Arrow (Over S))` alone is a predicate on the large
  arrow type and does not say the subset is small in u. Without `Small.{u} W₀`,
  taking W₀ to be the whole W_S class and singleton filtered diagrams makes
  the generation assertion automatic. Added `Small.{u} W₀` to the definition.
- H4: `relativeCone` and `relativeConeMap` duplicated the already recorded
  `Enhanced.coneExtension` and `Enhanced.coneExtensionMap` in the parent
  `ContravariantSliceModel` module. Removed those private copies, reused the
  existing canonical constructions and the exact DK categorical-equivalence
  predicate, and removed the newly unnecessary RightStraightening and
  CoherentNerveComparison direct imports. I also checked current source using
  `scompile.py --source` for ContravariantSliceModel and SimplicialIntervalLifting.
- H8: the helper docstrings lacked source/blueprint annotations, and the theorem
  only mentioned two source results instead of carrying the proof. Both
  remaining helper docstrings now have source/blueprint annotations; the theorem
  docstring carries all eight node proof steps, including their dependencies.
- H9: made the filtered-index universes explicit as `{u,u}` and removed unused
  universe declarations v,w. Added all available stated proof-dependency modules
  as non-public imports, including the recorded Mathlib leaves.

Import note: the existing relative-cone definitions live in
`Sheaf.CategoryTheory.ContravariantSliceModel`, so this module imports it to
honor one definition per notion. Its theorem is not used as a proof input.
The future proof-dependency backlink from ContravariantSliceModel to this
module must be omitted under stages/2-statements.md §3(7), which explicitly
allows omission of a backlink closing an import cycle. This is recorded in
lean.note. The fixed-vertex-cofibration node currently has no Lean statement;
it is a proof-only dependency and is retained in the eight-step proof docstring,
with no import until stated. It is not needed to type this statement. No new
node or dependency module is included in the final delivery.

Validation: the one delivered module compiles cleanly through scompile.py,
without errors or warnings. All definitions have real data, and the only
postponed proof in the module is the named theorem of this node. The node's
lean.declarations lists exactly the three delivered declarations and
lean.statement is extracted verbatim from the file signature. No informal
statement correction or citer audit is needed.
