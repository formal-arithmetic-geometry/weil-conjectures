## Worker report

`lean/Sheaf/AlgebraicTopology/AnodyneCocones.lean` states
`SSet.Enhanced.anodyne_cocones`. It has one theorem and one `sorry`.
The other seven declarations construct the join and canonical restriction maps
specified inline by the item. All definition data are actual constructions.
No other DAG theorem is stated, and no dependency module is changed.

The current node, its complete six-step proof, and the full source and docstrings
of `Sheaf.CategoryTheory.EnhancedDiagramsCones` were read. Source checks:
[Kerodon 018J](https://kerodon.net/tag/018J) is the right-anodyne/monomorphism
pushout-join assertion; [02N3](https://kerodon.net/tag/02N3) identifies right
anodyne maps with right cofinal monomorphisms; the opposite-category dual of
[02NR, condition (6)](https://kerodon.net/tag/02NR) gives the coherent-cocone
restriction assertion. The orientation is outgoing cocones, with the target
constant, rather than incoming cones. The mapping spaces follow the dependency's
right-pinched convention, as required by the item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- All small simplicial sets are `SSet.{u}`; `universe u` is explicit and
  `autoImplicit` is false. Functor simplicial sets are Mathlib's `(ihom K).obj C`.
  These are the dependency's fixed size and internal-functor conventions.
- The input monomorphism is `(i : A ⟶ B) [Mono i]`. Right anodyne is
  `(hi : SSet.rightAnodyneExtensions i)`, now imported from the already landed
  `Sheaf.CategoryTheory.RightAnodyne`. Its declaration and full docstring were
  read: it is the infimum of morphism properties containing isomorphisms and
  horns with `0 < i`, closed under pushouts, small transfinite compositions,
  and retracts. In degree zero there is no positive horn index, so this is
  exactly the stated positive-dimensional list, including the final horn.
- The join's ordered-concatenation convention is implemented by
  `terminalAugmentation` and `joinBifunctor`. The first gives each simplicial set
  its unique augmentation to `PUnit`. The second takes the external product,
  left Kan extends along `tensor AugmentedSimplexCategoryᵒᵖ`, and restricts to
  ordinary simplices. Mathlib's augmented tensor is ordinal concatenation.
  The Kan-extension colimit splits by the ordered cut of the target ordinal.
  An empty initial block gives `Y_r`, an empty final block gives `X_r`, and
  two nonempty blocks give `X_u × Y_v` with `u+v+1=r`; restricting the ordinal
  restricts these blocks. Thus this is precisely the specified ordinary join,
  including its two pure summands, and the notation `X▹` means `join X Δ[0]`.
  `joinMap` is the action of this one bifunctor on maps.
- `pushoutJoin i k` is the actual `pushout.desc` with domain
  `pushout (joinMap (𝟙 A) k) (joinMap i (𝟙 K))` and codomain `join B L`.
  Its legs are `joinMap i (𝟙 L)` and `joinMap (𝟙 B) k`; the required equality
  follows from the bifunctor's composition law. No arbitrary map is supplied.
- The first theorem conjunct quantifies over every `{K L : SSet.{u}}`,
  `(k : K ⟶ L) [Mono k]`, and states
  `innerAnodyneExtensions (pushoutJoin i k)`. Mathlib defines inner anodyne by
  the left lifting property against inner fibrations; its small-object theorem
  identifies this with the specified inner-horn weak saturation.
- The second conjunct quantifies over `(C : SSet.{u}) (_ : Quasicategory C)`,
  every `(p : B ⟶ C)`, and every vertex `(T : C _⦋0⦌)`. No colimit existence,
  nonemptiness, finiteness, or additional structure is assumed.
- The source mapping space is literally
  `mappingSpace ((ihom B).obj C) (diagramVertex p)
  ((constantDiagrams B C).app _ T)`; the target replaces `B` by `A` and `p`
  by `i ≫ p`. The theorem asserts `KanComplex` for each and
  `IsWeakHomotopyEquivalence (coconeMappingRestriction i p T)`.
  This last predicate is the dependency's bijection on path components and
  all positive based homotopy groups after realization, with no extra
  nonemptiness condition.
- `diagramRestriction i C` precomposes each whole coherent simplex with `i`
  through `Functor.HomObj.ofNatTrans` and `HomObj.comp`.
  `coconeMappingRestriction` is precisely the dependency's `mappingSpaceMap`
  for this map, at the literal diagram and constant endpoints. Endpoints
  reduce definitionally; there are no chosen equivalence inverses or casts.
- Naturality in the target is the equality of entire simplicial maps
  `constantDiagrams B C ≫ diagramRestriction i C = constantDiagrams A C`.
  This includes edges and every higher simplex of `C`. Because the actual
  restriction is a simplicial map of functor categories, it restricts every
  composition triangle and all higher compatibility witnesses as well.
  This is the node's coherent postcomposition clause; no strict composition
  operation on right-pinched mapping spaces is assumed.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.diagramVertex`, `constantDiagrams`, `mappingSpace`,
  `mappingSpaceMap`, and `IsWeakHomotopyEquivalence`, with Mathlib's `SSet`,
  `Quasicategory`, `KanComplex`, and `ihom`.
- `Sheaf.CategoryTheory.RightAnodyne`: `SSet.rightAnodyneExtensions`.
  This definition is already in the current item's `stmt_deps`.
- Mathlib's augmented-simplex monoidal structure, terminal augmentation,
  external product, Kan-extension functor, type colimits, and
  `SSet.innerAnodyneExtensions` provide the join data and inner-anodyne notion.
  The declarations and full construction signatures were inspected.

The stated proof-only Mathlib declarations were also read:
`SSet.relativeCellComplexOfMono` in
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`, and
`SSet.modelCategoryQuillen.I`, `SSet.rlp_monomorphisms` in
`Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`.
Their modules are imported non-publicly. The remaining proof dependencies
have no recorded Lean module in the current node records, so there is no
module to import for them. The theorem docstring records every one of the
item's six proof steps and its cited proof tools.

Edge cases checked: identity `i` and `k`; empty `A=B`; empty `K` and `L`;
`K=L`; the empty boundary in degree zero; the right horn with `n=1`, `i=1`;
ordinary-category nerves; and empty Kan mapping spaces. The last-vertex
inclusion into `Δ[1]`, joined against `∅ → Δ[0]`, gives the inner horn
missing vertex 1 in `Δ[2]`, confirming orientation. The join in degree zero
has just the two pure vertex summands. The augmentation degree `-1` is
essential to preserve those summands when either factor is empty. No chosen
inhabitant of a Kan space appears anywhere.

Searches re-run in this repair:

- `msearch.py ... leanfinder`, query "Right anodyne inclusions induce
  equivalences of coherent cocone mapping spaces and inner anodyne pushout
  joins": eight hits, including `SSet.modelCategoryQuillen.J`,
  `CategoryTheory.CosimplicialObject.cechConerveEquiv`, small-object cocones,
  and horn-colimit declarations; no exact theorem.
- `msearch.py ... loogle`, query `"anodyne", "Cocone"`: zero hits.
- `msearch.py ... grep`, query
  `right.?anodyne|pushout.?join|cofinal.*cocone`, subdirectory
  `AlgebraicTopology`: zero hits.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, and `lean/Sheaf` for
  `rightAnodyneExtensions`, `pushoutJoin`, `joinBifunctor`,
  `coconeMappingRestriction`, and `anodyne_cocones`: found the landed
  `SSet.rightAnodyneExtensions`, which is now reused; no join or item theorem.
  Further concept searches for simplicial join, Day convolution, and ordinal
  concatenation found no project join construction. The upstream item-id
  search and proposed-name search of `dag/lean_names_upstream.json` had no hits.

## Repair of the earlier attempt

The inherited module already marks the expensive left-Kan-extension construction
`joinBifunctor` with `@[no_expose]`. The initial wrapper check of that exact file
succeeded in 4.7 seconds (sandbox) and 7.3 seconds (library module name).
This repair also marks `terminalAugmentation` with `@[no_expose]`, so automatic
exposure does not export its augmented-object equivalence and functor-law proof
terms. Its definition remains the same real terminal augmentation, and the join,
join-map, and pushout-join interfaces keep the same types and constructions.
All consumers of that definition are in this module and are checked together.
No external user exists in the searched source trees. No new theorem, statement
correction, dependency repair, or additional DAG node is needed.

The node copy has been refreshed from the current repository; only its `lean`
record changes. This removes stale field comparisons from the earlier attempt.
The report's inherited second-reading section has been removed: a fresh second
reader must inspect the final repaired version before delivery.

The repaired module compiles cleanly through `scompile.py` in both sandbox
and actual-library-module positions (2.0 and 2.2 seconds), with no warnings.
The standard 60-second limit is unchanged. The required `deliver2.py --no-push`
dry run is the final check; nothing will be pushed by this worker.


## Second reading by Q01

I independently read the full node, its six proof steps, the final Lean file,
all statement-dependency records, and the declaration bodies used below. The
original worker report above describes the inherited version; this section
records the delivered version and supersedes its claims about local helpers.
The final file contains just `SSet.Enhanced.anodyne_cocones`, with one `sorry`.

Source check: these are Kerodon tags, not Stacks tags. I read
[018J](https://kerodon.net/tag/018J), [02N3](https://kerodon.net/tag/02N3),
[02NR](https://kerodon.net/tag/02NR), [01KX](https://kerodon.net/tag/01KX),
[01L0](https://kerodon.net/tag/01L0), and
[01L5](https://kerodon.net/tag/01L5). The first source assumes two simplicial
monomorphisms and requires only right anodyneness of the first. The cofinality
sources, after taking opposites, give outgoing cocones into an arbitrary target
vertex, with no colimit hypothesis. The pinch sources justify precisely the
right-pinched convention of the dependency. No additional standing hypothesis
is required. There is no repair-note JSON for this item and no statement_change.

Clause-by-clause checklist (the node's objects and hypotheses first):

1. Small simplicial sets and the enhanced conventions: `A B K L C : SSet.{u}`,
   `(ihom B).obj C`, `diagramVertex`, `constantDiagrams`, and `mappingSpace`.
   PASS. I read their definitions in
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`, not merely their names.
   In particular, `mappingSpace` fixes the whole initial face at the source
   and the final vertex at the target, in every degree. The functor-category
   internal hom is Mathlib's exponential with coherent higher simplices.
2. Right-anodyne monomorphism: `(i : A ⟶ B) [Mono i]` and
   `(hi : SSet.rightAnodyneExtensions i)`. PASS. I read the landed definition
   in `Sheaf.CategoryTheory.RightAnodyne` against
   `def-coef-infinity-right-anodyne`: its infimum imposes isomorphisms,
   positive-index horns, pushouts, small transfinite compositions and retracts.
   The degree-zero horn has no positive index, so the generators are exactly
   n >= 1 and 0 < i <= n.
3. The ordered join and canonical pushout comparison: the first conjunct uses
   the landed `SSet.Enhanced.pushoutJoin` from
   `Sheaf.AlgebraicTopology.PushoutJoinSaturation`. PASS. I opened that node
   and its entire module. `joinAugmentation` is right Kan extension, assigning
   a singleton at the empty ordinal; `orderedJoinFunctor` convolves along
   ordinal concatenation. A simplex has a unique cut into initial and final
   blocks, allowing either empty block, giving the node's two pure summands
   and mixed summands. Operators restrict those blocks. The actual
   `pushout.desc` has the node's four join objects and its canonical legs;
   the compatibility proof is bifunctor naturality. This is not a Cartesian
   pushout product, an unspecified map, or a join with reversed factors.
4. Every monomorphism k, with no further restriction:
   `∀ {K L : SSet.{u}} (k : K ⟶ L) [Mono k]`. Its conclusion is
   `innerAnodyneExtensions (pushoutJoin i k)`. PASS. I read Mathlib's
   `innerAnodyneExtensions` and its small-object characterization
   `innerAnodyneExtensions_eq_retracts_transfiniteCompositions`, confirming
   the inner-horn weak saturation, not all-horn anodyneness.
5. Any quasicategory, diagram, and target vertex:
   `∀ (C : SSet.{u}) (_ : Quasicategory C)` followed by
   `∀ (p : B ⟶ C) (T : C _⦋0⦌)`. PASS. No colimits, finite shape,
   inhabitedness, model structure, or chosen inverses are assumed.
6. Both displayed mapping spaces are Kan: the two `KanComplex` conjuncts
   have exactly `(diagramVertex p, constantDiagrams B C ... T)` and
   `(diagramVertex (i ≫ p), constantDiagrams A C ... T)` as endpoints. PASS.
7. The equivalence is induced by actual restriction:
   `IsWeakHomotopyEquivalence (mappingSpaceMap ((MonoidalClosed.pre i).app C)
   (diagramVertex p) ((constantDiagrams B C).app _ T))`. PASS. I read
   Mathlib's `MonoidalClosed.pre`, its adjunction characterization and
   `uncurry_pre_app`: this is precomposition by i, so its vertex images are
   p composed with i and the same constant diagram on A. These endpoint
   images need not reduce definitionally to the literal endpoints in (6);
   they are exactly those diagrams by the canonical precomposition formula.
   There is no arbitrary map or chosen comparison. I also read
   `mappingSpaceMap` and `IsWeakHomotopyEquivalence`: it is postcomposition
   on the full right-pinched simplices and asserts a bijection on realization
   path components and all positive based homotopy groups, as the node asks.
8. Naturality in T and coherent postcomposition:
   `constantDiagrams B C ≫ (MonoidalClosed.pre i).app C = constantDiagrams A C`.
   PASS. This is an equality of entire simplicial maps, hence includes each
   edge T to T' and every higher simplex. The same canonical simplicial
   precomposition carries composition triangles and their higher witnesses
   to their restrictions. Together these give exactly the coherent clause,
   without imposing a nonexistent strict mapping-space composition operation.
   Moving the universal constant-diagram equality before p and T is logically
   equivalent to stating its naturality for all those p and T.

Edge cases: empty A = B and arbitrary empty K or L are admitted; the join's
singleton augmentation retains the pure terms and makes the empty simplicial
set its unit. The k = identity case is included. With n = 1, i = 1 and
k the empty boundary into the point, ordinal concatenation gives the inner
horn with missing vertex 1 in dimension 2, confirming the handedness. Boundary
degree zero is included. Empty mapping spaces are Kan and their component
bijection is tested, without inserting a point. If C is empty, the T-binder
correctly has no instances; the join conclusion remains. Ordinary-category
nerves provide the usual outgoing cocone restriction. There are no rings,
characteristic restrictions, scheme hypotheses, or zero-object assumptions.
The explicit arbitrary universe u is the dependency's fixed small universe;
there is no new equality between independent universe parameters.

Independent H4 searches, recorded also in searches.jsonl:

- LeanFinder: "Leibniz join of right horn inclusion with monomorphism is inner
  anodyne" returned eight horn/Quillen-generator hits, no join theorem.
- LeanFinder: "Restriction along a final inclusion preserves the space of
  natural transformations from a diagram to a constant functor" returned
  ordinary-category final/structured-arrow lemmas, not arbitrary simplicial
  shapes or coherent Kan mapping spaces.
- Loogle: `"innerAnodyneExtensions"` returned the property and its closure
  instances, not this two-clause theorem.
- msearch grep: `Leibniz|pushout.?join|right.?cofinal|right.?anodyne` in
  AlgebraicTopology returned no Mathlib hit. Direct rg of Mathlib,
  upstream WeilConjectures, and this project's lean/Sheaf found the landed
  ordered join and pushoutJoin described above, plus a separate right-cone
  theorem, but no exact cocone-equivalence theorem. The upstream-name index
  had no hit for the item theorem or its former restriction helpers.

Mismatches repaired:

- H4: the inherited terminal augmentation, join bifunctor, join, join-map,
  and pushoutJoin duplicated the now-landed saturation module (including
  an exact full-name collision on pushoutJoin). Removed all five; imported
  the landed module publicly and added its existing node to stmt_deps.
- H4: the inherited explicit diagramRestriction is the same precomposition
  notion Mathlib already provides. Replaced it with MonoidalClosed.pre,
  and used mappingSpaceMap directly instead of retaining a redundant
  coconeMappingRestriction wrapper. No helper declaration remains.
- Dependency bookkeeping: the inherited file imported RightAnodyne but the
  copied node's stmt_deps still omitted its owning definition node. Added
  def-coef-infinity-right-anodyne, as the worker had intended.
- Missing proof import: the pinch-comparison dependency now has a landed
  declaration. Read its complete signature and proof docstring, then added
  its module as a non-public import. The saturation theorem is already
  available through the public import needed for pushoutJoin. The remaining
  unstated proof nodes have no modules; the recorded Mathlib proof leaves
  use the Skeleton and CategoryWithFibrations imports retained here.

No new node, dependency repair, mathematical statement correction, or unit
change is needed. I checked the existing dependency modules against their
own nodes; this delivery changes neither. The theorem's docstring still
contains all six node-proof steps and their tools. Every theorem proof is
sorry; no definition data or new assumption is hidden. The node's
lean.statement is verbatim equal to the final signature, all binders are
explicit, and all Lean lines fit 100 characters. Final scompile.py checks
passed without warnings: sandbox 2.2 seconds, library module 2.6 seconds,
with the default per-file 60-second limit.
