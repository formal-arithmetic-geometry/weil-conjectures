## Worker report

This delivery states `lem-coef-right-decalage-index-calculus` in
`Sheaf.CategoryTheory.RightDecalageIndexCalculus`, with main declaration
`SimplexCategory.RightDecalage.indexAdjunction`. Its sole theorem has proof `sorry`.
All data definitions, category structure, morphisms and functors are constructed in full;
the small proofs inside those constructions establish their structural laws. There are
no additional postponed theorems, new DAG nodes, dependency repairs or statement changes.

The previous worker's conclusion was mistaken: the Q52 PASS and ledger entry record
stage 1, the five-step natural-language proof split. The base node has no `lean` record.
This delivery preserves that split and supplies its stage-2 statement; it does not
resplit or replace the reviewed proof.

Source read: Lurie, Higher Topos Theory, Lemmas the project server--17, printed pp. 553--554
(PDF pages 570--571, zero based),
<https://people.math.harvard.edu/~lurie/papers/HTT.pdf>. Lemma the project server defines the
last-point-preserving ordinal category; the project server specifies adjoining the last element.
The indexing adjunction is the elementary calculation in the DAG, not a quoted theorem
of HTT. Also read the current `main-20261015` blueprint ancestor
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`:
the finite-coefficient mapping-complex adjunction in its second paragraph is the
ancestor place recorded by this node. Its statement and route are unchanged.

Clause-by-clause comparison with the unchanged natural statement:

1. Small ordinary nerves and the enhanced conventions: import the recorded dependency
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its module uses Mathlib's ordinary
   `CategoryTheory.nerve` and quasicategory primitives. The present conclusion is entirely
   an ordinary categorical assertion, so no ambient enhanced category or diagram is an
   extra parameter. All indexing object and morphism types are small (`Type 0`), hence
   admit these nerves in any containing universe; no equality of ambient universes is
   imposed. All binders are explicit and `autoImplicit` is disabled.
2. Finite ordinals, including the empty one, with all monotone maps: use Mathlib's
   `AugmentedSimplexCategory = WithInitial SimplexCategory`. `WithInitial.star` represents
   the empty ordinal, and `.of A` represents the nonempty ordinal `Fin (A.len + 1)`.
   The skeleton is exactly the category of finite ordinals, not a bound on cardinality.
   The nonempty subcategory and its inclusion are Mathlib's `SimplexCategory` and
   `AugmentedSimplexCategory.inclusion`.
3. Adjoining a greatest element: `adjoinLast .star = ⦋0⦌` and
   `adjoinLast (.of A) = ⦋A.len + 1⦌`; thus it adds one point even to the empty ordinal.
   In each case that point is `Fin.last (adjoinLast J).len`.
4. The category `D` has exactly the augmented-simplex objects and all the stated maps:
   `LastPointOrdinal` is the existing Mathlib `InducedWideCategory` construction on
   these objects via `adjoinLast`. Its morphisms are simplex maps satisfying
   `preservesLast`, namely `f.toOrderHom (Fin.last A.len) = Fin.last B.len`.
   No restriction is placed on images of ordinary elements. `lastPointCategory` gives
   the existing induced composition of these monotone maps. The identity/composition
   closure is the explicit structural instance `preservesLastMultiplicative`.
5. The functor `i : Δ → D` is `inclusion`, with object `.of A` and arrow
   `SSet.Enhanced.appendLast f`. The full signature and docstring of this dependency
   declaration were read: it sends an ordinary element `x.castSucc` to
   `(f.toOrderHom x).castSucc` and the last element to the last element. It therefore
   never sends an ordinary element to the new last point.
6. The functor `j : Δ₊ → D` is the actual `augmentedInclusion`, constructed by
   `WithInitial.lift inclusion`. It agrees with `i` on nonempty ordinals. On the empty
   ordinal it is `emptyOrdinal`; its empty-source arrows are `emptyArrow`, the constant
   map from the enlarged singleton to the target's last element. There are no ordinary
   source elements in that case, and no maps from a nonempty ordinary ordinal to the
   empty ordinary ordinal. Thus all of `j`, including its empty cases, is supplied.
7. The functor `U : D → Δ` is `forgetLast`, exactly Mathlib's `wideInducedFunctor` for
   `adjoinLast` and `preservesLast`. On objects it is `adjoinLast`; on arrows it keeps
   the underlying simplex morphism. Its targets are always nonempty.
8. The adjunction `i ⊣ U` is the existential `∃ adj : inclusion ⊣ forgetLast`.
   This is Mathlib's adjunction structure, including unit, counit, naturality and both
   triangle identities. No arbitrary functors or a stronger hypothesis are assumed.
9. The specified natural Hom bijection is enforced by
   `∀ (A : SimplexCategory) (J : LastPointOrdinal) (f : inclusion.obj A ⟶ J),
   adj.homEquiv A J f = restrict f`. `restrict` is constructed as the monotone map
   `x ↦ f.hom.toOrderHom x.castSucc`. Bijectivity and naturality in both variables are
   already properties of `adj.homEquiv`; the equality requires this precise restriction
   map, with values at the target's distinguished point allowed.
10. Initiality of the empty ordinal is `Nonempty (IsInitial emptyOrdinal)` in the same
    conjunction and for the same category `D`. `Nonempty` merely turns the universal
    property structure into a proposition; no object or arrow data are chosen from it.

Dependency declarations used:

- Node `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, primary record
  `SSet.Enhanced.coneCategory`; read the entire module and its docstrings. The part used
  concretely here is `SSet.Enhanced.appendLast` (lines 138--159), the existing last-vertex
  extension shared with the enhanced mapping-space convention. The node's quasicategory,
  nerve, functor and cone conventions are retained through this import, without copying
  any definition. The item's `stmt_deps` and every dependency node remain unchanged.
- Mathlib `AugmentedSimplexCategory`, `AugmentedSimplexCategory.inclusion`, in
  `Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic` (definition and inclusion
  at lines 31--42). `WithInitial.lift`, in `Mathlib.CategoryTheory.WithTerminal.Basic`
  (lines 699--715), extends the inclusion by the explicit empty-source maps.
- Mathlib `SimplexCategory.Hom.mk`, `Hom.toOrderHom`, `smallCategory`, and
  `homEquivOrderHom`, in `Mathlib.AlgebraicTopology.SimplexCategory.Defs` (lines 85--153),
  give exactly monotone maps of finite ordinals; `SimplexCategory.const`, in
  `Mathlib.AlgebraicTopology.SimplexCategory.Basic` (lines 45--47), gives empty-source maps.
- Mathlib `InducedWideCategory`, `InducedWideCategory.Hom`, its `category`, and
  `wideInducedFunctor`, in `Mathlib.CategoryTheory.Widesubcategory` (lines 40--78),
  provide the category of the specified arrows and the forgetful functor.
- Mathlib `CategoryTheory.Adjunction` and its `homEquiv`, in
  `Mathlib.CategoryTheory.Adjunction.Basic`, and `CategoryTheory.Limits.IsInitial`
  imported through the augmented-simplex API give the two conclusion structures.

Edge cases checked before and during writing:

- The empty ordinal enlarges to a singleton and remains a genuine object of `D`.
  There is exactly one `D` arrow from it to each object, including itself.
- For an empty target `J`, every `A → UJ` is the unique map to its enlarged singleton;
  its extension gives the unique last-preserving arrow. No target nonemptiness was added.
- A nonempty source may have some or all of its ordinary points mapped to the target's
  new last point. These are valid `D` arrows, and `restrict` does not exclude them.
- For the smallest nonempty source, `A = ⦋0⦌`, the inclusion enlarges its one point to
  two points and the restriction reads exactly the first point.
- Checked unit inclusion and counit folding on original points, the inner last point,
  and the outer last point. Both triangle composites fix every point.
- A finite enumeration checked restriction/extension inverse formulas on 246 arrows
  (original source cardinalities 1 through 4, original target cardinalities 0 through 4),
  two-variable naturality on 23144 composites (sizes at most 3), and singleton-source
  uniqueness for original target cardinalities 0 through 4. These are mathematical
  edge-case checks, not Lean proofs added to a stage-2 module.

Searches actually run:

- `msearch.py leanfinder`: "The simplex category is left adjoint to forgetting an added
  greatest element in the category of last-point-preserving finite ordinal maps".
  Eight hits: ordinary simplex concrete maps, `homEquivOrderHom`, `homEquivFunctor`,
  `toCat`, augmented-simplex and skeletal functors, and realization adjunction. None
  states the category `D` and its adjunction; their exact source APIs were inspected.
- `msearch.py loogle`: `SimplexCategory, CategoryTheory.Adjunction`. Ten hits were
  skeleton/coskeleton, chain-complex, nerve, subdivision and realization adjunctions;
  they have different functors or categories.
- `msearch.py leansearch`: "The natural hom set bijection between maps of finite ordinals
  fixing a new greatest element and arbitrary monotone maps is an adjunction". Eight
  hits included `OrderHom.withTopMap` and the ordinary simplex Hom equivalences, along
  with Galois-connection, free monoid and bounded-lattice adjunctions. No exact match.
- `msearch.py grep`, subdirectory `AlgebraicTopology`:
  `decalage|Decalage|LastPoint|last.*[Aa]djunction|[Aa]djunction.*last`: zero hits.
- Direct `rg` of the project and `lean/Sheaf` for
  `decalage|Decalage|lastPoint|LastPoint|last.*[Aa]djunction|[Aa]djunction.*last`, and
  `grep -rn` of the upstream project for the item id: no declaration for this statement.
  A further full Mathlib/project/Sheaf search for
  `rightDecalage|LastPoint|lastPoint|lastPreserving|LastPreserving|preservesLast`
  found no collision. The item id, `RightDecalage` and `LastPoint` also had no entry
  in `dag/lean_names_upstream.json`.

The category and maps are notions explicitly introduced by this item's own statement;
their helper declarations stay in its owning module and are all listed in
`lean.declarations`. The dependency already defines the needed extension of nonempty
ordinal maps, which is reused. There is no separate missing independent notion to
introduce as a new node. No mathematical statement dispute was found.

Validation: `scompile.py NV lem-coef-right-decalage-index-calculus` compiled the file
in both the sandbox and final library module layouts successfully, with no errors or
warnings (2.1 seconds and 2.0 seconds, respectively). All delivered declarations have
source/blueprint docstrings, every Lean line is at most 100 characters, and the JSON
copy differs from the base only by its `lean` field. The required `deliver2.py NV lem-coef-right-decalage-index-calculus --no-push`
completed successfully: `OK (dry run): commit afdd0effe4 passes the preflight and
compiles; nothing pushed`. The delivery command reruns compilation and server preflight
after this report-only validation update.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
