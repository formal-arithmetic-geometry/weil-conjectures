# Absolute marked tests and categorical equivalences

## Worker report

The module `Sheaf.AlgebraicTopology.MarkedFlatCategoricalEquivalenceTest` states
`SSet.Marked.marked_flat_categorical_equivalence_test`, with proof `sorry`.
It also constructs `SSet.Marked.naturalMap`: its underlying map is the supplied simplicial
map, and its marking-preservation proof transports an inverse and both inverse triangles,
or transports the degeneracy witness. This helper supplies the canonical map mentioned by
the item; it is not a new independent mathematical notion. Its data contain no `sorry`.

Hypotheses and clauses, checked against the current node:

- Small simplicial sets are the unrestricted `B E C A : SSet.{u}` binders.
  The first clause assumes only `[Quasicategory E]` and takes every `b : B ⟶ E`.
  In particular `B` is not assumed to be a quasicategory.
- The canonical map `B-flat → E-natural` is literally
  `flatMap b ≫ flatToMarked (natural E)`; both factors retain the specified underlying map.
  The existing `flat` marks exactly degenerate edges. The existing `natural` marks
  equivalence edges together with degeneracies; the point-model theorem identifies this
  with precisely the equivalence marking for the quasicategory `E`.
- Absolute marked weak equivalence is the recorded `SSet.Marked.weak`, testing the actual
  `mapSharpPre` against every naturally marked quasicategory.
- Categorical equivalence is expanded verbatim from `SSet.exists_joyal_model_structure`:
  for every `Q : SSet.{max u v}`, `Q.Quasicategory` implies `IsEquivalence` for the ordinary
  functor obtained by applying `hoFunctor` to precomposition with the lifted input map.
  Thus the first `↔` is exactly the node's flat-to-natural equivalence assertion.
- The second conjunct binds `C E`, assumes `[Quasicategory C] [Quasicategory E]`, and
  quantifies over every `c : C ⟶ E`. Its left side is `weak (naturalMap c)` and its right
  side is the same categorical test. No inverse or extra marking assumption is supplied.
- The third conjunct quantifies over arbitrary `t : A ⟶ B`, with no fibrancy hypothesis.
  Its left side is the same categorical test; its right side tests
  `Enhanced.IsWeakHomotopyEquivalence (Enhanced.coreMap
  ((MonoidalClosed.pre (uliftFunctor.{v, u}.map t)).app Q))` for every quasicategory `Q`.
  This is the specified precomposition map on the existing cores, not an arbitrary map
  between objects of the right types. Weak homotopy equivalence uses realization and
  bijections on components and all positive based homotopy groups.
- Universes `u v` are explicitly declared and unrestricted. `max u v` includes every
  containing test universe, including the original universe. The theorem can itself be
  instantiated with enlarged inputs. The existing point-model theorem explicitly supplies
  invariance of `weak` under `enlargeMap`; no new size equality or small-test restriction is
  imposed. All variables are explicit under `set_option autoImplicit false`.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.core`,
  `SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.IsWeakHomotopyEquivalence`.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`: `SSet.exists_joyal_model_structure`;
  the statement uses its exact `hoFunctor`/`MonoidalClosed.pre` testing formula.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked.flatMap`,
  `SSet.Marked.natural`, `SSet.Marked.weak`, `SSet.Marked.marked_point_cartesian_model`.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`: `SSet.Marked.flatToMarked` and
  the proof input `SSet.Marked.marked_anodyne_lifting_calculus`.
- `Sheaf.CategoryTheory.IsofibrationPullbackLimit`: `SSet.Enhanced.coreMap`.
  The last two already-landed nodes are added to `stmt_deps` to record the canonical
  maps used directly in the signature. Their statements and Lean records are unchanged.
- The remaining recorded proof inputs are imported without `public`:
  `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest` / `SSet.joyal_functor_equivalence_test`,
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` /
  `SSet.Enhanced.enhanced_functor_cone_calculus`,
  `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus` /
  `SSet.homotopyCategory_triangle_calculus`, and
  `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak` /
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`.

The theorem docstring gives all seven proof steps: identify minimal and natural mapping
cores; restrict coherent inverses to cores; curry tests against `Fun(K,Q)`; use the two
identity-functor tests to obtain a quasi-inverse; deduce each marked-map equivalence;
and check enlargement and empty inputs.

Edge cases: empty-to-empty passes all tests. For empty-to-nonempty, the empty test
quasicategory gives an empty-to-point core map, which fails on components. The assumptions
never select an input vertex. Identity maps are included. A merely simplicial source is
allowed in the first and third clauses. Degenerate edges, including at isolated vertices,
are preserved by the explicit helper. No nonemptiness or nondegeneracy restriction occurs.

Source check: read HTT Remark the project server, Lemma the project server, Proposition the project server and
Proposition the project server in the author's published-book PDF
https://www.math.ias.edu/~lurie/papers/highertopoi.pdf (printed pp. 154–156).
The node's HTT.pdf endpoint timed out; this is the same author's alternate source.
These give the core identities and two-test-object argument used in the node.
No node correction is required and no statement is disputed.

Searches: the interrupted turn's `searches.jsonl` is preserved. It records successful
`msearch.py` LeanFinder, LeanSearch, Loogle and Mathlib grep calls, reproduced below.
The resumption additionally searched `lean/Sheaf` and upstream `WeilConjectures` by
`marked_flat_categorical_equivalence_test`, `naturalMap`, marked/categorical-equivalence
patterns, and the exact node id. There is no existing declaration of this combined
statement or of this natural-marking map. The existing `coreMap` was found and reused.
`CoherentNerve.IsCategoricalEquivalence` uses a same-universe core-testing convention;
the assigned node explicitly uses the Joyal homotopy-category test, so the statement
retains that dependency's exact formula and proves its comparison with cores.
No duplicate categorical-equivalence definition is introduced.

- leanfinder: `Absolute marked weak equivalences of minimally marked simplicial sets into naturally marked quasicategories are categorical equivalences detected by restriction on functor cores`. Result: 8 hits; SimplexCategory.SkeletalFunctor.isEquivalence, SSet.QCat, CategoryTheory.nerveFunctor.fullyfaithful, CategoryTheory.hoFunctor.instIsLeftAdjointSSetCatHoFunctor, SSet.Truncated.HomotopyCategory.functorEquiv, SSet.Truncated.instCategoryHomotopyCategory₂, SSet.OneTruncation₂.nerveEquiv, SSet.Truncated.HomotopyCategory₂.instCategoryStruct. No exact match.
- grep: `marked.*[Ee]quivalence|[Cc]ategorical[Ee]quivalence|coreMap` in `AlgebraicTopology`. Result: 0 hits; none. No exact match.
- leansearch: `Marked weak equivalences of naturally marked quasicategories are categorical equivalences detected by cores of functor simplicial sets`. Result: 8 hits; HomotopicalAlgebra.WeakEquivalence.mk, HomotopicalAlgebra.mem_weakEquivalences, HomotopicalAlgebra.weakEquivalence_iff, HomotopicalAlgebra.weakEquivalences, HomotopicalAlgebra.CategoryWithWeakEquivalences.weakEquivalences, HomotopicalAlgebra.weakEquivalences_op, HomotopicalAlgebra.weakEquivalences_eq_unop, HomotopicalAlgebra.ModelCategory.categoryWithWeakEquivalences. No exact match.
- loogle: `SSet, "categoricalEquivalence"`. Result: 0 hits; none. No exact match.

## Worker self-check

Re-read each of the three conjuncts against the node. The first source is unrestricted,
the second source and target are quasicategories, and the final test uses the specified
core restriction in every containing universe. Existing predicates and canonical maps
are reused. The helper has actual data and no postponed proof. The only theorem is the
assigned node and its proof is `sorry`. The shared repository and upstream sources were
not edited. Independent review is left to the maintainer, as required by the dispatch brief.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
