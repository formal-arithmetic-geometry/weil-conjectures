## Worker report

The module `Sheaf.AlgebraicTopology.JoyalSmallTestUniverseInvariance` states
`SSet.joyal_small_test_universe_invariance`. Its only theorem has proof `sorry`.
No definition, dependency record, or natural-language statement is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The simplicial sets, inner-horn definition of quasicategory, and internal functor
  simplicial sets are Mathlib's existing `SSet`, `SSet.Quasicategory`, and `ihom`,
  publicly imported through the recorded module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` of
  `def-cbc-enhanced-diagrams-cones`. Its recorded declaration
  `SSet.Enhanced.coneCategory` and its helper declarations were read; cones do not
  enter this particular statement, so no new cone construction is introduced.
- Nested universes are represented by explicitly bound universe parameters `u v`,
  with the containing universe `max u v`. This ranges over every enlargement;
  instantiating `v` above `u` includes strictly nested universes. Allowing equal
  levels also expresses the harmless identity transport case.
- Smallness of the total disjoint union of degree sets is represented by
  `{A B : SSet.{u}}` and the first quantifier `(C : SSet.{u})`. Since degrees are
  indexed by the small, countable simplex category, their total disjoint union is
  in `Type u`. Conversely, bijections of the degree sets with small sets transport
  all face and degeneracy maps to a simplicial set in `SSet.{u}`. Simplicial
  isomorphisms preserve the two restriction-equivalence conditions. Thus using
  these representatives does not exclude the node's small-up-to-bijection objects.
- The map `u : A -> B` of the node is the explicit argument `(f : A ⟶ B)`;
  the different letter avoids confusion with the universe parameter. No mono,
  equivalence, quasicategory, or nonemptiness hypothesis is imposed on A or B.
- The ordinary category hS is `hoFunctor.obj S`, from
  `Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat`. I read `HoRel₂`,
  `HomotopyCategory`, `hoFunctor₂`, and `hoFunctor`: this is the free category on
  the reflexive edge quiver modulo triangle relations, after 2-truncation.
  Degenerate edges are identities; arbitrary finite edge words are retained.
- Condition (i) is the left side of `↔`: for every `(C : SSet.{u})` with
  `C.Quasicategory`, the functor
  `(hoFunctor.map ((MonoidalClosed.pre f).app C)).toFunctor` is an equivalence.
  `MonoidalClosed.pre` is the actual restriction from Fun(B,C) to Fun(A,C),
  defined by the closed adjunction, not a freely chosen comparison.
- Condition (ii) is the right side of `↔`, using every `(C : SSet.{max u v})`
  with `C.Quasicategory`. Only f is lifted, with `uliftFunctor.{v, u}.map f`.
  The definition in Mathlib's SimplicialSet.Basic lifts simplices degreewise.
  In particular, C is unrestricted in size within the larger universe and has
  no `LocallySmall`, mapping-space size, or small-model hypothesis.
- Ordinary categorical equivalence is Mathlib's `Functor.IsEquivalence`, applied
  to the induced ordinary functor. It is not merely a bijection of isomorphism
  classes, or an assertion about the core of the functor category.
- The empty simplicial sets and quasicategories are included by the unrestricted
  binders. There is no `Nonempty` or chosen-vertex argument.

Proof dependencies: the sole additional proof module imported is
`Sheaf.AlgebraicTopology.SmallInnerHornCompletion`, whose recorded theorem
`SSet.Enhanced.small_inner_horn_completion` was read together with its signature
and proof docstring. It constructs RX in the original universe and permits all
larger testing targets. Its canonical inclusion and restriction interface are
exactly what steps 2--6 of this node's proof need. The theorem docstring carries
all six proof steps, including finite relation chains and the empty case.

Source check: read the July 30, 2026 version of
[Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Theorem 3.6.8(iii), printed pp. 115--116 (PDF pages 130--131). This gives the
ordinary homotopy-category restriction convention. As the node explicitly says,
the universe refinement is agent-formulated, not a separately numbered theorem
in that source. No change to that attribution is made here.

Edge cases checked mathematically before writing:

- A = B = empty: both restriction functors are identities for every C.
- A = empty, B nonempty: the empty quasicategory detects failure on both sides,
  since Fun(B,empty) is empty whereas Fun(empty,empty) has its unique object.
- B = empty forces A empty for a supplied simplicial map; this is included.
- C = empty, C = point, and identity f all have their usual unrestricted meanings.
- C with large mapping spaces remains allowed on the right. The proof uses a
  small simplicial subset and its horn completion, rather than assuming a small
  full subcategory of C.
- There is no finite-dimensional or positive-degree restriction. Countable horn
  closure and all degrees remain within the small universe.

Searches for existing declarations (2026-10-17):

- `msearch.py ... leansearch`: "Equivalence on homotopy categories of internal
  functor simplicial sets can be tested on small quasicategories in any larger
  universe". Eight hits, including `essentiallySmall_congr`, `locallySmall_congr`,
  `hoFunctor.unitHomEquiv`, and `Truncated.mapHomotopyCategory`; none states this
  equivalence of testing ranges.
- `msearch.py ... leanfinder`: "Testing homotopy categories of internal functor
  simplicial sets against small quasicategories is invariant on enlarging
  universes". Eight hits: QCat, hoFunctor, the two homotopy-category constructions,
  and their instances/extensionality. No universe-testing theorem.
- `msearch.py ... loogle '"Quasicategory", "Small"'`: zero hits.
- `msearch.py ... grep '(small|universe).*(Quasicategory|quasicategory)|[Qq]uasicategory.*(small|universe)' AlgebraicTopology`:
  zero hits in Mathlib.
- `rg` in upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `small.test.universe`,
  `small_test_universe`, and `universe.invariance`: no matching theorem.
  Upstream node-id search also returned no hits.
- Broader `rg` of the shared simplicial and category-theory modules found the
  universe argument in the docstrings of JoyalModelStructure and
  JoyalIntervalBoundaryTests. Their actual declarations concern a model structure
  and interval lifting tests, respectively, and do not state this equivalence.
  JoyalFunctorEquivalenceTest and CategoricalEquivalencesSmallGeneration likewise
  already use larger-universe tests rather than compare them with small tests.

No statement correction, disputed statement, missing notion, or unusable
recorded dependency was found.

## Second reading by N6

The dispatcher explicitly prohibits starting other agents and specifies that the
maintainer independently reviews this delivery. This section records the worker's
second pass, not a claim that an independent worker read it.

Reopened the node and the final Lean signature together. The two quantifiers
respectively range over all u-small and all larger-universe quasicategories;
`Quasicategory` is the only target hypothesis. The argument is an arbitrary map
between two small simplicial sets. Both functors are canonical precomposition
followed by the ordinary edge-word/triangle-quotient homotopy-category functor.
The right-hand lift acts on that same input map. No local-smallness or
nonemptiness condition is present. The conclusion is exactly their iff.
The representable-smallness convention and its invariance under simplicial
isomorphism are documented above and in the module header. No mismatch or
statement edit was found in this pass.

Validation: every delivered Lean file is checked separately using `scompile.py`;
only the expected postponed-theorem warning is allowed. Delivery preflight and
its per-file compilation are run through `deliver2.py --no-push` before push.
