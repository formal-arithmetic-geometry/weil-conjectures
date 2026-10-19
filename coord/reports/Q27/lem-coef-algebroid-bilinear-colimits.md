## Worker report

Item: lem-coef-algebroid-bilinear-colimits. Module:
`Sheaf.CategoryTheory.AlgebroidBilinearColimits`. Main declaration:
`SSet.Enhanced.Algebroid.bilinear_change_preserves_small_colimits`.

The module states Haugseng, *On the tensor product of enriched infinity-categories*,
arXiv:2311.13362v1, Corollary 9.2, for the algebroid category of the recorded
`def-coef-complete-algebroid`. Corollary 3.2 and Definition 2.2 specify its canonical
operation; Corollary 8.17 is its presentable case. Source opened and read online:
https://arxiv.org/html/2311.13362v1#S9, together with Section 3.

The conclusion packages a representative of the canonically prescribed bifunctor and
its separate cocontinuity. It does not select a functor from an unspecified existence
assertion. `BinaryChangeOfEnrichment` specifies the output object space and the whole
algebra functor on every simplex and every chain in the varying many-object operad.
Thus the existential is a way of representing the named canonical construction,
not permission to find some colimit-preserving map with different action.
All helper declarations belong to that same construction, are listed in `lean.declarations`,
and have source/blueprint docstrings. No independent new notion or dependency repair is used.

Hypothesis and clause correspondence:

- The three monoidal infinity categories are the simplicial total spaces `E F G`,
  with their explicit `Quasicategory` instances, and the projections `p q r` to
  `monoidalSimplexBase`. `hp hq hr : IsCocompleteMonoidal ...` assert, separately
  for each, `IsMonoidalInfinityCategory`, `HasSmallColimits` of the fiber at `[1]`,
  and preservation of all small colimits by each fixed-object tensor functor.
  The last clause quantifies over the actual active tensor operations
  `IsMonoidalTensorOperation` and uses the dependency's `tensorWith`. There is
  no presentability or local-smallness hypothesis.
- Small means universe `u`, with arbitrary containing universe `max (u+1) v`.
  `IsSmall.{u, max (u+1) v}` tests indexing simplicial sets in that containing
  universe; this is the dependency's size convention. No equality between the
  small and ambient universes is assumed.
- The product monoidal category is `pullback p q` with projection
  `binaryCoefficientBase p q`. Its fiber at `[n]` is the product of the two
  coefficient fibers, as required for the product monoidal structure.
- The given strong monoidal functor is `b : pullback p q ⟶ G`, with
  `hb : IsStrongMonoidalInfinityFunctor (binaryCoefficientBase p q) r b`.
  This is the recorded monoidal-infinity-category predicate, including the
  equation over Delta-op and preservation of all cocartesian edges.
- `binaryCoefficientInclusion` is the actual pairing of the two fiber inclusions;
  `binaryCoefficientFunctor b hb` restricts b to the fiber at `[1]` by a literal
  pullback lift. `hcolim : PreservesSmallColimitsSeparately ...` says that b
  preserves small colimits in each variable. This is not joint preservation
  of colimits in the cartesian product category.
- `H : BinaryChangeOfEnrichment.{u,v} p q r b` is the algebroid bifunctor.
  Its source is exactly `total p ⊗ total q` and its target exactly `total r`;
  `total` is the recorded dependency's Algd, not its complete subcategory.
- `H.objectSpaces` specifies the product of object spaces via the universal
  family of points. The map `points` covers `product`, and the canonical map
  from the product point family to the pullback along `product` is an isomorphism.
  Therefore the fiber over `(X,Y)` is exactly the pair of point fibers, X times Y.
  This is a strict representative of the canonical product: in the coherent-nerve
  Kan-complex model, products and their point maps give this cartesian square.
  Its existence is included in the conclusion, not added as a hypothesis on V,W,T.
- `H.object_formula` gives the product parameter for every simplex, not only
  for vertices. `binaryFamilyMap` explicitly sends each coordinate in every
  relative-nerve chain through its family map. `binaryDomainLeft` and
  `binaryDomainRight` are the two product-family projections;
  `binaryDomainProduct` is the comparison to the output family.
- `H.algebra_formula` says that the output value at every operad simplex is
  `b.app _ t`, where the two pullback projections of t are precisely the input
  algebra values. The displayed equalities uniquely specify the coefficient
  pair t. At arity `[1]` this is the mapping object
  `b(A(x,x'), B(y,y'))`; in every other arity it also fixes composition, units,
  coherent transformations, faces and degeneracies. The cartesian point-family
  comparison ensures that this tests every output-family simplex. The proof
  binders hA,hB,hC only identify the required fibers and are propositionally
  irrelevant; object_formula and naturality provide their compatibility.
- The conclusion `PreservesSmallColimitsSeparately.{u} H.functor` is the two
  universal assertions for fixing B and fixing A. Each uses the existing
  `PreservesColimitsIn`, which sends every colimiting coherent cocone through
  the actual mapped-cocone construction and asserts it remains colimiting.
  Thus it concerns the canonical colimit comparisons, not abstract isomorphisms
  between unrelated colimit objects.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: the full recorded module was read,
  including the docstrings and signatures of `total`, `universalFamily`,
  `familyDomain`, `FamilySimplex`, `TotalSimplex`, `totalAmbient`, `totalForFamily`,
  `tensorWith`, and `IsPresentablyMonoidal`. We use `total`, `universalFamily`,
  `familyDomain`, `FamilySimplex`, and `tensorWith` directly. The existing fiber,
  relative-nerve and universal-point-family constructions are not copied.
- Its public dependency `Sheaf.CategoryTheory.MonoidalInfinityCategory`:
  `monoidalSimplexBase`, `monoidalUnderlying`, `monoidalFiberInclusion`,
  `IsMonoidalInfinityCategory`, `IsMonoidalTensorOperation`, and
  `IsStrongMonoidalInfinityFunctor`. Their complete definitions were read.
- Its public dependency `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.HasSmallColimits`, `PreservesColimitsIn`, and `IsSmall`.
  In particular preservation uses the dependency's mapped coherent cocones.
- The relative-nerve simplex data are from
  `Sheaf.CategoryTheory.KanRelativeNerveLeftFibration`; the universal point-family
  normalization is from `Sheaf.CategoryTheory.UniversalLeftFibrationIdentity`.
  Their sources and relevant complete interfaces were read.
- All eight proof dependencies currently have no Lean record in the shared DAG.
  Accordingly none is imported solely for the proof. The seven-step proof docstring
  records their roles in order, including both variables, fixed-endpoint Segal
  locality, the universe enlargement, and the genuinely cocontinuous unary factor.

Edge cases checked before writing:

- Empty indexing simplicial sets are admitted by `IsSmall`, with no `Nonempty`
  binder: preservation includes the initial algebroid in both variables.
- Object spaces may be empty or disconnected. The universal-family product
  condition does not require points or connectedness. An empty factor gives the
  empty product fiber. The fixed factor may itself be the empty algebroid.
- Arity zero is retained by `familyDomain` and `binaryFamilyMap`; the coordinate
  function can have an empty indexing type, but the family base remains present.
  Thus units are not lost by reducing the formula to Hom objects only.
- Constant and degenerate chains are included in the `a : [m] ⟶ [n]` binder;
  the normalization applies to coherent diagrams, not merely their vertices.
- No assumption of presentability, common coefficient smallness, completeness
  of algebroids, or joint cocontinuity of b is present.
- The cartesian point-family square fixes the space product even when a fiber is
  empty. It is not a vacuous test based on choosing a point of each object space.

Searches performed (all Mathlib service searches via msearch.py):

- LeanFinder: "Bilinear change of enrichment of operadic infinity algebroids
  preserves colimits separately". Eight hits, including
  `CategoryTheory.EnrichedCat.bicategory`, whiskering, ordinary enriched
  composition, and simplicial enrichment of simplicial objects. These are strict
  enriched ordinary categories or their bicategories, not operadic algebroids
  over space-valued object parameters. No matching statement.
- Loogle: `"Enriched", "PreservesColimits"`. Zero hits.
- Mathlib grep: `algebroid|[Ee]nrich.*[Cc]olimit|[Cc]olimit.*[Ee]nrich`.
  One hit in `Mathlib/Algebra/LieRinehartAlgebra/Defs.lean`, unrelated Lie algebroids.
- LeanSearch: "Bilinear change of enrichment on infinity algebroids preserves
  small colimits separately". Eight hits, primarily
  `CategoryTheory.Limits.PreservesColimit₂` and its constructors, ordinary
  bifunctors and cocones; other hits are base change of bilinear forms. No match.
- Direct rg of the upstream `WeilConjectures` source for the exact item id and
  `algebroid|Algebroid`: no hits. The corresponding upstream-name-index search
  also returned none.
- Direct rg of `lean/Sheaf/CategoryTheory` for `bilinear`, `Bilinear`,
  `externalProduct`, `changeEnrichment`: no existing binary algebroid construction.
  The algebroid search located the recorded `CompleteAlgebroid` module, which
  supplies Algd but no binary change-of-enrichment operation or colimit theorem.
- Duplicate-name search over Mathlib, upstream, and `lean/Sheaf` for
  `IsCocompleteMonoidal`, `PreservesSmallColimitsSeparately`,
  `binaryCoefficientBase`, `BinaryObjectSpaces`, `BinaryChangeOfEnrichment`,
  and `binaryFamilyMap`: no existing declaration.

No statement correction, disputed statement, dependency record repair, or new DAG
node is necessary. The only sorry is the main theorem corresponding to this item.
Helper definitions have real data; the proofs inside definitions only establish
simplicial naturality or the equations required by actual pullback lifts.

Validation: scompile.py compiled this file both under its sandbox name and under
its intended library module name, within the 60-second limit, with no errors and
no warnings. No project/global build was run.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
