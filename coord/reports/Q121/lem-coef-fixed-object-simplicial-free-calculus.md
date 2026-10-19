## Worker report

Module: `lean/Sheaf/CategoryTheory/FixedObjectSimplicialFreeCalculus.lean`.
Main declaration: `SSet.Bergner.fixed_object_simplicial_free_calculus`.
The only postponed proof is this named theorem, with the seven-step DAG proof in
its docstring. `IsDegreewiseFree` and `IsDegreewiseCoproduct` are concrete predicates
for the two ordinary universal properties introduced in the item's own statement.
They contain no postponed data or proofs. No statement correction, disputed statement,
new node, or dependency repair is needed.

The source was opened and read: Dwyer--Kan, *Simplicial localizations of categories*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf,
printed pp. 269--271 (1.4, 2.1, 2.7) and 276--278 (7.1--7.6). In particular, 7.5--7.6
require the domain of the retract to stay fixed; the Lean retains that requirement.

Hypothesis and clause correspondence:

- The Bergner structure from `lem-coef-coherent-nerve-comparison` is the binder
  `M : CategoryTheory.BergnerModelData.{u}`. Its three classes are characterized
  by the dependency's actual model axioms, DK equivalences, local Kan fibrations
  with equivalence lifting, and cofibrations by lifting. No arbitrary class is
  assumed. `O : Type u` ranges over every small object set, including the empty set.
- Simplicial categories on exactly `O` and identity-on-objects functors are the
  existing `SSet.Bergner.Fixed O`, `FixedHom`, and `fixedCategory`. The simplicial
  mapping sets are `A.Hom a b`. `bundle` and `bundleMap` forget only the fixed-object
  constraint and retain exactly the same enrichment and component maps.
- `I_O` is the existing `discrete O`, with constant mapping sets the Hom sets of
  Mathlib's discrete category. Its canonical map to `A` is `discreteInclusion A`.
  The global initial map is the existing `fromEmpty (bundle A)`.
- Local weak equivalences are the existing `fixedWeakEquivalences O`, requiring
  `Enhanced.IsWeakHomotopyEquivalence` of every mapping simplicial-set map.
  Local Kan fibrations are `fixedFibrations O`, the horn-inclusion RLP on every
  mapping set. These use the recorded realization-based weak equivalences and
  recorded Kan--Quillen horns.
- The first two conjuncts give `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}`.
  The next conjunct gives an actual `ModelCategory (Fixed O)` with all three
  classes fixed to `fixedWeakEquivalences`, `fixedFibrations`, `fixedCofibrations`.
  Thus the model assertion includes the actual lifting, retract and factorization
  axioms, rather than an uninterpreted Prop or a chosen stronger assumption.
- The next two conjuncts are `HasFunctorialFactorization` for cofibrations followed
  by local trivial fibrations, and local trivial cofibrations followed by fibrations.
  “Trivial” is intersection with the same local weak-equivalence class.
- Agreement of cofibrations is the iff for every `f : A ⟶ B`, comparing
  `fixedCofibrations O f` to `M.model.categoryWithCofibrations.cofibrations
  (bundleMap f)`. The following iff compares the canonical discrete initial map
  with the global empty initial map, giving exactly agreement of cofibrant objects.
- For every cofibration `f : A ⟶ B`, the theorem supplies `B'`, `j : A ⟶ B'`,
  `s : B ⟶ B'` and `r : B' ⟶ B`, with `IsFreeExtension j`, `f ≫ s = j`,
  `j ≫ r = f`, and `s ≫ r = 𝟙 B`. Both maps have literally the same domain `A`.
  The reused `IsFreeExtension` asserts degreewise injectivity, chosen subsets of
  generators, their preservation by every degeneracy, and the universal property
  of freely adjoining those generators to the old category in every degree.
  This universal property is precisely `B'_n = A_n * F_n`, with `F_n` the free
  category on that directed graph; no graph relations are imposed.
- The next clause supplies, for every cofibrant `A`, a fixed-object retract from
  an object satisfying `IsDegreewiseFree`. This predicate quantifies independently
  over each degree and a graph of generators, and says each assignment of those
  generators extends uniquely to an ordinary functor with any object function.
  It adds no compatibility of the chosen degreewise graphs, matching the node's
  “free in every degree” conclusion exactly.
- Coproducts exist by `HasColimitsOfSize`. For every colimiting `BinaryCofan.mk i j`,
  `IsDegreewiseCoproduct i j` asserts in every degree that two ordinary functors,
  with the same chosen object function to any small category, extend uniquely to
  a functor on the coproduct. This characterizes the ordinary free product
  amalgamating the identities: all within-factor composition/identity relations
  and no extra cross-factor relations. Using all colimiting cocones avoids
  choosing a particular presentation of the coproduct.
- The final conjunct takes arbitrary `X,X',Y,Y'`, their colimiting coproduct
  cocones, and the induced map `h` characterized by its two commuting triangles.
  The hypotheses are exactly local weak equivalences of `f` and `g`, and the
  conclusion is `fixedWeakEquivalences O h`. No cofibrancy of any of the four
  factors is required. The cocone and triangle premises merely specify the
  canonical arrow `X * Y → X' * Y'`; they are not extra mathematical restrictions.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.BergnerModelData`, its model and three class-characterization
  fields, and the signature/docstring of `CategoryTheory.coherent_nerve_comparison`.
- `Sheaf.CategoryTheory.CoherentNerveInfrastructure` (through that module):
  `CategoryTheory.CoherentNerve.SCat`, `sCatCategory`, `hom`, and `underlying`.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.Fixed`, `FixedHom`, `fixedCategory`, `bundle`, `bundleMap`,
  `fixedWeakEquivalences`, `fixedFibrations`, `fixedCofibrations`, `discrete`,
  `discreteInclusion`, `emptyCat`, `fromEmpty`, `DegreeFunctor`, `IsFreeExtension`.
  The source signatures/docstrings and `simplicial_interval_lifting` were read.
  Its owning landed node, `lem-coef-simplicial-interval-lifting`, is added to
  `stmt_deps` under brief-stage2 §5's authorization to cite landed nodes. Its
  declaration is not rebound or restated.
- The already-stated proof dependencies are imported non-publicly:
  `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`,
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits`. Their recorded statements
  and source declarations were read. The other proof dependencies,
  `lem-coef-sorted-simplicial-algebra-model` and
  `lem-coef-free-resolution-coproduct-augmentation`, currently have no recorded
  Lean declaration; they are proof inputs only and introduce no notion needed
  to type this statement, so no imaginary module is imported.
- Mathlib's `ModelCategory`, `HasFunctorialFactorization`, `HasLimitsOfSize`,
  `HasColimitsOfSize`, `BinaryCofan`, `IsColimit`, and enrichment definitions are
  used directly. All universes and variables are explicitly bound.

Edge cases checked before writing:

- `O` empty: the fixed-object category has one enrichment and one morphism; all
  mappingwise conditions and graph families are empty. Neither `Nonempty O` nor
  `Nontrivial O` appears.
- One object and loop generators: the free-category universal property retains
  arbitrary finite powers of loops, rather than collapsing loops to one arrow.
- Empty mapping sets: mappingwise weak equivalence and coproduct universal
  properties are not replaced by nonemptiness, connectedness, or local Kan
  assumptions. The zero-edge word contributes the identities.
- Degree zero: `n : ℕ` includes zero in all degreewise predicates; the reused
  free-extension definition quantifies over all allowed degeneracies there too.
- All four factors of coproduct invariance may fail cofibrancy and local Kan
  fibrancy. No such typeclass or premise occurs.
- Universe `u` is common to small objects and mapping sets, exactly as in the
  recorded `SCat.{u}` interface. Test categories in the degreewise universal
  properties include every small ordinary category in that universe, so in
  particular include the actual free categories that detect these properties.

Searches performed (all with no exact statement match):

- `msearch.py ... leanfinder "Fixed object simplicial categories have a model
  structure with Bergner cofibrations, strong free retracts and coproducts
  preserving local weak equivalences"`: eight hits, including the Kan--Quillen
  cofibration/fibration instances, `SimplicialCategory`, and
  `ModelCategory.categoryWithCofibrations`; none is this theorem.
- `msearch.py ... loogle '"SimplicialCategory", "Cofibration"'`: zero hits.
- `msearch.py ... grep 'Bergner|free.*simplicial.*categor|fixed.object'
  AlgebraicTopology`: zero hits.
- `rg` in upstream `WeilConjectures/` for fixed-object/free-extension vocabulary,
  and `grep -rn` for this item's id: no upstream declaration of the item.
- `rg` in `lean/Sheaf/CategoryTheory` and `lean/Sheaf/AlgebraicTopology` found the
  reusable definitions in `SimplicialIntervalLifting.lean`. Its theorem gives
  part of the fixed-object model assertion, but does not give Bergner agreement,
  a retract with fixed domain, or coproduct invariance. It is therefore not an
  exact existing match. The downstream inversion module only cites this item
  in its proof plan and does not state its theorem.
- The proposed names `IsDegreewiseFree`, `IsDegreewiseCoproduct`, and
  `fixed_object_simplicial_free_calculus` were searched in Mathlib, upstream and
  `lean/Sheaf` before writing; none existed.

Validation: `scompile.py Q121 lem-coef-fixed-object-simplicial-free-calculus
lean/Sheaf/CategoryTheory/FixedObjectSimplicialFreeCalculus.lean` passed, both the
sandbox elaboration and library-path compilation, with no errors or warnings.


## Second reading by Q121

I independently read the item record, Dwyer--Kan Sections 1.4(iii)--(v), 2.7,
7.2, 7.4--7.6 (the cited pages 269--271 and 276--278), and the complete Lean
signature. The item introduces a small object set `O`, the fixed-object simplicial
category `sCat_O`, its identity-only object `I_O`, the degreewise free-product
coproduct, local mapping-space weak equivalences and local Kan fibrations, then
asserts the following clauses in order:

1. `sCat_O` has limits and colimits, a model structure whose weak equivalences are
   local weak equivalences and whose fibrations are local Kan fibrations, and both
   factorizations are functorial. In the file this is the first two
   `HasLimitsOfSize`/`HasColimitsOfSize` conjuncts, the existential `ModelCategory`
   with classes exactly `fixedWeakEquivalences O`, `fixedFibrations O`, and
   `fixedCofibrations O`, followed by the two `HasFunctorialFactorization` clauses.
   `fixedWeakEquivalences` is the mappingwise
   `Enhanced.IsWeakHomotopyEquivalence` predicate and `fixedFibrations` is the
   mappingwise horn RLP, both from the recorded interval-lifting dependency.
2. Its cofibrations are exactly Bergner cofibrations fixing `O`. The sixth clause
   is the pointwise iff between `fixedCofibrations O f` and
   `M.model.categoryWithCofibrations.cofibrations (bundleMap f)`.
3. Its cofibrant objects are exactly the global Bergner-cofibrant simplicial
   categories with object set `O`. The seventh clause compares the fixed initial
   map `discreteInclusion A` with the global initial map
   `fromEmpty (bundle A)`; this is the initial-map formulation of cofibrancy for
   the same `M.model`.
4. Every cofibration has a retract, keeping its domain `A` fixed, of a free map.
   The eighth clause quantifies `B'`, `j : A ⟶ B'`, and the section/retraction
   maps `s,r`, and uses the existing `IsFreeExtension j`, whose actual fields are
   mappingwise injectivity, degreewise generator subsets stable under degeneracies,
   and the degreewise free-category universal property. Thus no stronger or
   weaker private free notion is introduced.
5. Every cofibrant object is a retract of one free in every degree. The ninth
   clause uses the fixed initial map and `IsDegreewiseFree`, whose independent
   `n : ℕ` quantifier and ordinary `DegreeFunctor` universal property express
   exactly degreewise freeness.
6. Fixed-object coproducts are degreewise ordinary free products. The tenth clause
   applies to every colimiting `BinaryCofan.mk i j` and states the unique extension
   property of `IsDegreewiseCoproduct` in every degree, with arbitrary object map
   and target ordinary category. This is precisely the ordinary coproduct
   universal property and does not choose an extra presentation.
7. A pair of local weak equivalences induces a local weak equivalence on the
   coproduct, without cofibrancy or fibrancy assumptions. The final clause
   quantifies all four factors, both colimit cocones, and the uniquely induced
   `h`, assumes the two commuting triangles and the two mappingwise weak
   equivalences, and concludes `fixedWeakEquivalences O h`.

The imported dependency declarations were opened. `Fixed`, `FixedHom`,
`fixedCategory`, `bundle`, `bundleMap`, `fixedWeakEquivalences`,
`fixedFibrations`, `discrete`, `discreteInclusion`, `fromEmpty`, `DegreeFunctor`,
and `IsFreeExtension` are exactly the landed declarations in
`Sheaf.AlgebraicTopology.SimplicialIntervalLifting`; `BergnerModelData` and its
actual model/class characterizations are exactly those in
`Sheaf.CategoryTheory.CoherentNerveComparison`. No declaration is shadowed or
redefined. The extra dependency `lem-coef-simplicial-interval-lifting` in the
sandbox node is the owning node for these landed declarations and is correctly
recorded; the shared base node had not yet received the promoted `lean` record.

I found no mismatch between the node and the Lean signature. In particular, the
Lean has no nonemptiness, finiteness, Noetherian, Kan, cofibrancy, or characteristic
hypothesis; it keeps the retract domain fixed; and it quantifies coproduct factors
without cofibrancy. `O : Type u` includes the empty set, and all degree quantifiers
include `n = 0`. Empty mapping sets, zero/identity-only categories, loop generators,
and arbitrary target object maps are covered by the explicit universal properties.
The shared universe `u` is the same universe used by `Fixed`, `SCat`, and the
small ordinary test categories, so no covered case is excluded by an independent
universe.

The existing-definition searches were repeated with `rg` over the shared
`lean/Sheaf`, the slopmaster2 `WeilConjectures` tree, and Mathlib, and with the
recorded LeanFinder/Loogle searches. They found only the reusable fixed-object
and model-category infrastructure; no `IsDegreewiseFree`, `IsDegreewiseCoproduct`,
or fixed-object free-calculus theorem. Therefore this is a genuinely new
statement module. The module compiled cleanly through
`scompile.py Q121 lem-coef-fixed-object-simplicial-free-calculus` (sandbox and
library-path checks, no errors or warnings). No repair was necessary.
