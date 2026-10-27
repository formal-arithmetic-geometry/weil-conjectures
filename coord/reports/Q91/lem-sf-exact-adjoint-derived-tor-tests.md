## Worker report

The item is stated in `Sheaf.CategoryTheory.DerivedCategory.ExactAdjointTorTests`.
Its only postponed proof is
`CategoryTheory.ExactAdjointTorTests.exact_adjoint_derived_tor_tests`.
Definitions have real data. No original statement or proof text was corrected.
The item gains only the statement dependency `def-sf-kflat-tensor-presentation`.

Hypothesis and conclusion correspondence:

- The categories are `A : Type uA`, `B : Type uB`, with independent morphism
  universes `vA`, `vB`, `Abelian` structures and chosen ordinary unbounded
  `HasDerivedCategory.{wA}` / `HasDerivedCategory.{wB}` structures. None of the
  six universes are identified.
- Symmetric monoidal abelian categories are `MonoidalCategory`,
  `MonoidalPreadditive`, `SymmetricCategory` on A and B. Countable coproducts
  provide the sums in the statement's direct-sum total tensor, with no exactness
  of filtered colimits, Grothendieck, closedness or projective-resolution assumption.
- The specified derived tensor structures are `MonoidalCategory` and
  `SymmetricCategory` on their derived categories, with `_tensorA` and `_tensorB`
  the recorded `DerivedCategory.KFlatTensorPresentation`. Its resolution field
  supplies K-flat resolutions of every unbounded complex; its natural comparison
  identifies the given tensor on K-flat pairs with the existing signed total
  tensor. It adds no common choice of resolutions between A and B.
- K-flatness reuses `CochainComplex.IsKFlatForTotalTensor`, the existing two-sided
  quasi-isomorphism test. This is equivalent to the statement's acyclic test:
  tensor the quasi-isomorphism from zero to an acyclic complex for one direction;
  for the other, use that a map is a quasi-isomorphism exactly when its cone is
  acyclic, and signed total tensor commutes with this finite-sum cone. Thus the
  package does not introduce a distinct notion of K-flatness.
- `E`, `R`, the two `Additive` instances and their finite-limit and finite-colimit
  preservation instances render precisely the two additive exact functors.
  `a : E ⊣ R` retains the supplied ordinary adjunction. `E.mapDerivedCategory`
  is J and `R.mapDerivedCategory` is D(R).
- `P`, `c` and `P.IsLeftDerivedFunctor c ...` are the chosen total left derived
  R with its universal counit. `α : P ≅ R.mapDerivedCategory` is the supplied
  exact comparison. `_compatibility` is the counit equation
  `whiskerLeft Qh α.hom ≫ R.mapDerivedCategoryFactorsh.hom = c`.
- `transportedAdjunction a α` is the actual degreewise-localized adjunction
  transported using `ofNatIsoRight α.symm`; neither unit nor counit is an
  arbitrary supplied arrow. `P.Monoidal` retains its specified strong monoidal
  structure, whose lax tensorator is the displayed μ.
- `projection a α K L` is J(η_K tensor 1), then J(μ), then ε. The universally
  quantified `IsIso (projection ...)` is exactly the assumed invertibility of q.
- `DerivedCategory.singleFunctor A 0` and its B analogue are A[0] and N[0].
  The component of `R.mapDerivedCategorySingleFunctor 0` is precisely σ_N.
  `comparison a α K N` is inverse q followed by J(1 tensor (α then σ)),
  in the exact order in the item. It is a fixed arrow, not a chosen isomorphism.
- The first conclusion says this arrow is `IsIso` for every K,N; together with
  the actual arrow this is the derived isomorphism, not merely a per-degree fact.
  The second conclusion is joint naturality for every derived f and heart map g,
  using `(singleFunctor A 0).map (R.map g)` on the target.
- The final conclusion quantifies all K and all integers a,b. The hypothesis
  quantifies every M in A and every q outside `Set.Icc a b`, using `IsZero`
  of the actual homology object of K tensor M[0]. The conclusion tests every
  N in B for exactly the same q,a,b on JK tensor N[0]. No a ≤ b hypothesis,
  boundedness, constructibility, coefficient regularity or projective condition
  has been introduced.

Dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
- `def-weil-exact-derived-adjunction` retains its landed binding to
  `Sheaf.SixFunctors.OpenTensorNormalizationData`,
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`, imported publicly.
  Its full signature, docstring and localization body were read. The same body
  with independent universes is the item-owned helper
  `CategoryTheory.Adjunction.exactDerivedOfUniverses`, in `ExactAdjointTorTests`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactorsh`,
  `mapDerivedCategorySingleFunctor`; this is the recorded Mathlib match of
  `lem-sf-exact-functor-derived-triangulated`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryHomologyFunctorIso`, read with its docstring and
  construction; imported privately for the proof dependency
  `lem-weil-pbc-exact-functor-bounded-below`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor`, the existing binary total tensor
  interface of `def-sfb-preserves-kflat-quasi-iso` used by the new definition.
- `Mathlib.CategoryTheory.Functor.Derived.LeftDerived`:
  `Functor.IsLeftDerivedFunctor`, the ordinary total derived universal property.

Edge cases checked: identity adjunction gives the usual single-complex tensor
comparison; K=0 and N=0 have the expected zero tests; a=b retains its one possible
nonzero degree; a>b tests all degrees and transfers total acyclicity. Negative
endpoints and arbitrary unbounded K are included. Naturality allows arbitrary
derived morphisms f, not just maps between selected resolutions. The functors
need not be faithful or equivalences. Independent universes elaborate.

Searches were run with msearch.py (all responses are in searches.jsonl):

- LeanFinder: “Exact adjoint functors with invertible derived projection comparison
  preserve Tor amplitude and give natural degree zero tensor test isomorphisms”:
  eight hits on Tor, Ext and exact-functor factorizations, no match.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal`: twelve
  hits on ordinary monoidal adjunctions, none for the present derived Tor tests.
- Mathlib grep: `projectionComparison|torAmplitudeIn_mapDerivedCategory|exactAdjointDerivedTor`:
  no hits. Project rg for the item id, Tor-test names and proposed declaration
  names: no existing item declaration.
- LeanSearch for a chosen derived K-flat tensor presentation: eight hits on
  HomologicalComplex.tensorObj, generic localization monoidal structures and
  projective Tor, no exact packaging.
- LeanFinder for an abstract acyclic-test K-flat tensor presentation: eight hits
  on projective Tor and graded tensor colimits, no match.
- Mathlib grep `KFlatTensorPresentation|IsAcyclicTotalTensorKFlat|KFlat.*Model`:
  zero hits. Project searches found the existing K-flat predicate (reused),
  native derived monoidal constructions requiring extra graded/flat-resolution
  assumptions, and RingedEquivalenceTensorDescent.TensorModel, requiring extra
  countable tensor preservation and a monoidal structure on complexes. None
  matches the binary presentation under the present general hypotheses.
- `tools/blueprint_refs.py search K-flat tensor presentation` returns only the
  broader blueprint unit sk-def-sfb-derived-categories. DAG text and project
  declaration searches found no existing definition node for this package.

Both delivered modules compiled separately with scompile.py, in dependency
order, cleanly (library checks: 5.9 s and 13.3 s). No proofs beyond definitions were supplied; no warnings remained.
The theorem's docstring contains all four accepted proof steps and their inputs.
No STATEMENT-DISPUTED issue was found.

## New nodes

`def-sf-kflat-tensor-presentation` packages exactly the missing chosen binary
K-flat tensor computation in its own module. The signed total tensor and K-flat
predicate are reused from `def-sfb-preserves-kflat-quasi-iso`. The chosen ordinary
derived category is from `def-weil-abstract-derived-category`. The package contains
resolution existence, a natural comparison on pairs of complexes and its
invertibility on K-flat pairs, so every pair of K-flat resolutions computes the
specified tensor. Source: the item's finite Tor amplitude paragraph and the
K-flat descent construction in blueprint lem-sfb-derived-monoidal.proof.md.
The three required kinds of searches and the project/DAG checks are recorded
verbatim in the new node. This is data and properties of the assumed tensor,
not a theorem asserting resolutions exist for arbitrary abelian categories.

## Repair of returned delivery

The immutable-head return d906a7c4731a raised H13+H4: the packet rebound
Q22's landed `def-weil-exact-derived-adjunction` record to a second module,
orphaning the declaration used by existing consumers. The repair follows the
return's explicit option (a): `exactDerivedOfUniverses` is now an item-owned
helper in `ExactAdjointTorTests.lean`, included in the item's `lean.declarations`
and carrying the item's blueprint docstring. The standalone
`ExactAdjunctionOfUniverses.lean` is removed. The dependency node copy is restored
byte for byte from live, including its original module, declaration, statement,
existing flag and review metadata; it contributes no changed dependency record.
`OpenTensorNormalizationData` is publicly imported, leaving all its consumers
and the localized adjunction they use intact. The helper uses the identical
CatCommSq factorizations and degreewise localization, with independent universes.
The item's mathematical statement and theorem signature are unchanged.

## Second reading by Q91

Repair self-check, performed directly without starting another agent as the
worker brief requires. Re-read the returned H13+H4 diagnostic, the landed
adjunction signature and full definition, the item module and both delivered
node records. The helper now belongs to the item; there is no dependency-record
rebind and no separate helper module. All previously accepted clauses remain:
transport along α.symm, q in unit/tensorator/counit order, τ as inverse q then
J of tensoring with α followed by σ, the counit compatibility orientation,
invertibility, joint naturality, and the same all-heart-object interval including
a > b. The K-flat tensor presentation is unchanged. JSON signatures are checked
against the Lean source, and every delivered file compiled cleanly through scompile.
