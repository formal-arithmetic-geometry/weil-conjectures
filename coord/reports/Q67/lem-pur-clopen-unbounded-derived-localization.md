## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization` states
`AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.clopen_unbounded_derived_localization`.
Its conclusion is `LocalizationStatement`: this fully defined proposition existentially
quantifies the complex, homotopy, and derived comparison diagrams and states their
properties as labeled conjuncts. It is a conclusion to be constructed, not an
extra assumption. All postponed assertions use `sorry`; helper definitions have real data.

Hypotheses, with no source correction:

- `X : Scheme.{t}` is the scheme; `I : Type w` and `[Finite I]` give any finite index set,
  including the empty set. `Y : I → Scheme.{t}` and `j : ∀ i, Y i ⟶ X` are its components.
- The two instance families `IsOpenImmersion (j i)` and `IsClosedImmersion (j i)` express
  open and closed subschemes. `hd` is pairwise disjointness of their image sets and `hc`
  says their images cover every point of X.
- `topology X` and `topology (Y i)` are the recorded small pro-etale sites. No equality
  between their object and morphism universes is imposed. Module sections live in
  `max v w (t+1)`, containing both the site and the finite index universe. `t,u,v,w`
  are explicitly declared. The standard unbounded localization uses its full morphism
  universe `max u (v+1) (w+1) (t+2)`.
- `R : Sheaf (topology X) RingCat.{u}` and `hcomm` express a sheaf of commutative rings,
  following the recorded module-gluing interface. Commutativity holds on every test
  object. `clopenRingRestriction` gives exactly the restricted coefficients.
- `gluing`, `moduleUnit`, `moduleCounit`, and `insertion` select the fully specified
  sectionwise data of `clopen_ringed_module_gluing`, whose proof in the imported module
  is complete. The theorem specifies scalar action, restriction maps, morphisms,
  restriction-of-sections unit, and projection counit. These helpers do not select
  data from a postponed bare existence assertion.

Conclusion, clause by clause:

- Unbounded cochain complexes are Mathlib `CochainComplex _ ℤ`. `complexRestriction`
  is `mapHomologicalComplex (.up ℤ)` of the recorded module restriction. `complexGluing`,
  `degreeIso`, and `differential` specify gluing each degree and each differential,
  naturally also on chain maps.
- `complexUnit` and `complexCounit` give inverse equivalences. Their `_degree` conjuncts
  identify them with the specified module unit and counit. `complex_triangle₁` and
  `complex_triangle₂` give both triangle equations.
- `homotopyFamily` applies the same restrictions through Mathlib's homotopy quotient.
  `homotopyGluing`, the two isomorphisms, their two factorization comparisons,
  normalization equations, and both triangle conjuncts give the induced inverse
  equivalences on homotopy categories, with the same unit and counit.
- `restriction_cohomology` and `insertion_cohomology` are natural isomorphisms of
  functors for every integer m. `acyclic_iff` and `quasiIso_iff` express both directions
  of componentwise detection, for every unbounded complex and every chain map.
- `derivedFamily` is the tuple of `restriction.mapDerivedCategory` and the target is
  the product of the actual component derived categories. `derivedGluing`, `derivedUnit`,
  `derivedCounit`, and both derived triangle equations express the inverse equivalence.
- `restrictionFactors`, its component normalization, and `gluingFactors` are exactly
  the comparisons with Q and the product of the component Q's. The two derived
  normalization equations say that the unit and counit are the localized degreewise
  module maps, through precisely those comparisons.
- `restriction_triangulated` uses the canonical exact-functor shift comparison.
  `componentShift` is the coordinatewise existing derived shift. `gluingShift`, its
  zero and addition equations, its counit normalization, and `gluing_triangulated`
  express that inverse gluing is triangulated for tuples of distinguished triangles.
  This directly expresses the product triangulation on shifts and triangles rather
  than choosing a different structure on any component derived category.
- `derivedInsertion` is the canonical exact-functor localization of the same module
  insertion; `mapDerivedCategoryFactors` supplies its localization comparison.
  `restriction_insertion` gives the identity in its own coordinate and
  `restriction_other_insertion` gives a natural isomorphism to the zero functor off
  that coordinate.
- `insertion_restriction_sum` and `gluing_sum` are bilimit bicones in functor categories,
  with vertices equal to the identity and inverse gluing respectively. These are
  precisely the two natural finite direct-sum formulas, also for an empty family.
- `derived_cohomology` is a natural isomorphism of functors on all derived objects
  and morphisms for every integer m. `isZero_iff` and `isIso_iff` state joint detection.
- `empty_component`, `zero_coefficients`, and `empty_partition` give zero complexes
  and equivalence of the derived categories with `Discrete PUnit.{1}`, the one-object,
  one-arrow category. The empty-partition clause also explicitly states `IsEmpty X`
  and terminality of the product derived category.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` and the imported upstream extension:
  `Scheme.ProEt` and `Scheme.ProEt.topology` (objects in t+1, morphisms in t).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent existing Mathlib `SheafOfModules`, with Mathlib's abelian instance.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`:
  `clopenRingRestriction`, `clopenModuleRestriction`, `clopenRestriction`,
  `clopenModuleRestriction_additive`, and `clopen_ringed_module_gluing`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`, additivity and essential
  surjectivity of Q, and the existing derived triangulation.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory` and `Functor.mapDerivedCategoryFactors`, including
  their canonical shift structure and triangulatedness.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its localization comparison.
- Proof imports: `Mathlib.CategoryTheory.Localization.Pi` (`Functor.IsLocalization.pi`),
  `Mathlib.CategoryTheory.Localization.Predicate` (`Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`), and
  `Mathlib.CategoryTheory.Adjunction.Limits` (equivalences preserve limits and colimits).
  The exact-functor complex cohomology comparison uses
  `Functor.homologyFunctorIso` in `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

Edge cases read against the statement: singleton identity partition, an empty component
among nonempty components, all components empty, the empty partition, the zero ring sheaf,
negative and zero cohomological degrees, and unbounded complexes. No finiteness condition
on cohomological support, nonzero coefficient hypothesis, or nonempty-index instance is
added. Natural isomorphisms are functor isomorphisms, not pointwise choices. Finite sums
are specified by bilimit universal properties without requiring a noncanonical chosen sum.

Searches made:

- msearch LeanFinder: “finite clopen decomposition unbounded derived categories module
  sheaves restriction gluing equivalence”: eight hits about locally constant or condensed
  modules; no exact match.
- msearch LeanFinder: “An unbounded complex of module sheaves on a finite clopen partition
  is equivalent to the tuple of its restrictions, and this induces a normalized equivalence
  on derived categories”: eight hits, including bounded derived representatives and
  singular complexes; no exact normalized statement.
- msearch Loogle: `Functor.mapDerivedCategory, HomotopyCategory.map,
  CategoryTheory.Pi.single`: unknown first identifier; no match. Retried with fully
  qualified `CategoryTheory.Functor.mapDerivedCategory,
  CategoryTheory.Equivalence.mapHomologicalComplex`: zero hits.
- msearch LeanSearch: “exact functor of abelian categories induces functor on unbounded
  derived categories”: eight hits, including the actual `Functor.mapDerivedCategory`.
  Its complete source was read and used.
- msearch grep: `clopen.*[Dd]erived|[Dd]erived.*clopen`: zero Mathlib hits.
- rg on `lean/WeilConjectures` and `lean/Sheaf` with that pattern found several related
  coefficient and clopen tensor modules. `ProEtaleFiniteClopenTensorCalculus` states
  a derived decomposition for its commutative coefficient encoding, but does not give
  all the complex/homotopy equivalences and localized module unit/counit normalization
  required by this node. It is therefore not an exact existing match.
- grep for the item id in `lean/WeilConjectures` found no declaration; rg of
  `dag/lean_names_upstream.json` and both source trees for the new namespace and
  declaration name found no clash.

Sources read: `literature/stacks-project/derived.tex`, labels
`lemma-right-derived-exact-functor` (015F) and `definition-unbounded-derived-category`
(05RU), and the full nine-step finite-clopen argument in this DAG node. No statement
correction, dependency repair, or new independent definition node is needed.

Validation: scompile.py confirmed the complete module against the current server
sources in 51.7 seconds. Its two long-line warnings were repaired before preflight.
The prescribed dry run and final delivery are run after this report is prepared.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
