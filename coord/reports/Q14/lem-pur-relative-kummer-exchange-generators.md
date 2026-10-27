## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators` states all four
clauses of lem-pur-relative-kummer-exchange-generators. Every theorem has proof `sorry`.
No mathematical statement, dependency list, or proof plan is changed.

Hypotheses and clauses:

* `A : Type (u + 1)` and `[CommRing A]` are the arbitrary constant coefficient ring,
  in the established six-functor size convention; `Scheme.{u}` supplies all four schemes.
* `sq : ChosenCartesianSquare v a' a g` supplies the cartesian square and its chosen
  identification, including the projection equations and commutativity.
* `L₀ : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)` is the given sheaf L.
  `DerivedCategory.singleFunctor _ 0` puts it in degree zero. `L(upperStar ... a)`
  represents a*L; it is canonically the ordinary sheaf pullback placed in degree zero
  through `singleFunctorCompLeftDerivedUpperStarIso`. Applying `L(upperStar ... v)`
  gives F'. `derivedSquareUpperStarIso ... sq.toCommSq` is exactly the identification
  with a'^*g^*L. No sheaf or derived category is replaced by a model category.
* The map b is always the component of the existing `derivedBaseChangeMap` in the
  module category. This is the module exchange retained by the recorded dependency
  `BaseChangeMapAbelianAndSets`; no arbitrary map is a parameter.
* `relativeKummerExchange_unit` is the actual derived unit identity. Its right side
  writes out Ra'_*theta_L instead of treating the square identification as an equality
  of objects. Its left side is g*eta_a followed by b.
* Global H^q classes are represented by morphisms from the degree-zero constant free
  rank-one module sheaf to F[q]. This is the ordinary derived-Hom realization of
  module sheaf cohomology. It is equivalent to the resolution/global-section definition:
  Hom(A_X,-) is evaluation of global sections and injective resolutions compute its
  derived functors. This does not assert that forgetting module injectives preserves
  injectivity. The class ranges over every such morphism; q is any natural number,
  including zero.
* `kummerExchangeClassPullback` applies the actual exact derived inverse image to
  the class and uses only the constant-sheaf comparison, the single comparison, and
  the shift comparison. It is the module realization of the cohomology pullback
  recorded as `Etale.cohomologyMap` on underlying abelian cohomology. No comparison
  is obtained by choosing an unspecified isomorphism.
* A global section of a module sheaf G is represented as a sheaf morphism A_B → G,
  equivalently its value on 1. `kummerExchangeEdge` constructs this morphism by the
  derived adjunction, H^0, and H^0(K[q]) ≅ H^q(K). This is the Leray edge section,
  which on an injective representative takes a global cocycle to its class in the
  direct-image cohomology sheaf, as in Stacks 072W.
* `kummerExchangeSectionPullback` is pullback of this actual section, precomposed
  with the canonical constant-sheaf identification. `kummerExchangeHigherMap`
  is H^q(b) precomposed with the exact inverse-image homology comparison.
  `relativeKummerExchange_edge` asserts their composite equals the edge of the actual
  pulled-back class. Equality of these sheaf morphisms is precisely equality of the
  sections in the node, with the actual module-derived exchange.
* `relativeKummerExchange_generators` assumes `h₀` and `h₀'`, invertibility of H^0
  of the two derived units. Their sources canonically identify with L and g*L by
  exact inverse image and the single/homology comparisons. The square comparison
  identifies the second unit's target with the target of b.
* `hvan` quantifies over all integer degrees different from 0 and 1 and requires
  `IsZero` for the cohomology sheaves of both direct images, namely
  `kummerExchangeImage` and `kummerExchangeTarget`. The latter uses F'=v*F explicitly.
* `x` is any global degree-one class; `hx` requires its actual edge morphism A_B →
  R^1a_*F to be an isomorphism. `hx'` requires precisely the edge of the pulled-back
  class to be an isomorphism over B'. The conclusion is `IsIso` of the specified b.
* `relativeKummerExchange_degreeZero` assumes the same degree-zero units and vanishing
  in every integer degree except zero. It concludes `IsIso b` without a degree-one
  class or generator hypothesis.
* There is no finite-type, quasi-compactness, properness, torsion, nonzero-ring,
  connectedness or nonemptiness hypothesis on g or on any scheme.

Dependency declarations used:

* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `Etale.DerivedCategoryModule`.
* `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded etale sheaf framework;
  `CategoryTheory.Sheaf` with `ModuleCat` is the six-functor encoding of module sheaves.
* `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets` publicly retains
  `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `Etale.derivedBaseChangeMap`, `Etale.derivedSquareUpperStarIso`.
* `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `derivedUpperStarLowerStarAdjunction`, `singleFunctorCompLeftDerivedUpperStarIso`,
  `leftDerivedUpperStarHomologyFunctorIso`; `UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`; `Scheme.upperStarConstantSheafIso` is reused as constructed.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, its shift comparison; `FullyFaithful`:
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`.
* `Mathlib.CategoryTheory.Triangulated.Adjunction`: canonical adjoint shift construction.
  `kummerExchangeUpperCommShift` and `kummerExchangeLowerCommShift` instantiate the
  existing canonical constructions on the named functor abbreviations, exactly as
  the definitions in Etale.Derived.Shift; that large module is not imported.

The module imports the recorded proof modules non-publicly, including exact inverse
image, module/abelian exchange and direct-image comparisons, cohomology forgetting,
commutative exchange charts, the square comparison and the Plus isomorphism criterion.
The mathlib proof leaves `Functor.homologyFunctorIso`, `mateEquiv`, `unit_mateEquiv`
and `DerivedCategory.Plus.isIso_iff` are supplied by their defining modules.

Sources read: the current blueprint proof of prop-pur-gm-relative-kummer, Step 3,
and the full resolution arguments in sites-cohomology.tex at labels
lemma-base-change-map-flat-case (0736) and lemma-higher-direct-images (072W).
The helper definitions belong to this node's specified maps and sections, have real
construction data, and are listed in lean.declarations. No independent new notion
or dependency module is introduced.

Edge cases checked: zero ring and zero sheaves are admitted (the isomorphism criterion
then has its usual zero-object interpretation); empty schemes are admitted; q=0 is
included in the edge identity; negative degrees are included in both vanishing conditions;
identity squares and arbitrary g require no special assumptions. The two-degree criterion
requires a global degree-one class exactly as the node does; the degree-zero variant
has no such binder. Universes follow the recorded module-site convention and impose
no equality on site object and morphism universes.

Searches for an existing statement:

* msearch.py leanfinder, query `Derived etale exchange preserves adjunction units and
  global cohomology edge sections and detects invertibility from generators`: eight
  hits, all about etale ring algebras/differentials, no matching statement.
* msearch.py loogle, query `"baseChange", "cohomology"`: zero hits.
* msearch.py grep, query `exchange.*(edge|generator)|edge.*(baseChange|exchange)`:
  zero Mathlib hits.
* rg in lean/WeilConjectures and lean/Sheaf for edge/Edge and generator constructions:
  found `derivedBaseChangeMap_app_homEquiv` in KummerGenerator, which supplies a
  general adjunction compatibility but does not state the degreewise edge identity
  and both isomorphism criteria. These existing functors and comparisons are reused.
* rg in both roots for this blueprint node id: no matching module.
* rg in both roots and Mathlib for every proposed kummerExchange/relativeKummerExchange
  declaration name: no collision.

No statement dispute or node correction was needed.

The named functors `kummerExchangeUpper` and `kummerExchangeLower` are definitions
whose bodies are exactly the recorded L(upperStar) and R(lowerStar);
`kummerExchangeAdjunction` and `kummerExchangeArrow` likewise only specialize the
existing adjunction and actual exchange. They avoid repeated expansion of large
implicit functor arguments during elaboration. No second functor construction or
mathematical notion is supplied. All helper data are explicit terms.

## Second reading by Q14

Self-check by the author (dispatcher brief prohibits starting another agent; the
maintainer supplies the independent review). Read the node and the final file side
by side: the cartesian square and arbitrary constant ring match; L is in degree
zero; F and F' use canonical exact inverse images; the unit identity includes the
square isomorphism rather than suppressing a transport. The edge identity ranges
over every natural degree and every derived-Hom global class; both sides are
morphisms from the constant rank-one sheaf, hence equality of the actual sections.
The generator criterion contains both invertible degree-zero units, both integer
vanishing conditions, and the actual global class and its pullback. The degree-zero
criterion has no degree-one class. No geometric finiteness assumptions were added.
The four theorem proofs are entirely sorry; all definitions contain real canonical
constructions. No statement correction or dependency repair was made.
