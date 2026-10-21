## Worker report

The module `Sheaf.CategoryTheory.ExactDerivedComposition` states
`CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso` with a single `sorry`.
No definition, dependency interface, or natural-language statement is changed.

Clause-by-clause correspondence:

- The three abelian categories are `C`, `D`, `E` with their respective `Category` and
  `Abelian` instances. Each has independent object, morphism and localization universes
  (`uᵢ`, `vᵢ`, `wᵢ`), and a `HasDerivedCategory.{wᵢ}` instance. Thus no equality of size
  universes and no existence of resolutions is assumed.
- The functors are `F : C ⥤ D` and `G : D ⥤ E`. Additivity is `[F.Additive]` and
  `[G.Additive]`; exactness is precisely the finite-limit and finite-colimit preservation
  instances for each, as the node specifies.
- `C(H)` is Mathlib's `H.mapHomologicalComplex (ComplexShape.up ℤ)`, on all integer-indexed
  cochain complexes. The localizations are `DerivedCategory.Q`, the induced functors
  are `mapDerivedCategory`, and the displayed `a_H` is `mapDerivedCategoryFactors.hom`.
- Existence AND uniqueness of a natural isomorphism, in the stated direction, are expressed
  by `∃! μ : D(F ⋙ G) ≅ D(F) ⋙ D(G), ...`. Lean's functor composition `F ⋙ G` denotes
  the node's mathematical `GF`. The explicit `@mapDerivedCategory` arguments merely supply
  `comp_preservesFiniteLimits F G` and `comp_preservesFiniteColimits F G`; these are existing
  Mathlib proofs of consequences of the hypotheses, not extra hypotheses or new instances.
- `∀ K : CochainComplex C ℤ` expresses the normalization for every unbounded complex.
  Reading `≫` from left to right, its factors are exactly `μ_{QK}`, `D(G)(a_{F,K})`, and
  `a_{G,C(F)K}`. The right-hand side is `a_{GF,K}`. The final `Q.map` of
  `mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))` makes the node's stated termwise identity
  identification explicit. Reading its definition in Mathlib Algebra/Homology/Additive.lean
  shows it is induced by the identity natural transformation of `F ⋙ G`, hence is identity
  in each degree. It is not a new comparison condition.

Dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`, and
  `DerivedCategory.Q`, Mathlib.Algebra.Homology.DerivedCategory.Basic.
- `lem-weil-pbc-exact-functor-derived-factorization`: its recorded Mathlib match
  `CategoryTheory.Functor.mapDerivedCategoryFactors` and `mapDerivedCategory`,
  Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
- The proof dependency `lem-weil-pbc-localization-universal-property` is imported from
  Mathlib.CategoryTheory.Localization.Predicate: `Localization.liftNatIso`,
  `fullyFaithfulWhiskeringLeft`, and `natTrans_ext`. Its full signatures and docstrings were
  read. The docstring carries all four steps of the DAG proof: exactness of the composite,
  the whiskered common factorization, lifting the identity, then cancellation and
  localization extensionality for uniqueness.

Edge cases checked before writing: identity functors, zero functors, zero/acyclic complexes,
complexes with nonzero terms in arbitrarily positive and negative degrees, and independent
size universes. The component formula remains well typed in each case. Abelian categories
are nonempty since they contain zero objects; no nonemptiness restriction is added.
No boundedness, injectivity, enough-injectives, or faithfulness hypothesis appears.

Searches (all performed for this item using the prescribed msearch wrapper):

- LeanFinder: "The functor induced by a composite of two exact functors on unbounded derived
  categories is uniquely isomorphic to the composite and agrees with the localization
  factorizations" returned 8 hits: mapDerivedCategoryFactors, Factorsh, Ext.mapExactFunctor_hom,
  the lifting instance, mapDerivedCategoryFactorsh_hom_app, mapDerivedCategorySingleFunctor,
  mapDerivedCategory, and the shift-commutation instance. None states unique existence.
- Loogle: `CategoryTheory.Functor.mapDerivedCategoryCompIso` returned seven hits in the
  online Mathlib index, including the compositor and its normalization on `Q` objects.
  The pinned local Mathlib does not contain that compositor. The project does contain it.
- LeanSearch: "There is a unique natural isomorphism from the derived functor of a composite
  of exact functors to the composite of their derived functors compatible with localization"
  returned 8 hits including leftDerivedUnique, rightDerivedUnique, their natural-transformation
  composition lemmas, mapDerivedCategorySingleFunctor, isoUniqFunctor and leftDerivedNatIso.
  These are general ingredients, not this full unique normalized compositor statement.
- msearch grep: `mapDerivedCategoryCompIso|mapHomologicalComplexCompIso|natTrans_ext` returned
  25 hits, including the complex-level comparison and localization extensionality.
- Direct rg of project WeilConjectures and Sheaf found the existing compositor and
  normalization `mapDerivedCategoryCompIso_fac` in
  WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor, read at lines 175–216.
  That construction supplies existence and normalization but no uniqueness assertion.
  Searching `∃!.*mapDerivedCategory`, compositor names ending in `unique`, and the proposed
  declaration name found no declaration of the complete statement or name clash.
- The required grep for the blueprint id in WeilConjectures found no match.

The local source Stacks categories.tex, lemma-properties-left-localization (04VG), and the
current blueprint proof of def-sfb-derived-extend-comp-iso were read. The former supplies
functor factorization; the latter asserts composition for exact functors. The natural
transformation enhancement and uniqueness are the explicitly cited Mathlib localization
universal property. There is no statement dispute or correction and no missing notion.

Validation: the prescribed server single-file compiler accepted both sandbox and library
module forms without errors or warnings (1.7 s and 1.9 s respectively).

## Second reading by Q106

No independent worker was started, as the dispatcher's brief prohibits starting agents;
the maintainer performs the independent delivery review. A separate self-check re-read the
node and final signature. It verified each hypothesis and clause listed above, particularly
the `∃!` scope over the complete normalization predicate, the orientation of all four maps,
the explicit identity identification, and the independent universes. No mismatch was found.
