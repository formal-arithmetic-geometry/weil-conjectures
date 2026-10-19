## Worker report

The module `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` states
`CategoryTheory.Functor.exactFunctor_derivedFunctor`, with `sorry` as its entire proof.
No definitions, new nodes, dependency replacements, or statement corrections are needed.

Sources read: `derived.tex`, lemma-right-derived-exact-functor (Tag 015F), parts (2)--(4),
and lemma-bounded-derived (Tag 05RW); `sites-cohomology.tex`, section-base-change-map
(Section 0735), the paragraph before lemma-base-change-map-flat-case. Exactness makes
termwise application invert quasi-isomorphisms, without any resolution hypotheses.
The dual left-derived formulation is the node's explicit dual Kan extension assertion.

Hypothesis and clause correspondence:

- The two arbitrary abelian categories are `A : Type uA`, `B : Type uB`, with independent
  `Category.{vA}`, `Category.{vB}` and `Abelian` instances. The independent
  `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wB}` binders specify the chosen
  localization morphism universes, as in def-weil-abstract-derived-category; these are
  size choices, not enough-injectives or enough-projectives assumptions.
- The exact functor is `F : A ⥤ B` with `F.Additive`, `PreservesFiniteLimits F`,
  `PreservesFiniteColimits F`, exactly the dependency's exactness convention.
- `DerivedCategory.Q` is each cochain localization. The termwise functor is
  `F.mapHomologicalComplex (ComplexShape.up ℤ)`.
- The supplied arbitrary factorization functor is `FD`, not just the canonical
  `F.mapDerivedCategory`. Its comparison `φ : DerivedCategory.Q ⋙ FD ≅
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` has exactly the
  direction in the node (Lean writes composition from left to right).
- Clause (1) is the first two conjuncts: `FD.IsRightDerivedFunctor φ.inv` and
  `FD.IsLeftDerivedFunctor φ.hom`, for cochain quasi-isomorphisms. Mathlib's definitions
  are respectively left and right Kan extension properties along `DerivedCategory.Q`.
- Clause (2) is the existential `Fplus`, with its restriction comparison
  `e : Fplus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ FD`.
  The bounded termwise functor is the existing `F.mapCochainComplexPlus`, and the bounded
  localization is the existing `DerivedCategory.Plus.Q`. The existential `φplus` is
  their factorization comparison. The component equation specifies that it restricts
  the given `φ`, rather than being an unrelated isomorphism: after inclusion,
  `φplus_K` followed by the target quotient-to-derived comparison equals `e` followed
  by `FD` of the source quotient-to-derived comparison followed by `φ_K`.
  The two bounded Kan conjuncts are `Fplus.IsLeftKanExtension φplus.inv` and
  `Fplus.IsRightKanExtension φplus.hom`. These are precisely the node's explicit
  definitions of right/left derived functors, with respect to the bounded cochain
  localization at quasi-isomorphisms.
- The final 'every complex computes' claim is rendered for arbitrary right derived
  pairs `(RF, α)` by `∀ K, IsIso (α.app K)`, not just for the supplied inverse of `φ`.
  The analogous left claim is expressed for arbitrary `(LF, ε)`.
  Both assertions are also stated for bounded pairs, as in the node's last proof step.

The bounded assertions deliberately use the Kan predicates directly. Although Mathlib
provides the localization instance for the composite defining `Plus.Q`, instance search
in the first server compile did not unfold the named `Plus.Q` definition. Using its Kan
universal property avoids introducing an extra localization hypothesis or a duplicate
instance/definition. The equivalence is exactly the `isRightDerivedFunctor_iff_isLeftKanExtension`
and `isLeftDerivedFunctor_iff_isRightKanExtension` definitions, and the node already names
these Kan properties as the intended meaning.

Dependency declarations read and used:

- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`, and
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic` (including its
  localization instance); imported transitively through the public exact-functor module.
- lem-weil-pbc-exact-functor-derived-factorization: its Mathlib match
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, with `mapDerivedCategory` and the
  triangulated/shift compatibility instances, in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. No specialization module is needed.
- def-weil-pbc-bounded-derived-subcategories: its Mathlib match `DerivedCategory.Plus`
  in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, and `Plus.ι`; these are the
  existing full subcategories defined by the standard t-structure's existential lower bound.
- lem-weil-pbc-exact-functor-bounded-below: the recorded
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` and
  `CategoryTheory.Functor.isGE_mapDerivedCategory_obj`, in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
  Their signatures/docstrings and the existing `mapDerivedCategoryPlus` restriction were read.
- Proof dependency lem-weil-pbc-localization-universal-property: `Localization.lift`,
  `fac`, `liftNatTrans`, and `natTrans_ext` in `Mathlib.CategoryTheory.Localization.Predicate`.
- Proof dependency lem-weil-pbc-bounded-below-cochain-localization: `DerivedCategory.Plus.Q`
  in `Mathlib.Algebra.Homology.DerivedCategory.Plus`, and the general composite localization
  instance at lines 234--248 of
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`. The latter is
  imported as a proof dependency; it precedes the enough-injectives hypothesis.
- The existing `mapCochainComplexPlus` and `mapCochainComplexPlusCompι` in
  `Mathlib.Algebra.Homology.CochainComplexPlus` were read; the inclusion comparison is
  definitional. Likewise `HomotopyCategory.Plus.quotientCompιIso` and
  `DerivedCategory.Plus.QhCompιIsoιCompQh` are identity comparisons after unfolding,
  which explains the simpler component equation in the statement.

Edge cases checked: zero functor, zero complex, zero abelian category, complexes with
no lower bound in the unbounded claims, and every integer lower bound in the bounded
claims. No nonzero, connectedness, injectivity, projectivity, or finite-dimensionality
hypothesis occurs. Categories and their localization morphisms use six independent
universes. No bound is fixed globally, so negative bounds and arbitrarily shifted
bounded complexes remain included. `FD` and `φ` are arbitrary, including noncanonical
isomorphic factorization pairs; the restriction comparison and component equation
preserve this generality. There is no hollow definition and no disputed statement.

Searches actually run using `msearch.py NE lem-weil-pbc-exact-functor-derived-functor`:

- leanfinder: 'An exact functor induces both left and right derived functors on unbounded
  and bounded below derived categories'. Eight hits, including `mapDerivedCategory`,
  `mapDerivedCategoryFactors`, derived-functor existence and Ext mapping. None states
  both Kan properties, the arbitrary bounded restriction, and the computation claims.
- loogle: '"isRightDerivedFunctor_of_inverts"'. Two hits:
  `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` and
  `CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts`. These are general
  ingredients, not the whole statement. The dual left declarations were also read.
- leansearch: 'A functor factoring through a localization with an isomorphism is both
  a left and a right Kan extension'. Service unavailable: Internal Server Error;
  recorded as unavailable, not a negative search result.
- grep, CategoryTheory: `isRightDerivedFunctor_of_inverts|isLeftDerivedFunctor_of_inverts`.
  Eleven hits in PointwiseRightDerived, PointwiseLeftDerived and DerivabilityStructure/Derives.
- `rg` in the upstream `WeilConjectures` tree and project `lean/Sheaf` for exact/derived
  terminology, then for `isRightDerivedFunctor_of_inverts` and exact derived names.
  Read upstream RightDerivedFunctor/MapDerivedCategory and PlusExact in full: these
  specialize the right-derived claim to the canonical homotopy factorization and their
  derived-functor comparisons require K-injective resolutions or enough injectives;
  neither states this node's two-sided cochain statement for arbitrary factorization pairs.
- The required upstream node-id grep returned no match. `dag/lean_names_upstream.json`
  contains `mapDerivedCategoryFactors` but no attachment for this item.
- The chosen full declaration name `CategoryTheory.Functor.exactFunctor_derivedFunctor`
  was searched in Mathlib, upstream and `lean/Sheaf`: no existing declaration.

Validation: the final module compiled cleanly using `scompile.py`, on the server,
with nice 19, two threads, and the 60-second per-file limit (reported time 1.2 s).
No local Lean or Lake invocation was run. The sole theorem proof is `sorry`.

## Second reading by NE

I reread the node, its Stacks source (Derived Categories, Tag 015F, parts (2)--(4),
and Tag 05RW for the bounded-below localization), all four statement dependencies,
and the module independently.  The node's objects and hypotheses are rendered as follows:

- Abelian categories `A : Type uA` and `B : Type uB`, with independent category,
  abelian, and `HasDerivedCategory` instances, are the first binders of
  `exactFunctor_derivedFunctor`.
- The exact functor is `F : A ⥤ B` with `[F.Additive]`,
  `[PreservesFiniteLimits F]`, and `[PreservesFiniteColimits F]`; no resolution,
  Noetherian, finiteness, or characteristic hypothesis is added.
- The cochain localization functors are `DerivedCategory.Q`, and the termwise
  functor is `F.mapHomologicalComplex (ComplexShape.up ℤ)`.
- The arbitrary factorization pair is `FD` and
  `φ : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
  DerivedCategory.Q`, with the same direction as the node.
- Clause (1) is rendered by the first two conjuncts,
  `FD.IsRightDerivedFunctor φ.inv ...` and `FD.IsLeftDerivedFunctor φ.hom ...`.
  These are Mathlib's left- and right-Kan formulations of the two derived-functor
  assertions.
- Clause (2) is the existential `Fplus`, restriction comparison `e`, and bounded
  comparison `φplus`.  The displayed component equation states that `φplus` restricts
  the supplied `φ`; the following `IsLeftKanExtension` and `IsRightKanExtension`
  conjuncts are exactly the bounded derived-functor assertions.  The two final
  bounded universal quantifiers express the node's “every bounded-below complex
  computes” consequence.
- The two unbounded universal quantifiers over arbitrary right and left derived
  pairs state the node's final “every complex computes” claim, with `IsIso` at each
  complex.  Quantifier order and comparison directions agree with the node.

Edge cases were checked again: zero categories and zero functors, zero complexes,
complexes with no lower bound, every integer lower bound (including zero and negative
bounds), and arbitrary independent universes.  No excluded empty or characteristic
case is introduced, and no nontriviality or resolution assumption is hidden.

Searches were repeated with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`,
and the first worker's LeanSearch log was checked (service failure, not absence).
Independent LeanFinder query: “Exact functor between abelian categories has invertible
unit and counit for both Kan extensions along derived localization”: eight hits,
including general derivability-structure and Kan-extension equivalence ingredients.
Independent Loogle query `"isLeftDerivedFunctor_of_inverts"`: two hits, the general
left-derived construction and invertibility result, not the complete statement.
An earlier two-string Loogle query was rejected by its parser; it is not negative
evidence.  No existing declaration states this whole theorem.  The dependency
declarations were opened and match the notions used.

No mismatch was found, so no statement or module change was necessary.  The module
compiled with `scompile.py` under the required nice-19, two-thread, 60-second limit;
the only diagnostic is the intentional `sorry` proof.
