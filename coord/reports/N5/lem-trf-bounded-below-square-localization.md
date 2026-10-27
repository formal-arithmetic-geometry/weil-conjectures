## Worker report

The module `Sheaf.CategoryTheory.BoundedBelowSquareLocalization` states
`CategoryTheory.existsUnique_boundedBelowSquareLocalization`. It contains one theorem,
with proof `sorry`, and no definitions or additional nodes. The item node changes only
in `lean`. There is no statement correction and no disputed statement.

Sources read: the complete item and its four proof steps; each statement-dependency
node and its recorded declaration; the source `PlusAdjunction.lean`, especially
`Adjunction.derivedPlus_mateEquiv_app_fac` and its `hθ`; and the construction
`CategoryTheory.boundedBelowDerivedSquare` in `BoundedBelowDerivedMateModel.lean`.
The latter constructs a square but does not assert this node's uniqueness or the
factorization for that construction, so it is not an exact existing statement.
The compact-object example's Sheaf module is withdrawn; its node now points to
`WeilConjectures.CategoryTheory.CompactObject`, which was also opened for conventions.

Hypotheses and objects, matched with Lean:

- The four abelian categories are `A`, `B`, `A'`, `B'`, with explicit `Type`,
  `Category`, and `Abelian` binders. All object, morphism, and derived-localization
  universes are explicitly declared. They may be different levels; their maximum
  supplies the common bound of the size convention. No equality of universes is added.
- Their derived categories use the four `HasDerivedCategory` binders and Mathlib's
  `DerivedCategory`; the bounded-below source is `DerivedCategory.Plus B`.
- The four functors are exactly `L : B ⥤ A`, `L' : B' ⥤ A'`, `G : B ⥤ B'`, and
  `H : A ⥤ A'`. Each has `Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits` binders, exactly the dependency's encoding of exactness.
- `E`, `E'`, `T`, `S` are respectively `L.mapDerivedCategory`,
  `L'.mapDerivedCategory`, `G.mapDerivedCategory`, `H.mapDerivedCategory`.
- `σ : G ⋙ L' ⟶ L ⋙ H` has the direction L'G → HL: Lean writes functor
  composition in traversal order. There is no `IsIso σ` assumption.
- `N : HomotopyCategory.Plus B` ranges over all K⁺(B). Mathlib's
  `HomotopyCategory.plus` is the strict image of bounded-below cochain complexes
  under the homotopy quotient; its full subcategory has exactly those complexes
  as objects and chain maps modulo homotopy as morphisms. `N.obj` is its image
  in the ambient homotopy category, not an arbitrary unbounded replacement.
- `qN` is `DerivedCategory.Plus.Qh.obj N`. After `DerivedCategory.Plus.ι`,
  its ambient derived object is definitionally `DerivedCategory.Qh.obj N.obj`;
  the canonical comparison `QhCompιIsoιCompQh` is `Iso.refl`.

Conclusion and formulas, matched with Lean:

- `∃! θ` quantifies natural transformations from
  `DerivedCategory.Plus.ι ⋙ (G.mapDerivedCategory ⋙ L'.mapDerivedCategory)` to
  `DerivedCategory.Plus.ι ⋙ (L.mapDerivedCategory ⋙ H.mapDerivedCategory)`.
  These have source D⁺(B) and target D(A'), exactly the restrictions of E'T and SE.
  Uniqueness is therefore asserted only on the specified bounded-below source.
- The first two factors on the right of the first equality are A_N:
  `L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N.obj)`
  followed by `L'.mapDerivedCategoryFactorsh.hom.app (K(G) N.obj)`.
- The two factors after `θ.app (DerivedCategory.Plus.Qh.obj N)` on the left
  are B_N: `H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N.obj)`
  followed by `H.mapDerivedCategoryFactorsh.hom.app (K(L) N.obj)`.
  `mapDerivedCategoryFactorsh` is precisely the canonical homotopy factorization
  of the dependency's cochain comparison `mapDerivedCategoryFactors`.
- The mapped morphism in each equality is σ^K_N: first the `hom` component of
  `mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L'))`, then
  `(NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app N.obj`, then the
  `inv` component of `mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H))`.
  These canonical composition identifications insert no extra choice or assumption.
  `DerivedCategory.Qh.map` of this composite is q(σ^K_N), viewed in D(A').
- Composition `f ≫ g` means g after f. Thus the first equality is precisely
  B_N ∘ θ_qN = q(σ^K_N) ∘ A_N.
- The second equality is precisely θ_qN = B_N⁻¹ ∘ q(σ^K_N) ∘ A_N.
  Its final two factors are `φ_H.inv` followed by `S.map (φ_L.inv)`, the
  inverse of B_N in the correct reverse order.
- Both equalities appear under the universal quantifier over N. Including the
  component formula in the unique-existence predicate does not weaken uniqueness
  for the first equality: B_N is an isomorphism, and cancellation shows every
  transformation satisfying the square automatically satisfies the formula.
- This is the canonical termwise-derived D(σ): the localized termwise morphism
  conjugated by the exact-functor comparisons. There is no separately chosen
  transformation and no assumption selecting arbitrary comparison isomorphisms.
- There is no enough-injectives binder on any category; σ may be noninvertible.

Dependency declarations used, with files opened:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (class and its docstring).
- `def-weil-size-convention`: metatheoretic convention, no declaration; realized
  by explicit universe levels and `HasDerivedCategory` binders.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus` and
  `DerivedCategory.Plus.ι`, `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `lem-weil-pbc-exact-functor-derived-factorization`: `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`, `Functor.mapDerivedCategoryFactorsh`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The full signatures and
  the relation `mapDerivedCategoryFactorsh_hom_app` were read.
- Bounded-below homotopy objects and the canonical q are from
  `Mathlib.Algebra.Homology.HomotopyCategory.Plus` and
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`; the latter's Qh localization
  and the inclusion comparison were read. `Functor.mapHomotopyCategoryCompIso`
  and `NatTrans.mapHomotopyCategory` are from Mathlib's `HomotopyCategory` module.
- Proof dependency `lem-weil-pbc-bounded-below-cochain-localization` uses the
  above Plus module and the composite-localization instance in
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`,
  explicitly before its enough-injectives section; imported for the future proof.
- Proof dependency `lem-weil-pbc-localization-universal-property` uses
  `Localization.liftNatTrans`, `liftNatTrans_app`, `natTrans_ext`, and
  `fullyFaithfulWhiskeringLeft` in `Mathlib.CategoryTheory.Localization.Predicate`,
  whose signatures and docstrings were read; imported for the future proof.

Edge cases checked mathematically before writing: σ = 0 forces the zero derived
square by invertibility of B_N; σ = identity with coincident composites gives the
comparison-conjugated identity, with no cancellability of σ used. A noninvertible
σ has the same well-typed formula. For zero complexes and zero abelian categories
all maps are the unique zero maps and uniqueness still holds. The lower bound is
existential within K⁺ and may be any integer, including negative bounds. General
abelian categories without enough injectives are permitted because localization,
not an injective replacement, supplies the descent. No finite, nonempty, or
positivity restriction is introduced. The formula uses the ambient full inclusion,
so it makes no implicit assumption that a target comparison is literally a map
in a different full subcategory.

Searches actually run using `batch2/msearch.py N5 lem-trf-bounded-below-square-localization`:

- LeanFinder: "An arbitrary natural transformation between composites of exact additive
  functors descends uniquely to bounded below derived categories with canonical
  localization comparisons". Eight hits: principally `mapDerivedCategoryFactors`,
  `mapDerivedCategoryFactorsh`, and their app lemmas, plus right/left-derived
  composition facts. These supply ingredients, not this statement.
- Loogle: "CategoryTheory.Functor.mapDerivedCategoryFactorsh,
  CategoryTheory.Localization.liftNatTrans". Zero hits.
- Grep on Mathlib `CategoryTheory`: `mapDerivedCategoryFactorsh|liftNatTrans_app|natTrans_ext`.
  Twenty-five hits include `Localization.Predicate` lines 286, 332, and uses of
  these general lemmas in localization modules; none state this square theorem.
- LeanSearch: "An exact natural square descends uniquely to bounded below derived
  categories". Eight hits, including `DerivedCategory.right_fac_of_isStrictlyLE`,
  `HasDerivedCategory.standard`, and unrelated square lemmas. No exact match.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `boundedBelowDerivedSquare|bounded.below.*square|lem-trf-bounded-below-square-localization|mapDerivedCategoryFactorsh`
  located the existing square construction, arbitrary exact-derived pasting, and
  many uses of the individual comparison. The relevant source modules were opened;
  the unbounded pasting framework is not the asserted D⁺ existence/uniqueness theorem.
- Narrow direct `rg` for `boundedBelowDerivedSquare|lem-trf-bounded-below-square-localization|square_localization`
  found the parent construction and specialized geometric square statements.
- Name-clash search for `existsUnique_boundedBelowSquareLocalization` in Mathlib,
  upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no match. Searches for
  `existsUnique.*[Ss]quare|[Ss]quare.*existsUnique|boundedBelowSquareLocalization`
  in Mathlib derived-category and localization directories also found no match.

Validation: prescribed `scompile.py` compiled the sandbox and library forms cleanly
in 1.5 s and 1.4 s. Every variable and universe is explicit, and the only postponed
proof is the named theorem above. Dry-run and delivery results are appended below.

## Second reading by N5

I reopened the node and the final Lean file for a separate reading pass, without
starting another agent, as the dispatcher brief requires. The maintainer supplies
the independent review. In this pass I checked all four functor directions and all
four exactness hypotheses; the arbitrary σ binder; the K⁺ quantifier; and that θ
is between the *unbounded composites restricted to D⁺*, with target D(A'), rather
than claiming uniqueness on all of D(B). I read the two comparison factors in A_N
and B_N against their types. I checked the two homotopy compositor orientations,
then the reverse order of the two inverse factors in B_N⁻¹. The first equality
matches the square and the second matches the component formula. The extra formula
inside `∃!` is equivalent to the square alone by cancellation of B_N, so it does
not restrict or enlarge the class of solutions. No injective or IsIso σ hypothesis
is present, and no dependency notion was copied. This pass found no mismatch and
required no change. There are no new nodes or repaired dependency modules to read.

Delivery validation: `deliver2.py N5 lem-trf-bounded-below-square-localization --no-push`
printed `OK (dry run)` for commit `f48cc129d60`: preflight and per-file compilation
passed. A final direct `grep -rn` for the item id in `lean/WeilConjectures` found
no upstream attachment. Stacks Tags 014X, 015F and 05RW(1) were additionally read
in the local `literature/stacks-project/derived.tex` to check the cited argument.
