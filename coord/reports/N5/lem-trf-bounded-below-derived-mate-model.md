## Worker report

The module `Sheaf.CategoryTheory.BoundedBelowDerivedMateModel` constructs
`CategoryTheory.boundedBelowDerivedSquare` and states
`CategoryTheory.Adjunction.boundedBelowDerivedMateModel`. The theorem proof is `sorry`;
the square has real data, obtained by the preimage operation of
`Localization.fullyFaithfulWhiskeringLeft`. There are no new nodes, dependency repairs,
or statement corrections. No repair note exists for this item.

The node's hypotheses and clauses are rendered as follows:

- The four abelian categories are A, B, A', B', with explicitly bound object and morphism
  universes, `Category` and `Abelian` instances. The separately named universe levels allow
  arbitrary categories within the common ambient bound, without imposing accidental
  equalities of object, morphism, or localization sizes.
- The derived localizations are the four `HasDerivedCategory.{w...}` instances; the
  bounded-below categories are `DerivedCategory.Plus`. Localization from bounded-below
  homotopy complexes is `DerivedCategory.Plus.Qh`.
- Enough injectives are assumed exactly for A and A', as `EnoughInjectives A` and
  `EnoughInjectives A'`. There is no such assumption on B or B'. Mathlib's class means
  every object has a monomorphism into an injective object.
- L : B ⥤ A, R : A ⥤ B, L' : B' ⥤ A', R' : A' ⥤ B' are additive, and the given
  adjunctions are `adj : L ⊣ R` and `adj' : L' ⊣ R'`. Exactness of L and L' is precisely
  preservation of finite limits and finite colimits.
- G : B ⥤ B' and H : A ⥤ A' are additive and preserve finite limits and finite colimits,
  expressing exactly their stipulated exactness. No preservation of injectives by H
  is assumed or used in constructing the square.
- C(F) on homotopy complexes is `F.mapHomotopyCategoryPlus`; exact descent D(F) is
  `F.mapDerivedCategoryPlus`. The canonical identifications are
  `F.mapDerivedCategoryPlusFactorsh`. These are the bounded-below restrictions of the
  recorded exact-functor derived factorization, not separately chosen identifications.
- The canonical derived adjunctions are literally `adj.derivedPlus` and
  `adj'.derivedPlus`. The comparisons α and α' are literally
  `R.rightDerivedFunctorPlusUnit` and `R'.rightDerivedFunctorPlusUnit`.
- An arbitrary natural transformation σ is `σ : TwoSquare G L L' H`, which has underlying
  transformation G ⋙ L' ⟶ L ⋙ H. There is no `IsIso σ` or isomorphism parameter.
  Its ordinary mate b is `(mateEquiv adj adj' σ).natTrans`.
- D(σ) is constructed as `boundedBelowDerivedSquare σ`. Precompose the source derived
  composite with Qh, apply φ_G followed by φ_L', then the localized termwise σ,
  then φ_H inverse followed by φ_L inverse. The explicit
  `mapHomotopyCategoryPlusCompIso (Iso.refl ...)` maps identify termwise composites.
  Fully faithful precomposition supplies the unique derived transformation with those
  components. This is a construction by localization, not a hypothesized arbitrary map.
- The derived mate b^D is literally
  `mateEquiv adj.derivedPlus adj'.derivedPlus (boundedBelowDerivedSquare σ)`.
- P is any `HomotopyCategory.Plus A`. Every bounded-below complex has such a homotopy
  image, and conversely Mathlib's full subcategory consists of such images. Thus this
  introduces neither an injectivity restriction nor a boundedness restriction beyond
  bounded below.
- Lean's left-to-right composition `≫` reverses the displayed functional composition.
  The left side is `D(G)(α_P) ≫ b^D_qP`. The right side is
  `φ_G,RP ≫ q(K(b)_P) ≫ α'_K(H)P ≫ R'^+(φ_H,P⁻¹)`.
  These initial and final φ factors are exactly the canonical localization
  identifications suppressed in the node's displayed equation. Multiplying by
  φ_G inverse on the left and R'^+(φ_H) on the right gives verbatim the precise
  equation in proof step 7 of the DAG node. No comparison unit is inverted.

The declaration docstring carries all seven proof steps: termwise descent; canonical
adjunction normalization; the localization preimage square; mate expansion and
naturality; the counit calculation; the primed unit calculation and comparison
naturality; and the degreewise ordinary mate calculation. The construction helper is
part of this node's D(σ), recorded in `lean.declarations`, as authorized in the brief.
There is no independent missing notion requiring a definition node.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- The size-convention node has no declaration, intentionally; the explicit universes
  and `HasDerivedCategory` binders implement it.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization Q.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.Plus`;
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`: `DerivedCategory.Plus.Qh`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`,
  `EnoughInjectives`, `InjectivePresentation`; also read `InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`;
  its bounded-below restrictions are the existing declarations
  `Functor.mapDerivedCategoryPlus` and `Functor.mapDerivedCategoryPlusFactorsh` in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus`, `Functor.rightDerivedFunctorPlusUnit`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus`, `derivedPlus_unit_app_fac`, `derivedPlus_counit_app_fac`.
  These are the three existing declarations recorded by the derived-adjunction
  dependency (its audit supplies the module). Its record is usable without repair.
- Proof dependencies are supplied by the imports above: the exact-functor module;
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, including
  `Adjunction.mapHomotopyCategory` and `mapHomotopyCategoryPlus`; and
  `Mathlib.CategoryTheory.Localization.Predicate`, including
  `Localization.fullyFaithfulWhiskeringLeft`, `liftNatTrans`, `natTrans_ext`.
  Their full relevant signatures and docstrings were read.

Sources read: the seven DAG proof steps; the whole mate theorem and its parameter
section in PlusAdjunction.lean; its derivedPlus construction and unit/counit formulas;
and Stacks sites-cohomology.tex, remark-base-change (Tag 07A7), whose map is the
counit transpose. This preserves that normalization.

Edge cases checked before writing: zero complex (all arrows are zero-object arrows);
zero transformation σ (the localization and mate constructions remain defined);
identity squares/identity adjunctions; arbitrary integer lower bounds (no degree-zero
normalization or nonnegative restriction); H sending an injective to a noninjective
object (the right comparison unit at H(P) is never inverted); and unrelated category
and localization universes (all are explicit). Empty categories are not abelian because
an abelian category has a zero object, so no extra nonemptiness assumption is needed.
No statement is disputed.

Searches actually run:

- msearch.py leanfinder: "Bounded below derived adjunction mate computed by underived
  mate and right derived comparison units" returned 8 hits on general derived units
  and counits, not the unconditional construction and mate statement here.
- msearch.py loogle: "CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac,
  NatTrans.mapDerivedCategoryPlus" returned 0 hits, reporting the upstream name unknown
  in its Mathlib index. This is not evidence that the upstream declaration is absent.
- msearch.py grep: "mapDerivedCategoryPlus|mateEquiv" in
  Algebra/Homology/DerivedCategory returned 0 hits.
- msearch.py leansearch: "Derived mate of an arbitrary square of exact functors on
  bounded below derived categories is the underived mate followed by comparison units"
  returned 8 hits including general derived adjunction formulas, mateEquiv, and
  mapDerivedCategory; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf found the upstream
  `derivedPlus_mateEquiv_app_fac`. Its additional θ and hθ inputs do not construct D(σ),
  so the full item is not an existing-declaration match. This delivery fills precisely
  that interface gap and reuses its canonical adjunctions and comparison maps.
- rg read `Sheaf.CategoryTheory.DerivedExactSquare`: its
  `Functor.mapDerivedCategoryPlusSquareIso` takes an isomorphism, so does not handle the
  node's noninvertible σ. `Sheaf.CategoryTheory.DerivedExactMate` is unbounded and
  requires K-injective resolutions, so it is not the node's enough-injectives theorem.
- rg for the two proposed names in Mathlib/upstream/project and
  dag/lean_names_upstream.json found no existing declarations. The requested
  grep for the blueprint ID in lean/WeilConjectures found no occurrences.

Validation: scompile.py compiled both the sandbox and named library module cleanly.
The first compile exposed that the termwise composite functors need their canonical
composition isomorphisms; these were inserted in the real construction. The next
compile passed with no errors or warnings. `autoImplicit false` is set, every universe
and variable is bound, and all Lean lines are at most 100 characters.

## Second reading by N5

This is a separate second pass by the same dispatcher worker, not an independent
agent review: the dispatcher's explicit instruction prohibits starting other agents.
The maintainer's independent review remains the delivery review.

Re-read the node against the final module. Both adjunctions retain their specified
units/counits via derivedPlus, and only A/A' have enough-injectives assumptions.
All four exact functors retain both finite-limit and finite-colimit hypotheses;
R/R' require only additivity. The derived square is constructed for an arbitrary
TwoSquare, not an isomorphism. Following its preimage expression from left to right
checks the orientation: φ_G and φ_L' precede qσ, whereas φ_H inverse and φ_L inverse
follow it. Explicit homotopy composition isomorphisms inserted after the first compile
supply precisely the canonical identity termwise comparisons. The theorem's mate is
of this constructed square, so it has no extra hθ assumption. The two endpoint
comparisons in the conclusion agree with proof step 7. P is arbitrary bounded below,
and the final α' at H(P) is used as a morphism, which preserves the noninjective case.
No hypothesis, conclusion, definition data, source correction, or additional theorem
was silently introduced. No further change was needed in this second pass.
