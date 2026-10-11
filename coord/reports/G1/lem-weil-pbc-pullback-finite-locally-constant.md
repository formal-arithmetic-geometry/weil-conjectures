## Worker report

Module: `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`.
Declaration: `AlgebraicGeometry.Scheme.pullback_finite_locally_constant`.
This is a statement only, with one `sorry`; no definitions or proofs are added.
The item's node copy changes only `lean`.

Hypothesis and clause matching:
- Schemes T, Y, Y': `{T Y Y' : Scheme.{u}}`, for arbitrary explicit universe u.
- Morphisms g:Y'→Y and f:Y→T: `(g : Y' ⟶ Y) (f : Y ⟶ T)`, with no geometric
  property assumed. The conventions node introduces no separate notion, and records
  the Mathlib Scheme category as the convention to use.
- F an abelian sheaf on the small etale site of T:
  `(F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- h⁻¹ is sheafified presheaf pullback along etale base change:
  `Etale.upperStar AddCommGrpCat.{u + 1} h`. Its source definition is exactly
  `Functor.sheafPullbackConstruction.sheafPullback` along
  `MorphismProperty.Over.pullback @Etale ⊤ h`; it is not un-sheafified restriction.
- f⁻¹F finite locally constant: `hF` is the recorded
  `IsFiniteLocallyConstantEtaleSheafOfSets` applied to its underlying sheaf.
  `sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})`
  forgets abelian structure while preserving the sheaf. The dependency's predicate
  is existence of an etale trivializing cover plus finite stalk sets at every
  algebraically closed geometric point. No finite-generation substitute is used.
- (f∘g)⁻¹F ≅ g⁻¹(f⁻¹F): the first conjunct is `Nonempty` of exactly this
  isomorphism in the category of abelian sheaves; Lean composition is `g ≫ f`.
  This is the node's isomorphism assertion, not an equality of chosen constructions.
- This sheaf is finite locally constant on Y': the second conjunct applies the same
  recorded predicate to the underlying sheaf of the composite pullback.
  Via the first conjunct this also asserts finite local constancy for the iterated
  pullback: the predicate is invariant under sheaf isomorphism, since its two
  clauses are existence of constant restrictions and finiteness of stalk sets.

Dependency declarations read and used:
- `def-weil-pbc-scheme-conventions` is a conventions-only record (`convention: true`),
  explicitly introducing no declaration of its own. Read its statement and record;
  use `AlgebraicGeometry.Scheme`, `Scheme.Hom` and its category instance, defined in
  `Mathlib.AlgebraicGeometry.Scheme` (structure Scheme, structure Hom, Category Scheme).
- `def-weil-pbc-etale-sheaves`: import `Sheaf.AlgebraicGeometry.EtaleSheaves`; use
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantEtaleSheafOfSets`, whose complete
  definition and the definition of `IsLocallyConstantEtaleSheafOfSets` were read.
  The abelian category is the record's existing `CategoryTheory.Sheaf` specialized
  to `AddCommGrpCat`, not a private category. Read `etaleSetPullback` too; abelian
  inverse image uses the same construction in the source's `Etale.upperStar`.
- Read `AlgebraicGeometry.Etale.upperStar` and `Etale.upperStarComp` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (lines 238 and 325).
  Read `CategoryTheory.sheafCompose` in `Mathlib.CategoryTheory.Sites.Whiskering`
  (line 51). These are available through the dependency import.

Source verification: local literature/stacks-project is absent on this machine, so
opened the official source pages https://stacks.math.columbia.edu/tag/095A,
https://stacks.math.columbia.edu/tag/03Q1 and https://stacks.math.columbia.edu/tag/03CB.
095A gives preservation of local constancy, 03Q1 (3) gives stalk identification,
and 03CB gives composition of inverse images. The module docstring contains all
three steps of the node's proof and names every non-elementary dependency used there.

Edge cases checked before writing:
- Empty schemes and empty trivializing covers are allowed by the recorded Cover
  definition; no Nonempty or connectedness hypothesis is added.
- The zero sheaf is allowed, with singleton underlying stalks, hence finite.
- Infinite abelian stalks, including finitely generated infinite groups, do not meet
  the finite-set hypothesis. This checks why the source's finite-generation predicate
  cannot replace the recorded set-valued predicate.
- g and f may be arbitrary, identities, closed immersions, or non-surjective maps;
  no etaleness/properness/Noetherian condition is required.
- No field characteristic, coefficient-ring restriction, or chosen stalk point is
  introduced. The source/dependency convention uses scheme universe u and abelian
  carriers in u+1, with the recorded geometric-point quantification unchanged.

Searches actually run:
- msearch LeanSearch: `Pullback of finite locally constant etale sheaves preserves
  finite local constancy`: unavailable, Internal Server Error; not a negative result.
- msearch LeanFinder: `inverse image preserves finite locally constant sheaves`:
  eight results, CompHausLike.LocallyConstant functors and LightCondensed declarations;
  none about small etale sheaves.
- msearch Loogle: `IsFiniteLocallyConstantSheaf`: no hits, unknown identifier.
- msearch Mathlib grep: `IsFiniteLocallyConstantSheaf|upperStarComp`: no hits.
- rg of source WeilConjectures for `IsFiniteLocallyConstant|upperStar|` and the item
  id found the ConstructibleSheaf/Pullback source lemmas and six-functor operations;
  the item-id search itself had no hits. Also searched the exact final declaration
  name across Mathlib, WeilConjectures and lean/Sheaf: no collision.
- rg of lean/Sheaf for `IsFiniteLocallyConstantSheaf|pullback_finite_locally` found
  module-valued lisse sheaf files and finite-etale pushforward, not this statement.
- `tools/lean_names_upstream.py show lem-weil-pbc-pullback-finite-locally-constant`
  supplied no associated declaration.
- Read the source `Scheme.IsFiniteLocallyConstantSheaf.upperStar` in
  `WeilConjectures.ConstructibleSheaf.Pullback` (line 164). It preserves finitely
  generated stalk objects, whereas our item requires finite underlying stalk sets;
  it also does not state the item's two-morphism composition clause. Therefore it
  cannot be recorded as an exact existing statement. The generic `Etale.upperStarComp`
  supplies only the composition clause. No new notion or dependency module is needed.

No statement correction or STATEMENT-DISPUTED issue.

## Second reading by G1

I reopened the node copy and the complete Lean declaration. The node's objects,
hypotheses, and conclusion render as follows:

- Schemes (T,Y,Y') are the explicit binders `{T Y Y' : Scheme.{u}}`; this is
  the Mathlib scheme category required by `def-weil-pbc-scheme-conventions`.
- Morphisms (g:Y'\to Y) and (f:Y\to T) are `(g : Y' ⟶ Y) (f : Y ⟶ T)`;
  no extra etale, separated, finite, Noetherian, or characteristic hypothesis is
  present.
- The abelian sheaf (F) on (T_{\mathrm{Et}}) is
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The hypothesis that (f^{-1}F) is finite locally constant is exactly
  `hF : IsFiniteLocallyConstantEtaleSheafOfSets ((sheafCompose
  Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
  ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F))`.
- The first conclusion clause is `Nonempty` of the isomorphism between
  `Etale.upperStar ... (g ≫ f)` and the iterated `g` then `f` upper stars,
  matching ((f\circ g)^{-1}F\cong g^{-1}(f^{-1}F)).
- The second clause applies the same recorded predicate to the underlying sheaf
  of the composite pullback on `Y'`, exactly the node's finite-local-constancy
  conclusion.

The declaration uses the dependency predicate and the recorded `Etale.upperStar`
construction directly; no private replacement notion or additional instance is
introduced. I checked empty schemes and covers, the zero sheaf, arbitrary and
identity/non-surjective morphisms, infinite versus finite stalks, and all
characteristics. The universe is shared by the schemes and the coefficient
category is at `u + 1`, so no case is excluded. Searches (LeanSearch,
LeanFinder/Loogle, Mathlib/source/project `rg`, and upstream-name lookup) found
no exact existing declaration; the similarly named source result concerns finite
generation and is not this statement. No mismatch was found and no file or node
content required repair.
