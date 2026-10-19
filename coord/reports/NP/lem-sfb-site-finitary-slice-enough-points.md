## Worker report

The module `Sheaf.CategoryTheory.Sites.FinitarySliceEnoughPoints` states
`CategoryTheory.finitarySlice_enoughPoints`, with its only proof `by sorry`.
It introduces no definitions and changes only the item's `lean` record.
The statement is Stacks Sites, Lemma 0DW0, `lemma-criterion-points`, in
Section 00YN, read directly in `literature/stacks-project/sites.tex`.
The module docstring gives all four steps of the node's proof.

Hypothesis and conclusion correspondence:

- A small site in the fixed size convention: `{C : Type u} [Category.{v} C]`,
  `(J : Precoverage C) (hJ : J.IsSiteForCoverings)`. Both objects and arrows
  form sets; no global finite limits or pullbacks in C are imposed. This uses
  exactly the recorded site predicate, with composition by covering presieves
  and existence only of covering pullbacks.
- Fixed universe: sheaf values, the covering index, and the output point index
  are in `Type (max u v w)`, which contains objects and arrows of the site.
  The object and arrow universes remain independent. This includes sites with
  object universe t+1 and arrow universe t. The extra w allows larger values.
- The set-indexed objects are `(I : Type (max u v w)) (U : I → C)`.
- The sheaf h_U is
  `(presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
    (uliftYoneda.{max u w}.obj (U i))`.
  The lifted Yoneda presheaf has exactly the hom sets as sections, transported
  into the value universe by ULift. Its sheafification is the recorded
  sheafification, not an assumption that representables are sheaves.
- The coproduct is the categorical coproduct `∐ fun i : I => ...` in
  `Sheaf J.toGrothendieck (Type (max u v w))`. The unique arrow to the
  terminal sheaf is `terminal.from`; its being an epimorphism is `hcover`.
  All existence instances for this expression are inferred from Mathlib,
  without additional hypotheses.
- Each localized category is `Over (U i)`. The hypothesis
  `hlimits : ∀ i : I, HasFiniteLimits (Over (U i))` says exactly that every
  such slice has finite limits, including its terminal object.
- Its actual covering families are represented by the Mathlib precoverage
  `J.comap (Over.forget (U i))`. By the definition of `Precoverage.comap`, a
  presieve is a covering precisely when its image under forgetful is an
  actual J-cover. This is the localized-site dependency's definition, whose
  Grothendieck topology is `J.toGrothendieck.over (U i)`. No topology on the
  slice is chosen freely, and no subcanonical hypothesis is used.
- Every covering family: `hfinite` quantifies over each i, slice object X,
  index A, family V and arrows f, and assumes membership of
  `Presieve.ofArrows V f` in that localized precoverage.
- A finite covering refinement: it produces a type K with `Finite K`,
  objects W and arrows g covering the same X, together with `r : K → A`.
  The clause `∀ k, ∃ q : W k ⟶ V (r k), q ≫ f (r k) = g k` says that each
  new arrow factors through a specified original arrow over X. Arrows and
  factorizations are all in the slice. A need not be finite and this does
  not replace refinement by the stronger requirement of a finite subcover.
  Taking A in `Type (max u v)` represents every covering presieve; any
  larger presentation of the same presieve reduces to this one, and the
  finite refinement lifts back by choosing representatives of its finitely
  many arrows. Thus this index convention loses no covering families.
- A set-indexed family of points: the conclusion existentially quantifies
  `ι : Type (max u v w)` and
  `p : ι → GeometricMorphism (Type (max u v w))
    (Sheaf J.toGrothendieck (Type (max u v w)))`.
  The recorded geometric-morphism structure supplies both functors, their
  adjunction, and preservation of finite limits by the inverse image.
- Joint reflection of isomorphisms: for every pair of sheaves F,G and every
  morphism a, bijectivity of `(p j).inverse.map a` for all j implies `IsIso a`.
  Bijectivity is equivalent to invertibility in the category of sets. There
  is no extra point, stalk, or compatibility clause in the conclusion.

Statement dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`; its `inverse`, `direct`, `adj` and
  `leftExact` fields, and the `comp` definition used by the proof plan.
- `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction` (the latter two explain the proof plan).
- The localized-site dependency records
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, together with
  `CategoryTheory.GrothendieckTopology.over` and `CategoryTheory.Sheaf.over`.
  This set-sheaf statement imports the smaller owning module
  `Mathlib.CategoryTheory.Sites.Over`, using `Over`, `Over.forget` and its
  canonical localized-topology interpretation; no ring or module is needed.
  `Precoverage.comap` supplies the actual covering families exactly as specified
  in that dependency. The signatures and docstrings of both the topology and
  module restriction declarations were read.
- `def-weil-size-convention` is the recorded metatheoretic convention, with
  no declaring module; it is rendered by the explicit universes above.

The already stated proof inputs are imported without `public`:
`Sheaf.Paper.FinitarySiteEnoughPoints` (`finitarySite_enoughPoints`),
`Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`
(`continuousCocontinuous_toposAdjunctionForCoverings`),
`WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`
(`Functor.IsSpecialCocontinuousForCoverings`),
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
(`sheafification_sections_local`), and
`Mathlib.CategoryTheory.Sites.LocallySurjective`
(`Sheaf.isLocallySurjective_iff_epi`). The upstream sources missing in the old
checkout were read using `scompile.py --source`.
Their recorded interfaces are retained; future use of the small-category
finitary theorem may transport the category's sizes, and local-section descent
may be applied to the saturated covering-sieve presentation of the site. Neither
requires an added hypothesis on this statement.

Edge cases checked before writing:

- I can be empty. An epimorphism from the initial sheaf to the terminal sheaf
  forces the degenerate sheaf topos. Every object is empty-covered and the
  empty conservative family is valid. No `Nonempty` hypothesis was added.
- C may be empty. Slice assumptions are vacuous, and its sheaf category has
  only one object up to unique isomorphism, again allowing no points.
- A and K can be empty: finite includes zero, and the existential refinement
  map K → A has the correct empty-case meaning.
- A singleton family gives the ordinary single-slice criterion.
- Infinite coverings may have finite refinements without having finite
  subcovers; the explicit factoring arrows preserve this distinction.
- Non-subcanonical sites are included because h_U is sheafification, and
  the site need not itself have finite limits.
- Independent u and v and the containing value universe prevent a size
  restriction that would incorrectly drop sites with small hom sets and
  larger object types. Every variable and universe is explicitly bound.

Searches for an existing statement (no exact match):

- `msearch.py ... leanfinder`: "A site has enough points if a family of
  sheafified representables covers the terminal sheaf and each slice has
  finite limits and finite covering refinements". Eight hits: generic
  sheafification, `GrothendieckTopology.Point`, `Precoherent`, and canonical
  and coherent topology infrastructure; no slice criterion.
- `msearch.py ... loogle`:
  `CategoryTheory.GrothendieckTopology.HasEnoughPoints,
  CategoryTheory.GrothendieckTopology.over`. One hit on the instance
  transferring already-existing enough points to slices, not the converse
  existence statement with finite-cover hypotheses.
- `msearch.py ... grep`: `HasEnoughPoints|finitary|[Ff]inite.*[Rr]efin`,
  restricted to `CategoryTheory/Sites`. Twenty-five hits concerning point
  infrastructure and finitary extensive categories; no criterion as stated.
- Direct rg in Mathlib read `Precoverage.comap`, `Presieve.overEquiv`,
  `GrothendieckTopology.over`, `uliftYoneda`, `presheafToSheaf`, and the
  existing sheafification/colimit existence instances. These are reused.
- Direct rg of the project `lean/Sheaf` and upstream `WeilConjectures` found
  the finitary-site theorem and the consumer `proEtale_enoughPoints`; neither
  is this slice theorem. The former requires finite limits on the entire
  category and cannot replace the current statement.
- Exact item-id grep in upstream `WeilConjectures` returned no occurrence.
  Name searches for `finitarySlice_enoughPoints`, `finitarySlice`, and
  `FinitarySliceEnoughPoints` in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` returned no declaration with those names.

Validation: the delivered module compiled cleanly through the prescribed
`scompile.py NP lem-sfb-site-finitary-slice-enough-points ...` wrapper,
including the check under its library module name (1.6 seconds for that check).
Only the permitted named theorem has `sorry`; there are no helper definitions,
new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
