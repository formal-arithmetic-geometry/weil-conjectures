## Worker report

The delivery states `CategoryTheory.ExactDerivedPasting.exact_derived_transformation_pasting`
in `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`. Its only postponed proof is that
theorem, whose docstring gives all nine proof steps of the node. The node is unchanged except
for `lean`. There are no new DAG nodes, repaired dependencies, or statement corrections.

The finite-word and finite-expression helpers belong to this node's own pasting construction;
they implement the words and expressions explicitly introduced in its proof. They do not
replace the existing notions of exact functor, natural transformation, derived category,
degreewise application, localization, or canonical derived composition. All helper data is
constructed explicitly, without a postponed proof or choice of an unspecified object.

Hypotheses and clauses, individually:

* A finite diagram of abelian categories: `I : Type t`, `[Finite I]`, `C : I → Type u`,
  `[∀ i, Category.{v} (C i)]`, and `[∀ i, Abelian (C i)]`. Objects, morphisms, and chosen
  derived-category morphisms have the independent universes `u`, `v`, and `w`. A finite
  heterogeneous diagram may be presented in common sufficiently large universes; no equality
  of these three universes is imposed. The theorem does not impose a small-category condition.
* Chosen ordinary unbounded derived categories: `[∀ i, HasDerivedCategory.{w} (C i)]` and
  Mathlib's `DerivedCategory (C i)`. Localization uses all `CochainComplex (C i) ℤ` and
  `HomologicalComplex.quasiIso (C i) (ComplexShape.up ℤ)`.
* Additive exact edge functors: `Word.edge` takes the existing Mathlib `C i ⥤ₑ C j`, whose
  property is preservation of finite limits and finite colimits. Its additivity follows from
  Mathlib's existing `exactFunctor_le_additiveFunctor`, used by `Word.ordinary_additive`.
  This is equivalent to the node's explicit additive exactness, not an extra condition.
* Finite composites of edges: `Word.comp` is binary composition, `Word.ordinary` evaluates
  it to the ordinary exact composite, and `Word.derived` evaluates it to the composite of
  the exact derived edges. `Word.nil` represents the empty word at every vertex. Although
  the syntax permits any exact edge label, each particular expression uses only finitely
  many edges and cells; a finite given labelled diagram is a special selection of these.
* Degreewise `C(F)` and the standard derived factorization: `Word.cell` uses
  `mapHomologicalComplex (ComplexShape.up ℤ)`, `NatTrans.mapHomologicalComplex`,
  `Functor.mapDerivedCategory`, and its existing `Localization.Lifting` instance, whose iso
  is `Functor.mapDerivedCategoryFactors`. These are exactly the recorded dependency API.
  The chosen derived categories remain arbitrary through `HasDerivedCategory`; the chosen
  exact functors and their standard factorizations are the canonical ones in that API.
* A possibly noninvertible ordinary cell: `Word.cell` takes
  `α : P.ordinary.obj ⟶ R.ordinary.obj`, with no `IsIso` assumption. It first applies
  `P.comparison.inv`, then `Localization.liftNatTrans` to the degreewise cell whiskered by
  `DerivedCategory.Q`, then `R.comparison.hom`.
* The precise two-edge comparisons: when `P = Word.comp (.edge F₁) (.edge F₂)`,
  `P.comparison` is `Functor.mapDerivedCategoryCompIso F₁.obj F₂.obj` followed only by
  whiskerings of reflexive isomorphisms. Its direction is `D(F₁ ⋙ F₂) ≅ D(F₁) ⋙ D(F₂)`.
  The normalization is `mapDerivedCategoryCompIso_fac`, identical to the equation in
  the recorded `existsUnique_mapDerivedCategoryCompIso` dependency. Thus the construction
  is inverse source comparison, localized cell, forward target comparison, in that order.
* Specified ordinary compositor isomorphisms: their hom and inverse are ordinary natural
  transformations and are admissible `Expression.cell` arguments, interpreted by exactly
  the same `Word.cell`. They are not replaced by arbitrarily chosen derived isomorphisms.
* Finite composites and whiskerings: `Expression.cell`, `.id`, `.vcomp`, `.input`, and
  `.output` provide the five generating operations; `.assoc`, `.assocInv`, `.leftUnit`,
  `.leftUnitInv`, `.rightUnit`, and `.rightUnitInv` explicitly insert structural comparisons.
  The two evaluation functions recurse using identities, categorical composition,
  `Functor.whiskerLeft`, `Functor.whiskerRight`, and the corresponding functor unitors and
  associators in the ordinary or derived categories.
  The first conjunct says every derived expression equals the normalized lift of its entire
  ordinary evaluation. It is also the expression-induction formulation of preservation of
  identities, composition and both whiskerings, including all compositor occurrences.
* Every equality passes to derived categories: the second conjunct quantifies over any
  two expressions with common source and target words, and maps `e.ordinary = f.ordinary`
  to `e.derived = f.derived`. No assumption about invertibility is made here.
* Vertical square pasting uses `.vcomp` and `.input`/`.output` for the adjoining edges.
  Horizontal square pasting uses the two whiskerings and `.vcomp`. The second conjunct
  therefore applies to either orientation, including cells with different intermediate
  vertices, with `Word.comparison` inserting exactly the specified comparisons.
* Naturality equations: the ordinary naturality or interchange equality is an equality of
  the ordinary evaluations of the corresponding whiskered composite expressions; the
  second conjunct sends it to that same equality of derived evaluations. Each evaluated
  cell is itself a natural transformation, so its objectwise naturality is part of its type.
* Compositor unit equations: empty words have derived interpretation the actual identity
  functor, and their comparison is the existing `Functor.mapDerivedCategoryIdIso`.
  The structural `.leftUnit` and `.rightUnit` expressions, and their inverses, evaluate
  to the actual ordinary or derived functor unitors. The first conjunct identifies these
  actual derived unitors with localization using the prescribed comparisons. Comparing
  unit pastings with `.id` then gives the unit equations through the second conjunct.
  `.assoc` and `.assocInv` give the same explicit compatibility with the actual functor
  associators, for the two parenthesizations of a word. A specified ordinary compositor
  can also be supplied through `.cell`; it is derived by that identical localization rule.
* Invertible ordinary cells give invertible derived cells: the third conjunct is exactly
  `IsIso α → IsIso (Word.cell C α)`. No invertibility restriction appears in the other clauses.
* No resolutions, boundedness, or faithful evaluation: none occurs in the binders or helper
  definitions. Everything is localized from unrestricted integer-indexed complexes.

Dependencies read and used:

* `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q` and its localization instance.
* `lem-weil-pbc-exact-functor-derived-factorization`: its `mathlib_match` in
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, namely
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`, and the associated
  `Localization.Lifting` instance. The source and the entire factorization signature were read.
* `lem-sfb-exact-derived-composition`: imported
  `Sheaf.CategoryTheory.ExactDerivedComposition` and read
  `CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso`, including its final
  termwise-composition identification. The actual comparison is the existing upstream
  `Functor.mapDerivedCategoryCompIso`, in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, whose definition
  and `mapDerivedCategoryCompIso_fac` were read. It is the normalized comparison of that node.
* Proof dependency `lem-weil-pbc-localization-universal-property`: read its `mathlib_match`
  and `Mathlib.CategoryTheory.Localization.Predicate`, especially `Lifting`, `liftNatTrans`,
  `liftNatTrans_app`, `comp_liftNatTrans`, `liftNatTrans_id`, `liftNatIso`, and `natTrans_ext`.
* Other existing APIs used: `ExactFunctor` in `Mathlib.CategoryTheory.Limits.ExactFunctor`;
  `exactFunctor_le_additiveFunctor` in `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`;
  `NatTrans.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`; and upstream
  `Functor.mapDerivedCategoryIdIso` for the empty word.

Sources checked locally: `literature/stacks-project/derived.tex`, lemma
`lemma-right-derived-exact-functor` (Tag 015F, lines 5883--5903), and
`literature/stacks-project/categories.tex`, lemma `lemma-properties-left-localization`
(Tag 04VG, beginning at line 4406). The natural-transformation enhancement is explicitly
the Mathlib localization API, as the node's source and proof say; Stacks itself only states
the functor-factorization part there.

Edge cases checked before writing and again against the finished syntax:

* Empty `I`: no spurious nonempty or base-vertex hypothesis; the quantified conclusions
  are vacuous, as a diagram with no cells requires.
* Empty words and insertion at either end: `.nil` evaluates to identities and the canonical
  derived unit comparison, rather than to the derived identity functor without comparison.
* Identity and zero ordinary cells: `.cell` accepts both; neither an `IsIso` binder nor a
  nonzero hypothesis is present. The identity expression and an identity cell have the
  same derived evaluation by the first/second conjuncts.
* Pasting between different intermediate vertices: words are indexed by their two endpoints;
  the two sides of an ordinary cell need only have the same endpoints.
* Repeated edges, different parenthesizations, and arbitrarily long finite composites:
  recursive words and expressions impose no fixed-length bound.
* Negative cochain degrees and complexes unbounded in both directions: all degrees are `ℤ`,
  with no support or cohomological bound predicate anywhere.
* Invertible ordinary cells with nontrivial chosen factorization isomorphisms: conjugation
  uses both word comparisons; it does not assert equality of the single and composite
  derived functors.

Searches (all with `msearch.py Q21 lem-sp-exact-derived-transformation-pasting` where applicable):

* LeanFinder: `Exact functors on unbounded derived categories preserve natural transformation
  pasting and whiskering`. Eight hits, including `mapDerivedCategoryFactors`,
  `mapDerivedCategoryFactorsh`, and `Abelian.Ext.mapExactFunctor_hom`; no full match.
* Loogle: `CategoryTheory.Functor.mapDerivedCategoryCompIso`. Seven hits on the canonical
  composition isomorphism and component lemmas. This is a reused ingredient, not the
  arbitrary noninvertible finite-expression assertion.
* Mathlib grep: `mapDerivedCategoryNatTrans|mapDerivedCategorySquare|liftNatTrans.*comp`.
  Two hits in localization Adjunction/Predicate; no whole-statement match.
* LeanSearch: `Localization of natural transformations between exact functors preserves
  finite pasting and whiskering on unbounded derived categories`. Eight hits, including
  `Localization.liftNatTrans`, `Construction.natTransExtension`, and exact-functor whiskering;
  these supply ingredients, not this statement with the derived comparisons.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for `mapDerivedCategoryNatTrans`,
  `mapDerivedCategorySquare`, derived pasting and `liftNatTrans`. Existing upstream
  `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` handle invertible cells and
  comparisons. `Sheaf.CategoryTheory.DerivedExactSquareComposition` was opened: it states
  pasting for isomorphism cells, so it does not handle the node's arbitrary transformations.
* `rg -n 'lem-sp-exact-derived-transformation-pasting' lean/WeilConjectures`: no match.
* Declaration-name collision search for `ExactDerivedPasting`, `ExactFunctorWord`, and
  `DerivedPastingExpression` in both libraries and `dag/lean_names_upstream.json`: no match.

Validation: `scompile.py` compiled both its sandbox probe and the library module cleanly.
The final delivery is also checked by `deliver2.py --no-push` before pushing.
Every theorem proof is `sorry`, every universe and variable is explicitly
bound, and every line is at most 100 characters. The `autoImplicit false` setting is explicit.

## Second reading by Q21

This is the dispatcher's single worker's separate second reading; no second agent was started.
The maintainer will supply the independent review of the delivery.

I reread the node statement, its nine proof steps, the dependency's comparison normalization,
and the completed module. `Word.cell` has the three factors in the required order. For a
two-edge word the recursive comparison reduces to the normalized exact-composition iso;
for an empty word it is the canonical derived unit iso. Both expression whiskerings evaluate
at the correct side of the ordinary and derived word functors. All cells, including ordinary
compositors and their inverses, use the same localization construction, not an arbitrary map.

The first conjunct supplies the expression-induction conclusion needed to interpret every finite
expression with those comparisons. The second carries all given equations, rather than only
one square or only invertible pastings. The third treats invertibility separately, so it
cannot silently restrict the first two. No clause requires a faithful evaluation, resolution,
boundedness, nonempty diagram, or invertible cell. I found no mathematical mismatch or node
fault; no statement correction was made. The first compile exposed only an explicit-argument
ordering error and two missing namespace prefixes in the comparison definition; these were
corrected without changing its data or the theorem statement, and the next compile was clean.
After the first passing dry run I made structural unitors and associators explicit expression
constructors. This makes the first conjunct directly assert compatibility with the actual
derived unitors and associators, rather than requiring the reader to recover that consequence
from the localization construction. I reread these six evaluation clauses against their
endpoint words: left unit removes an initial empty word, right unit removes a final empty
word, and associativity changes only parentheses, with the inverse clauses reversed.
