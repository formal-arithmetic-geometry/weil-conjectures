## Worker report

The module `Sheaf.CategoryTheory.SimplicialLocalizationEssentialImage` states
`CategoryTheory.SimplicialInversion.simplicial_localization_essential_image` with
one `sorry` and no new definitions. Only the item's `lean` field changes.

Hypothesis and clause correspondence:

- Small simplicial category C and arbitrary set W of vertex arrows:
  `(P : SimplicialLocalizationCalculus.Pair.{u})`. Its `category : SCat.{u}`
  is C, and `marked : MorphismProperty (underlying category)` is precisely a
  predicate on vertex arrows. Its existing `Marks P` indexes all marked arrows,
  including their endpoints. No closure or saturation property is required.
- The Bergner model structure: `(B : BergnerModelData.{u})`. This existing
  structure has the actual model axioms and identifies its weak equivalences
  with Dwyer--Kan equivalences. Quantifying over it does not assume a new property
  of C or W; the dependency supplies its existence.
- The derived localization and its canonical structure map:
  `(L : SCat.{u}) (q : P.category ⟶ L)` together with
  `(_hq : Nonempty (LocalizationPresentation B P q))`. This is the exact
  presentation used in the recorded dependency's theorem: it fixes the marked
  arrow evaluations, resolves the walking-groupoid leg by a cofibration and weak
  equivalence, and imposes the model homotopy-pushout condition on q. Thus q is
  the specified localization unit, not an unconstrained map or arbitrary choice.
  `Nonempty` is only an assumption that the given q has this presentation;
  no object or map is defined by choosing from a postponed existence theorem.
- All displayed categories fit in one sufficiently large universe: `universe u`
  and the explicit `.{u}` parameters on B, P and L. Any individually small
  categories can be placed in this containing universe.
- Essential surjectivity of π₀q, including the explanation for each object y:
  `PiZeroEssentiallySurjective (A := underlying P.category)
  (B := underlying L) q`. Reading the existing definition gives exactly
  `∀ y, ∃ x, ∃ f : q.obj x ⟶ y, ∃ g : y ⟶ q.obj x`, with both composites
  equal to identities after applying `SSet.π₀.mk` to the corresponding mapping
  simplicial sets. These are inverse components, not strict inverse vertex arrows.
  The predicate retains the objects of C and L and quotients only mapping vertices
  by path components, as the node requires.
- No fibrancy, cofibrancy or saturation hypothesis: none occurs in the signature.
  In particular the cofibrancy conditions internal to the existing definition
  of a derived pushout concern its replacement span, not the original C or L.

Dependencies read and used:

- `Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`, main theorem
  `CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`:
  read its complete signature and docstring. It supplies the Bergner structure,
  existence of presentations and their mapping property. The statement uses its
  exact input interface `LocalizationPresentation B P q`.
- That module publicly imports
  `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`: read `Pair`,
  `Marks`, `LocalizationPresentation`, and their complete docstrings and fields.
  Only these constructions are used, not the downstream comparison theorem.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: read `BergnerModelData`,
  `PiZeroEssentiallySurjective`, `PiZeroEquivalence`, `DwyerKanEquivalence`
  and their full definitions/docstrings; these are available through the recorded
  dependency's imports, without a copied definition.
- Proof dependency `lem-coef-simplicial-category-degreewise-colimits`:
  `Sheaf.AlgebraicTopology.SimplicialCategoryDegreewiseColimits`, declaration
  `CategoryTheory.CoherentNerve.simplicial_category_degreewise_colimits`, is
  imported. Read the theorem and its object-set colimit construction.
- Proof dependency `lem-coef-simplicial-arrow-attachment-localization` has no
  recorded Lean declaration or mathlib match in the snapshot. Its proof import
  is deferred, as explicitly recorded in the theorem docstring. It is not needed
  to type the statement and no missing notion is being assumed in its place.

Source read: [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf),
Notation A.3.5.1, Remark A.3.5.2, Proposition A.3.5.5, printed pp. 891--893
(PDF pages 908--910). The module docstring reproduces all four steps of the node's
agent-derived essential-image argument, with each input identified.

Edge cases checked before writing: W empty (localization is equivalent under C
to C); C empty (its marking is empty and the localization has no objects up to
component equivalence); a marked identity or loop; repeated endpoints of different
marked arrows; walking-arrow inversion; non-Kan mapping sets. The statement
assumes neither nonemptiness nor object-surjectivity of q, and only asserts
existence of inverse components. It allows a chosen derived representative with
additional objects component-isomorphic to original objects.

Searches, 2026-10-17:

- `msearch.py ... leanfinder "The path component functor from a simplicial category
  to its derived localization is essentially surjective"`: eight hits, including
  ordinary `CategoryTheory.Localization.essSurj`, truncated homotopy-category
  surjectivity and cofibrant-object localization. No enriched localization theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.EssSurj,
  CategoryTheory.Localization.essSurj"`: two hits, the ordinary localization
  theorem and an unrelated locally-small-localization definition.
- `msearch.py ... leansearch "A simplicial localization unit is essentially
  surjective on the category of path components"`: eight hits, including ordinary
  localization, derived categories, skeletons and unrelated simplicial-set units.
- `msearch.py ... grep
  "(simplicial|Dwyer|Bergner).*(localiz|[Ee]ss[Ss]urj)|(localiz|[Ee]ss[Ss]urj).*(simplicial|Dwyer|Bergner)"`:
  zero Mathlib hits.
- Read `Mathlib/CategoryTheory/Localization/Predicate.lean`, lines 178--207:
  `Localization.essSurj` assumes an ordinary `L.IsLocalization W`. Identifying
  π₀q as such an ordinary localization would be an additional theorem; this is
  not an exact existing match for the node.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json` for `PiZeroEssentiallySurjective`,
  `simplicial_localization_essential_image` and the node id: the source and name
  index contain no match. Side-library hits are the predicate definition in
  `CoherentNerveComparison` and its existing uses; no statement of this theorem.
- Broader side-library search for simplicial localization/Bergner declarations
  located the recorded universal-property and comparison-calculus interfaces,
  which were read and reused. The node-id search of upstream returned no hits.

No statement correction, new nodes, dependency repairs or disputed statement.

Compilation: the initial module-system form could not import the mandatory proof
module `SimplicialCategoryDegreewiseColimits` because that published file is a legacy
(non-`module`) Lean file. Confirmed its current contents with
`scompile.py --source Sheaf.AlgebraicTopology.SimplicialCategoryDegreewiseColimits`.
The delivered file uses compatible legacy imports, retaining both required imports
and the identical theorem signature. No live dependency file was edited.

## Second reading by Q53

Author's self-check, under the dispatcher's direct-delivery instructions; the
maintainer performs the independent review. Reopened the item and the complete
Lean file and compared each binder and conclusion with the node. P includes
exactly C and its arbitrary vertex marking; B is the dependency's Bergner structure;
L, q and the presentation express exactly the derived pushout under C. The conclusion
uses the original existing component-essential-surjectivity predicate, whose two
component equalities were read directly. No strict-inverse condition, object-set
surjectivity, local Kan condition or cofibrant-source restriction was introduced.
The proof docstring follows the node's four steps and records the unstated proof
module explicitly. No mathematical mismatch was found. The only format change
was the compatible legacy import form required by the published proof dependency.
The node's lean.statement is extracted verbatim from the final theorem signature.
