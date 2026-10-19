## Worker report

Delivery: lem-coef-simplicial-model-target-test, group Q82, stage 2.
Module: Sheaf.CategoryTheory.SimplicialModelTargetTest.
The sole theorem is CategoryTheory.SimplicialModelTargetTest.simplicial_model_target_test;
its proof is exactly `sorry`. No mathematical claim is proved. The helper
IsEssentiallySurjective has real propositional data, and expresses the component-functor
condition for the very morphism being tested. This helper belongs to this node's notion,
as permitted by the human's missing-canonical-interface update; it is not an independent
mathematical lemma. No source statement or dependency node was changed.

Clause-by-clause correspondence:

- Small simplicial categories and nested universes: `X Y : SCat.{max (u + 1) w}`
  are regarded from the outset in the larger ambient universe. `[Small.{u} X]`
  and `[Small.{u} Y]` express smallness of objects in the smaller universe;
  `_hX` and `_hY` express smallness in u of each degree of every mapping set.
  These are precisely size conditions, not local Kan or cofibrancy conditions.
  `Small` allows objects represented by lifted types, as well as literal Type u types.
- The morphism in h sCat is `f : bergnerHomotopyFunctor.obj X ⟶
  bergnerHomotopyFunctor.obj Y`. The existing BergnerHomotopyCategory is the
  localization at DK equivalences and is the model homotopy category supplied by
  the inversion dependency. Forming it in the larger universe lets its Hom sets
  contain the model-target maps in the node; no restriction to strict functors occurs.
- Essential surjectivity is `_hf : IsEssentiallySurjective f`. The helper uses
  a three-arrow representative X ← A → B ← Y, outside arrows DK and central
  functor g. Its equality fixes exactly the class f, and its final condition is
  the existing `PiZeroEssentiallySurjective g`, using inverse component equations.
  Outside equivalences on pi-zero preserve and reflect essential surjectivity.
  Such representatives exist by the model-category replacements; no condition on
  original endpoints is added and no particular replacement is chosen.
- The iff's left side is `IsIso f`.
- The quantifier over every combinatorial simplicial model category is
  `∀ (C : Type (max (u + 1) w)) [Category.{u} C] [ModelCategory C]
  [SimplicialCategory C] (_T : SimplicialTensorCotensor C),
  CombinatorialModelCategory.{max (u + 1) w, u, u} C →
  SimplicialModelLocalization.SatisfiesSM7 C → ...`.
  These are the exact notions provided by the projective-model-calculus dependency:
  compatible enrichment, actual tensor/cotensor data, small generating sets and local
  presentability, and the actual SM7 corner maps. `_T` does not alter the map being
  tested: its presence expresses that the model category is tensored/cotensored.
  Categories are locally u-small; their objects may fill the larger universe.
  The auxiliary w permits arbitrary further object-universe enlargement. In particular,
  enriched simplicial presheaves on the u-small X and Y fit in this containing universe,
  after resizing their small object/mapping data. There is no independent lower test
  universe that could make the hypothesis vacuous.
- A^{cf} is the existing `BifibrantObject C`, with exactly the restricted mapping
  simplicial sets. Its ambient bundled version is the existing
  `liftBundle (BifibrantObject C)`, which lifts all objects, mapping degrees, identities
  and composition; it neither inverts more arrows nor picks an unrelated target.
- The displayed precomposition function is literally `fun a ↦ f ≫ a`, with a
  ranging over Hom(Y,A^{cf}) in the ambient Bergner homotopy category. The conclusion
  uses `Function.Bijective` and hence includes both injectivity and surjectivity.
- The final clause is the second conjunct, conditional on `IsIso f`. It quantifies
  over every actual simplicial functor `g : A ⟶ B`, every pair of isomorphisms
  `eX : Q A ≅ Q X`, `eY : Q B ≅ Q Y`, and the representing equation
  `Q.map g ≫ eY.hom = eX.hom ≫ f`. It concludes the existing
  `DwyerKanEquivalence g`. This includes the original endpoints (identity isomorphisms),
  cofibrant/fibrant replacements, and arbitrary representatives with equivalent endpoints.
  No cofibrancy, local Kan, or fibrancy assumptions are imposed on X,Y,A,B.

Dependency declarations read and used:

- Sheaf.CategoryTheory.SimplicialInversionUniversalProperty:
  CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property. Read the
  full signature and proof docstring. Its public dependency interfaces supply the
  existing CategoryTheory.BergnerHomotopyCategory, bergnerHomotopyFunctor,
  bergnerWeakEquivalences (SimplicialFullyFaithfulHomotopyImage), SCat and underlying
  (CoherentNerveInfrastructure), and PiZeroEssentiallySurjective and
  DwyerKanEquivalence (CoherentNerveComparison).
- Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus:
  CategoryTheory.simplicial_projective_model_calculus. Read its full signature and
  eighteen-step docstring, together with its helper interfaces. Its public interfaces
  supply HomotopicalAlgebra.CombinatorialModelCategory
  (ModelColimitLocalizationComparison), SimplicialTensorCotensor
  (SimplicialTensorCotensor), and SimplicialModelLocalization.SatisfiesSM7
  (SimplicialModelNerveLocalization). The current source was also confirmed using
  `scompile.py --source Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`.
- Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus (already publicly
  imported by the inversion module): CategoryTheory.SimplicialLocalizationCalculus.liftBundle.
  Read its complete concrete degreewise ULift construction and bifibrant inclusion.
- Proof imports: Sheaf.CategoryTheory.ModelLocalizationDetectsWeakEquivalences,
  HomotopicalAlgebra.modelLocalization_weakEquivalence_iff_isIso;
  Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma,
  HomotopicalAlgebra.map_surjective_of_isLocalization and LeftHomotopyRel.iff_map_eq;
  Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel,
  SSet.ProjectivePresheaf.simplicial_presheaf_projective_model. Read these signatures
  and docstrings. The interval-lifting proof dependency is already a public import of
  the inversion module. The projective-model and inversion modules are public imports
  here because their notions occur in the statement. The remaining proof dependency
  lem-coef-simplicial-derived-pushout-mapping has no Lean record/mathlib match at this
  snapshot, so its proof-only import is deferred. It is not needed to type this statement.
  The theorem docstring records all eight proof steps, including the component-functor
  invariance supplied by that deferred node. No downstream essential-image theorem is
  used as a proof step; only its already shared localization definitions are used.

Edge cases checked: both source categories may be empty; essential surjectivity then
forces the target empty up to equivalence, rather than being dropped. A nonempty source
cannot map to an empty target. Identity morphisms and arbitrary isomorphic endpoint
representatives are included. Neither source must be locally Kan or cofibrant. Model
categories such as simplicial sets and enriched presheaves are allowed at object universe
u+1 and mapping universe u. Terminal model categories are allowed and do not suffice by
themselves: the test quantifies over every model category. Smallness includes lifted
encodings and does not bound cardinalities by a fixed finite/countable value. All
universes and all binders are explicit, with `autoImplicit false`.

Searches for existing statements and definitions:

- msearch.py leanfinder, query: "Essentially surjective simplicial functor is an
  equivalence if precomposition on homotopy classes into every combinatorial
  simplicial model category is bijective". Eight hits: ordinary functor essential
  surjectivity, SSet.hoFunctor, cofibrant-to-homotopy-category surjectivity and truncated
  homotopy categories. None gives this restricted enriched model-target test.
- msearch.py loogle, query `SimplicialCategory, IsIso, Function.Bijective`:
  zero hits; service reports unknown identifier SimplicialCategory.
- msearch.py grep, query `model_target|ModelTarget|BergnerHomotopy|dwyerKan`:
  zero Mathlib hits.
- Direct rg of WeilConjectures and lean/Sheaf for those patterns and
  `CombinatorialSimplicialModel` found the shared Bergner localization and DK interfaces,
  used above, but no detection theorem. Exact item-id search in WeilConjectures and
  dag/lean_names_upstream.json found no declaration. Further focused search for
  `BergnerEssentiallySurjective|ModelTargetTest|SmallSimplicial|IsSmallSimplicial`
  found no existing helper to duplicate. Read the actual shared declarations rather
  than replacing them with a private simplicial category or homotopy category.

Source verification: opened https://people.math.harvard.edu/~lurie/papers/HTT.pdf
and read Lemma A.3.4.6 (printed p.886), Corollary A.3.4.11 (p.889) and the target
reduction in Lemma A.3.5.14 (p.896). Also read the current blueprint ancestor proof
paragraph 2. HTT is still WANTED as a project archival source; this delivery changes
neither literature nor shared records. No statement dispute or source correction.

Validation: prescribed scompile.py compiled the module both as sandbox and library
module, without errors or warnings (1.5 s and 2.0 s in the reported compilation run).

## Second reading by Q82

Author's final self-check, not an independent review: reopened the node and the generated
module and checked the correspondences above against the actual signature. Checked the
reversal of composition notation (Lean f ≫ a is mathematical a after f), the direction
of both endpoint isomorphisms in the final square, the distinction between PiZeroEssentiallySurjective
and strict essential surjectivity, the degreewise size conditions, and the actual full
bifibrant model target. Found no omitted clause or extra non-size hypothesis; no changes
were needed after compilation. Independent review is the maintainer's responsibility
under the supplied dispatcher brief; no other agents were started.
