## Worker report

The module [lean/Sheaf/CategoryTheory/LocalizationHomotopyCategory.lean](lean/Sheaf/CategoryTheory/LocalizationHomotopyCategory.lean) defines the full coherent functor subcomplex `invertingDiagrams`, the induced homotopy-category functor `homotopyLocalizationFunctor`, and the universal-property predicate `IsCoherentLocalization`. Its theorem `localization_homotopy_category` states the node: every vertex of `L` is equivalent to one in the image of `q`; the induced functor from `C` to `SSet.hoFunctor.obj L` is equivalent to the canonical ordinary localization and is a localization at `W`; and functors of pairs induce natural functors between the ordinary localizations.

The first hypothesis is `[Category.{u,u} C]`; the second is the morphism property `W`; the quasicategory hypothesis is `[Quasicategory L]`; `q : nerve C ⟶ L` is the specified coherent localization map; and `hq : IsCoherentLocalization W q` expands the coherent universal property for every quasicategory `E`, requiring a coherent functor equivalence with the full subcomplex of diagrams carrying every `W`-morphism to an `IsEquivalenceEdge`. The essential-surjectivity clause is rendered by `∀ z, ∃ c e, δ₁ e = q(c) ∧ δ₀ e = z ∧ IsEquivalenceEdge L e`. The homotopy-category clause uses `SSet.hoFunctor`, `MorphismProperty.Localization`, `MorphismProperty.Q`, `Functor.IsLocalization`, and an equivalence `SSet.hoFunctor.obj L ≌ W.Localization` with a natural isomorphism to `W.Q`. The final clause quantifies functors of pairs and gives `F : W.Localization ⥤ W'.Localization` with `W.Q ⋙ F ≅ T ⋙ W'.Q`.

The statement dependency is `def-cbc-enhanced-diagrams-cones`, imported as `Sheaf.CategoryTheory.EnhancedDiagramsCones`; its declarations used are `SSet.Enhanced.fullSubcomplex`, `SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.IsFunctorEquivalence`, `SSet.Enhanced.evaluation` conventions, and the internal hom/nerve primitives supplied by that module and Mathlib. Mathlib declarations used are `CategoryTheory.nerve`, `ComposableArrows.mk₀`, `ComposableArrows.mk₁`, `SSet.hoFunctor`, `CategoryTheory.nerveFunctorCompHoFunctorIso`, `CategoryTheory.MorphismProperty.Localization`, `CategoryTheory.MorphismProperty.Q`, and `CategoryTheory.Functor.IsLocalization`.

Edge cases checked: `C` may be empty, `W` may contain only identities or all morphisms, and `L` may have no vertices; the universal-property predicate and the essential-surjectivity conclusion remain meaningful in all cases. The empty indexing/diagram cases are covered by the full-subcomplex construction. No nonemptiness or filteredness assumption was added.

Searches for an existing declaration: `msearch.py ... leanfinder "The homotopy category of an infinity categorical localization is the ordinary category localization"` returned only special derived/model-category localizations; `loogle "SSet.homotopyCategory", "Localization"` returned no match; `grep` over Mathlib AlgebraicTopology and the project for localization/homotopy-category patterns found no arbitrary coherent-localization theorem; `leanfinder` semantic searches for coherent localization and essential surjectivity returned only the generic nerve reflector and special derived-category results. The recorded `mathlib_searches` in the node contain the full query outputs and verdicts. No existing project declaration matched the complete statement.

No `STATEMENT-DISPUTED` flag or node fault.


## Second reading by Q59

I independently read the node, its eight proof steps, the Lean module, the full statement
and recorded declarations of `def-cbc-enhanced-diagrams-cones`, and the definitions
`FiniteReedy.largeNerve`, `Inverts`, `localDiagrams`, and `IsLocalization` serving
`def-coef-coherent-localization-interface`. No maintenance repair note exists for this item.
There are no new definition nodes or dependency modules in this delivery. The worker's
report above describes the original draft; the changes below supersede its description.

The node cites Cisinski, not Stacks. I opened the actual
https://cisinski.app.uni-regensburg.de/CatLR.pdf and read Theorem 1.6.6, Corollary 1.6.8,
and Section 7.1, especially Definition 7.1.1, Remarks 7.1.4 and 7.1.6. Theorem 1.6.6
compares the edge quotient with the path presentation; Remark 7.1.6 gives the ordinary
localization comparison. Universes are enlarged to contain the ordinary categories;
there is no model-category, calculus-of-fractions, finiteness, nonemptiness, ring, or
characteristic hypothesis at this source place. The node's stronger specification that
W is a wide subcategory is retained, rather than silently generalized to an arbitrary
class of arrows. I did not change the node's mathematical statement or proof.

The object/hypothesis/conclusion list, matched clause by clause:

1. The simplicial primitives, ordinary nerve, internal functor categories, equivalence
   edges and coherent equivalences are the existing Mathlib and
   `SSet.Enhanced` constructions imported from `EnhancedDiagramsCones`. I checked their
   signatures and actual definitions: equivalence edges have one inverse and both inverse
   triangles; full subcomplexes retain exactly all simplices on the chosen vertices;
   coherent functor equivalence has a simplicial quasi-inverse and both coherent natural
   inverse equivalences. Verdict: same notions, with all transformations retained.
2. For every quasicategory X, hX has its vertices as objects. We use
   `SSet.hoFunctor.obj X`; `hoFunctor.obj.equiv` identifies its object type with the
   vertices. I opened `HomotopyCat.lean`, including `OneTruncation₂.HoRel₂`,
   `HomotopyCategory.mk`, `homMk`, and the quotient construction. Verdict: Mathlib
   initially uses path classes, so the original draft needed an explicit comparison
   with the node's edge description.
3. Morphisms are homotopy classes of parallel edges, homotopy generated by triangles
   with a degenerate SHORT side. Added `homotopy_category_description`: its first
   conjunct says every morphism between specified vertices is `homMk` of an edge;
   its second says equality is exactly `Relation.EqvGen` of the union of the existing
   `Truncated.HomotopicL` and `HomotopicR` relations. I read these two definitions in
   `Quasicategory/TwoTruncated.lean`: they are respectively triangles with the final
   or initial short edge an identity. No degenerate long-edge relation is allowed.
   Verdict: exact quotient, neither more nor fewer identifications.
4. Composition comes from inner two-horn fillers. Mathlib's existing
   `Truncated.HomotopyCategory.homMk_comp_homMk` identifies the long edge with the
   composite of the short edges for every `CompStruct`; the new surjectivity and exact
   equality criterion therefore give exactly the node's composition on edge classes.
   No duplicate category, composition, or homotopy relation is defined. Verdict: exact.
5. An edge is an equivalence iff its class is an isomorphism. The third conjunct of
   `homotopy_category_description` is precisely `IsEquivalenceEdge X e.edge ↔
   IsIso (Truncated.HomotopyCategory.homMk e.toTruncated)`, for all endpoints and edges.
   Verdict: both directions restored; the original theorem omitted this assertion.
6. C is an ordinary category, made small in a containing universe. The binders are
   `{C : Type u} [Category.{u, u} C]`. The source explicitly permits enlarging to a common
   containing universe, so this does not require an originally specified object or Hom
   universe to be equal: a category in independent universes is represented in their
   containing universe first. All declarations are polymorphic in that containing u;
   neither u = 0 nor a fixed small universe is imposed. Verdict: source size convention.
7. W is a subcategory containing all objects. It is `W : MorphismProperty C` together
   with `[W.IsMultiplicative]`. I opened that Mathlib class: it extends exactly
   `ContainsIdentities` and `IsStableUnderComposition`, with no isomorphism-closure or
   two-out-of-three requirement. Restored this missing hypothesis. The same applies
   to target pairs `(C',W')`. Verdict: exactly a wide subcategory.
8. L is a quasicategory and q is the specified map `N(C) → L`. The binders remain
   `{L : SSet.{u}} [Quasicategory L] (q : nerve C ⟶ L)`. Verdict: unchanged and exact.
9. Restriction along q identifies the entire coherent functor category with the full
   subcategory inverting W, for every quasicategory E. Replaced the two duplicate
   definitions `invertingDiagrams` and `IsCoherentLocalization` with the existing
   `HomotopicalAlgebra.FiniteReedy.IsLocalization` from
   `def-coef-coherent-localization-interface`, which is now added to `stmt_deps`.
   Its enlarged nerve is the degreewise `ULift` of the ordinary nerve. The canonical
   isomorphism `isoWhiskerLeft (nerve C) uliftFunctorTrivial ≪≫ (nerve C).rightUnitor`
   has that lifted nerve as source and the ordinary nerve as target. Composing its hom
   with the SAME q supplies precisely the existing interface; it does not choose a new
   localization or assume another map. The interface includes quasicategory and
   W-inversion explicitly; these follow from the node's factorization property by
   testing at L on its identity. Thus no additional mathematical assumption is made.
   Verdict: canonical transport, existing notion, all coherent transformations included.
10. q is essentially surjective. The first main conjunct quantifies every vertex z and
    gives c and an edge e with source q(c), target z, and `IsEquivalenceEdge L e`.
    Verdict: exact; no surjectivity-on-vertices replacement.
11. The actual induced `hq : C → hL` gives the ordinary localization, with universal
    property on functors AND natural transformations. `homotopyLocalizationFunctor q`
    is the inverse nerve counit followed by `SSet.hoFunctor.map q`, so it is induced by
    the specified q. The main conclusion gives `e : hL ≌ W.Localization`, an actual
    natural isomorphism `α : homotopyLocalizationFunctor q ⋙ e.functor ≅ W.Q`, and
    `Functor.IsLocalization (homotopyLocalizationFunctor q) W`. I opened
    `Localization/Predicate.lean`: this predicate requires inversion and equivalence
    of the canonical finite-word extension, hence the full functor-category universal
    property (including its `whiskeringLeftFunctor` and natural-transformation lifts).
    Verdict: exactly ordinary localization and comparison under C.
12. The comparison is natural for functors of pairs. `T : LocalizerMorphism W W'` is
    Mathlib's ordinary functor together with preservation of marked arrows. For any
    second coherent localization q', and any comparison `(e',α')` under C', the
    conclusion supplies a coherent lift F with `AreNaturallyEquivalent (q ≫ F)
    (nerveMap T.functor ≫ q')` and its commuting ordinary square. It then quantifies
    EVERY F and commuting square δ and gives a UNIQUE comparison isomorphism β to
    `T.localizedFunctor W.Q W'.Q`, characterized under every c by the component
    equation involving α, α', δ and the canonical `Localization.Lifting.iso`.
    The equation is precisely equality of the two pasted comparison squares.
    Uniqueness with prescribed restriction gives identity and composition coherence:
    pasted comparisons have the same restriction and hence coincide. Verdict: the
    original unrelated existence of a functor between ordinary localizations was too
    weak; the repaired clause relates the coherent and ordinary induced functors and
    specifies their natural comparison, independent of the choice of equivalences.

Edge cases: C empty forces L empty by essential surjectivity, consistently with the
universal-property test on the empty full essential image. L empty and C nonempty admits
no q, as it should. For empty X, all edge/morphism clauses have empty vertex binders and
`hoFunctor.obj.equiv` still covers all objects. A discrete C, identities-only W, and
W all arrows are all allowed. The nerve of the one-object group Z is a useful short-side
check: a triangle with degenerate LONG edge does not collapse its two inverse arrows in
the stated relation. At dimension zero the object equivalence is the existing one, and
identity edges are degeneracies, without any positive-dimensional or nonempty assumption.
No scheme, integer degree, zero object, or characteristic occurs in this node. The
universe lift used for the shared interface is an actual isomorphism in the containing
universe, with degreewise up/down maps, not an added universe equation.

Independent searches, using words different from the worker's:

- `msearch.py ... leanfinder "localizing a relative category and passing to its fundamental
  category gives the Gabriel Zisman localization"`: eight hits, including
  `Functor.q_isLocalization`, `Localization.Construction.liftToPathCategory`, and
  `MorphismProperty.Q`; none states the arbitrary coherent-localization comparison.
- `msearch.py ... loogle "SSet.hoFunctor"`: twelve hits, including the actual homotopy
  category, its object equivalence, and the nerve adjunction/product preservation.
  I opened the relevant Mathlib definitions rather than identifying them by name alone.
- `msearch.py ... leansearch "The fundamental category of a quasicategory is the quotient
  of edges by homotopy and detects equivalence edges"`: eight hits. In particular I
  opened `TwoTruncated.lean` and reused `HomotopicL/R`; its own documentation explicitly
  leaves the comparison with the path presentation as a TODO. Thus the needed comparison
  theorem is not already available there.
- Direct `rg` across Mathlib's quasicategory/simplicial files, the source project's
  `WeilConjectures`, the project's `lean/Sheaf`, and the DAG found no complete theorem.
  The project search DID find `hammockInvertingDiagrams`, `IsHammockInfinityLocalization`,
  and the separately recorded `def-coef-coherent-localization-interface`. I read their
  definitions and reused the latter, eliminating the worker's second definition.
  The underlying full subcomplex, equivalence predicate, ordinary localization,
  morphism-of-pairs structure, and canonical induced ordinary functor are all reused.

Repairs: restored W's wide-subcategory hypothesis; removed the two duplicate
coherent-localization definitions; added the existing interface dependency and its
canonical universe transport; added the node's omitted edge-homotopy/iso criterion;
replaced the weak final clause with coherent lifts and the uniquely normalized ordinary
comparison; expanded the proof docstrings to cover all eight node steps; and added the
already stated proof-dependency imports. The two postponed theorems are the first
homotopy-category clause and the localization clause of this SAME DAG statement, both
listed in `lean.declarations`; no independent lemma or theorem is smuggled in.
All definitions have actual data, both theorem proofs are exactly `sorry`, and no local
notation, local instance, private definition, unbound variable, or unbound universe is
used. No natural-language statement correction, new node, or dependency repair is needed.

Validation: the complete repaired module compiled cleanly with the prescribed
`scompile.py Q59 lem-coef-localization-homotopy-category <absolute module path>`;
its final run checked both sandbox and library contexts (1.5 s and 1.8 s), with no
errors or warnings. Every Lean line is at most 100 characters. The node's
`lean.statement` was extracted verbatim from the main declaration's final signature.
