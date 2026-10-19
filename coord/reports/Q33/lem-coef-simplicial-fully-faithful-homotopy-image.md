## Worker report

The module defines the Bergner weak-equivalence morphism property, its canonical Mathlib localization and localization functor, and the objectwise `π₀` essential-image predicate `InEssentialImage`.  The main theorem states that a simplicial functor `j : T ⟶ T'` whose mapping maps are weak homotopy equivalences induces an injective postcomposition map on localized morphisms from every small simplicial category `I`; its image is the classes represented by a functor `b : I ⟶ T'` whose every object is isomorphic in `π₀ T'` to an object in the image of `j`.

The binders `I T T' : CoherentNerve.SCat.{u}` render the small simplicial categories in a fixed universe.  The binder `j : T ⟶ T'` renders the simplicial functor.  `hlocal` renders the hypothesis that every mapping simplicial map is a weak homotopy equivalence.  `bergnerWeakEquivalences` is exactly the Dwyer–Kan condition from the dependency declaration `CategoryTheory.DwyerKanEquivalence`; `BergnerHomotopyCategory` is its Mathlib localization and `bergnerHomotopyFunctor` its canonical quotient functor.  The first conclusion is `Function.Injective` for postcomposition by the localization image of `j`.  The second conclusion is the equivalence between existence of a representative `b` with `bergnerHomotopyFunctor.map b = a` and the objectwise essential-image predicate, and existence of a representative `c : I ⟶ T` whose postcomposition is `a`.  `InEssentialImage` expands essential image into `π₀` inverse witnesses `f` and `g` and the two identity-component equalities.

Dependency used: `Sheaf.CategoryTheory.CoherentNerveComparison`, declarations `CategoryTheory.DwyerKanEquivalence` and `CategoryTheory.coherent_nerve_comparison`.  Mathlib used: `CategoryTheory.MorphismProperty.Localization` and `CategoryTheory.MorphismProperty.Q` from `Mathlib.CategoryTheory.Localization.Construction`, and `Function.Injective`.

Edge cases checked: the universe binder allows any small `I`, including the empty simplicial category; the essential-image condition is vacuous for empty `I`; no essential-surjectivity hypothesis on `j` is added; empty mapping simplicial sets are permitted by the weak-homotopy-equivalence predicate; the `π₀` equations use the identity arrows and therefore include identity and zero-length cases.

Searches: `leanfinder` for homotopically fully faithful simplicial categories and essential-image maps (ordinary full/faithful and homotopy-category hits only; no match); `loogle` query `"SimplicialCategory", "FullyFaithful"` (0 hits); grep of Mathlib for `Bergner|Dwyer.?Kan` (no matching declaration); `leansearch` query `Derived morphisms into a full simplicial subcategory are determined by essential image` (ordinary `EssentialImage` declarations only); `rg` over `WeilConjectures` and `lean/Sheaf` (no existing declaration for this node).  Thus no existing declaration matched the statement.

No `STATEMENT-DISPUTED` flag.

## Earlier second reading (a previous round; superseded)

The statement was checked against the node clause by clause.  The fixed universe and all smallness hypotheses are explicit; the local weak-equivalence hypothesis and the injectivity/image conclusions are rendered directly.  `InEssentialImage` records exactly the two inverse identities in `π₀` required for essential image.  No mismatch was found.

## Second reading by Q33

I independently read the current node, its five proof steps, the sandbox module, and
all three dependency-node statements. I opened the declarations of
`Sheaf.CategoryTheory.CoherentNerveComparison`, its infrastructure module, and the
weak-equivalence and mapping-space definitions of `EnhancedDiagramsCones`. There
is no repair note for this item, no statement_change, no new definition node and
no dependency module in this delivery. Only the item's lean record changes from
the current shared node; its mathematical statement and dependency lists remain
unchanged.

Source checked: Lurie, Higher Topos Theory, Corollary A.3.4.11, printed p.889
(PDF page index 906), https://www.math.ias.edu/~lurie/papers/HTT.pdf, opened and
read through the web PDF text. It concerns an excellent enriching model category,
a functor which is a weak equivalence on every mapping object, arbitrary enriched
source categories, and both injectivity and the derived essential-image test.
Here the enriching category is simplicial sets with the weak-equivalence
convention already supplied by the coherent-nerve dependency. Its proof replaces
categories before using strict functors; it does not impose cofibrancy on the
original source. There is no Stacks source for this node.

Object/hypothesis/conclusion checklist, in node order:

- Small simplicial categories, with enriched mapping sets and composition:
  `I T T' : CoherentNerve.SCat.{u}`. I read `SCat = EnrichedCat SSet` and
  `sCatCategory`, whose morphisms are `EnrichedFunctor SSet`, as well as
  `underlying = ForgetEnrichment SSet`. Verdict: exact objects, including
  non-discrete and non-locally-Kan mapping sets.
- Bergner homotopy category: `bergnerWeakEquivalences` packages the dependency's
  existing `DwyerKanEquivalence`; `BergnerHomotopyCategory` and
  `bergnerHomotopyFunctor` are abbreviations for Mathlib's `MorphismProperty.Localization`
  and `MorphismProperty.Q`. I read those Mathlib declarations. The dependency's
  `BergnerModelData.weak_iff_dwyer_kan` identifies precisely this class. Verdict:
  ordinary localization at the stated weak equivalences, with real data and no
  selected model structure or arbitrary localization map.
- The component category has the same objects and components of mapping sets:
  `InEssentialImage` quantifies over the original object types and uses the
  dependency's `IsPiZeroIso`. I read its signature: an actual reverse arrow with
  both composition classes equal to the identity classes under `SSet.π₀.mk`.
  Every component has a vertex representative (`SSet.π₀.mk_surjective`, read in
  Mathlib's PiZero.lean), so this is exactly isomorphism in the component
  category, without requiring an ordinary strict inverse. Verdict: exact.
- Simplicial functor: `j : T ⟶ T'`. Verdict: the enriched functor from the node.
- Local weak-equivalence hypothesis: `hlocal : ∀ x y : T,
  SSet.Enhanced.IsWeakHomotopyEquivalence (j.map x y)`. The existing predicate
  uses realization components and all based homotopy groups. Verdict: exact;
  there is no essential-surjectivity, fibrancy, cofibrancy or injectivity-on-objects
  hypothesis on j.
- Every small source I in a fixed sufficiently large universe: the theorem binds
  `I` without further instances or restrictions. `SCat.{u}` allows any such
  source and its enriched hom sets in universe u; its localization and Hom types
  can live in the larger universe. Verdict: matches the node's fixed-universe
  convention, with no forced equality of two independently specified universes.
- Postcomposition is injective: `Function.Injective (fun a :
  (bergnerHomotopyFunctor.obj I ⟶ bergnerHomotopyFunctor.obj T) =>
  a ≫ bergnerHomotopyFunctor.map j)`. Verdict: exact, on all localized morphisms.
- Image consists of all classes a satisfying the component-category
  essential-image criterion: the theorem quantifies over every localized arrow
  a and states `IsInBergnerEssentialImage I T T' j a ↔ ∃ c :
  (bergnerHomotopyFunctor.obj I ⟶ bergnerHomotopyFunctor.obj T),
  a = c ≫ bergnerHomotopyFunctor.map j`. Verdict: repaired to be exact; the
  preimage c is itself an arbitrary localized morphism.
- The induced component functor of a is only defined up to natural isomorphism:
  `IsInBergnerEssentialImage` computes it on an existential three-arrow
  presentation `I ← A → B ← T'`. Its w and v are Dwyer--Kan equivalences, and
  `Q(w) ≫ a ≫ Q(v) = Q(b)` fixes exactly the represented localized arrow.
  `InEssentialImage A T B (j ≫ v) b` says for each object z of A that b(z) is
  isomorphic in π₀B to v(j(t)) for some t. Since π₀w and π₀v are equivalences,
  this is precisely the required condition on π₀a. Such presentations always
  exist: choose a cofibrant replacement A → I and a fibrant replacement T' → B;
  maps A → B up to model homotopy compute the localized Hom set. Therefore the
  existential presentation adds no mathematical hypothesis. Conversely any
  permitted presentation computes the same objectwise condition, since a
  localized equality induces naturally isomorphic component functors. Verdict:
  exact and independent of representatives; no strict representative of a is
  assumed.

Mismatches found and repaired:

1. H3: the original left side required `a = Q(b)` for a strict `b : I ⟶ T'`.
   Derived morphisms for arbitrary non-cofibrant I and non-fibrant T' need not
   have that form. Replaced this by the three-arrow presentation above.
2. H3: the original right side only allowed preimages `Q(c)` for strict
   `c : I ⟶ T`. This tests a smaller set than the image of postcomposition
   between localized Hom sets. Replaced it by an arbitrary localized c.
   These are repairs to the Lean rendering, not corrections of the DAG node.
3. H4/interface reuse: the original object test rewrote the two inverse equations
   that the dependency already names `IsPiZeroIso`. It now uses that declaration.
4. H8: the original `InEssentialImage` docstring lacked source and blueprint,
   and the theorem docstring omitted the node's proof. Added source/blueprint
   references to the helper and the complete five-step proof to the theorem,
   including the full-replete-subcategory argument, equivalence witnesses, and
   component-category comparison. The additional presentation helper has its
   own source/blueprint docstring and is listed in lean.declarations. It is part
   of this node's essential-image notion, not an independent missing DAG notion.

Edge cases: empty I has the vacuous objectwise condition; choose an empty
cofibrant source in a presentation. Empty T with nonempty I makes the objectwise
condition impossible, because an equivalence A → I preserves nonemptiness and
there is no t. If both are empty the empty presentation applies. The case j=id
now tests every derived arrow, rather than merely the ones with strict
representatives: use any cofibrant/fibrant presentation and essential surjectivity
of T' → B. A one-object I gives the π₀-isomorphism test, and j may identify
objects or miss entire components. Empty mapping simplicial sets are allowed.
Identity and degree-zero composition classes are included in IsPiZeroIso. There
is no n, coefficient characteristic, scheme, or additive zero-object restriction
in this statement. Universes are explicitly bound by `universe u`; no variable
or universe is auto-implicit.

Independent searches (2026-10-17):

- msearch leanfinder: `Localization of simplicial categories and detecting
  essential image by maps from the terminal category` returned ordinary
  localization essential-surjectivity/calculus-of-fractions results, QCat,
  and ordinary functor essential image; no matching result.
- msearch loogle: `"EnrichedFunctor.const"` returned zero hits; this also checked
  the candidate point-test construction while deciding how to repair the image
  criterion.
- msearch leansearch: `Maps from the one object simplicial category classify
  objects up to equivalence` returned SimplicialCategory, SSet.hoFunctor.terminalIso,
  SSet.unitHomEquiv and other ordinary simplicial primitives; no matching result.
- rg by declaration names over all Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no collision with any delivered name.
- rg by `essential.image.*(simplicial|bergner)` and its reverse, and
  `homotopically.*fully.*faithful`, over all three Lean trees found no match.
  Broader searches did find the coherent-nerve and fixed-object Bergner modules;
  I read their signatures. The fixed-object class is on `Fixed O`, not SCat.
  Mathlib's FullyFaithful.whiskeringRight (Whiskering.lean:116), which I also
  read, concerns ordinary categories and cannot replace this derived enriched
  theorem. No existing declaration states this node. Existing localization,
  Dwyer--Kan and component-isomorphism definitions are reused.

Proof imports: `CoherentNerveComparison` is public because its definitions occur
in the statement. It already publicly imports `EnhancedDiagramsCones`, the
other stated proof dependency. `lem-coef-infinity-full-essential-image` has no
Lean record on the current base, so no import can be added for it; its role is
retained explicitly in the theorem's proof docstring. It is only a proof input,
not an unstated object required to type this item.

Validation: scompile.py Q33 lem-coef-simplicial-fully-faithful-homotopy-image on the
single delivered module compiled both the sandbox form and library-path form
cleanly (1.8 s and 1.6 s). Every definition has real data, the sole theorem has
whole proof `sorry`, no theorem was proved, all declaration docstrings carry the
source and blueprint, all lines are at most 100 characters, and lean.statement
was copied verbatim from the final theorem signature. No STATEMENT-DISPUTED flag.
