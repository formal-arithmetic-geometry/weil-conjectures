## Worker report

The module `Sheaf.CategoryTheory.SiteHypercoverDisjointUnion` states
`CategoryTheory.SimplicialObject.site_hypercover_disjoint_union`, with its only theorem proof
`sorry`. Its docstring gives all four DAG proof steps and their supporting nodes.
The fully defined helper `IsProperFaceMatchingArrow` is a characterization interface for the
existing matching-object notion, not a second construction or a new independent notion.
It uses the existing `matchingBoundaryIndex` and specifies the canonical matching arrow by
its composites with every face projection. Both declarations are listed in `lean.declarations`.
No statement correction, new node, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A small site is `{C : Type u} [SmallCategory C]`, with the recorded `Precoverage` site
  interface `J`, `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, and
  `J.HasPullbacks`. The fibre-product assumption is `[HasPullbacks C]`.
- Subcanonicity is `[J.toGrothendieck.Subcanonical]`. Mathlib's `J.toGrothendieck.yoneda`
  therefore has precisely the representable sheaves of sets as its objects.
- The fixed base is `(T : C)`. The input `K : SimplicialObject (FormalCoproduct.{u} (Over T))`
  encodes the families of objects mapping to T, all component maps over T, and all
  simplicial and augmentation equations. A simplicial object in this slice is the specified
  augmented object; no separate arbitrary augmentation is introduced.
- The degree-zero and proper-face covering hypotheses are `hcover`. For each matching
  arrow `μ` and each target member `j`, the subtype `{i // μ.f i = j}` is exactly its source
  fibre. `μ.φ i.val` followed by the equality transport has target `M.obj j`, and `.left`
  gives the arrow in C. Membership of `Presieve.ofArrows` in `J (M.obj j).left` is the
  covering-family condition, rather than an epi hypothesis replacing it.
- `IsProperFaceMatchingArrow` has three branches: degree zero is a terminal object;
  degree one is a limiting two-member fan and the equations `μ ≫ p i = K.δ i`;
  degree n+2 is a limiting cone on `matchingBoundaryIndex K n`, up to projection-compatible
  identification, with the same face equations. Thus it tests the exact matching arrows,
  never arbitrary morphisms. Quantifying over all choices is equivalent to testing the
  canonical choice, since all such limits are uniquely projection-compatibly isomorphic
  and covering families are stable under these isomorphisms. Existence of these limits
  follows from the slice's terminal object and pullbacks, then the recorded finite-limit
  theorem for FormalCoproduct. There is no vacuity from missing matching objects.
- `(a : ∀ n, Cofan (K _⦋n⦌).obj)` and `ha` give exactly the given coproducts in C/T,
  with their canonical inclusions. They impose neither global coproducts in C nor any
  disjointness condition in addition to the node's explicit hypotheses.
- `hsheaf` says the cofan with vertex `h_(a n).pt.left` and legs the Yoneda images of those
  inclusions is colimiting in sheaves on C. This is exactly that the canonical map from
  the coproduct of the representable sheaves is an isomorphism, by uniqueness of colimits.
  In particular it concerns the canonical inclusions, not an arbitrary isomorphism of objects.
- The conclusion supplies `A : SimplicialObject (Over T)` and identifications
  `e n : A _⦋n⦌ ≅ (a n).pt`. For EVERY operator `φ : [m] ⟶ [n]` and EVERY summand `i`,
  the displayed equation says that the induced map is the disjoint union of `K.map φ.op`.
  These equations uniquely specify the operators by the given coproduct universal properties.
  Thus the isomorphisms allow the harmless choice of representatives of the coproducts;
  they do not leave the simplicial structure unconstrained.
- `A ⋙ Over.post J.toGrothendieck.yoneda` is the actual representable augmented simplicial
  sheaf over h_T. The last clause asserts `Epi μ.left` for every one of its matching arrows.
  Using `.left` asserts the epi in sheaves on C, exactly as the node requests. Since the
  matching construction occurs in `Over h_T`, its terminal object in degree zero is h_T
  and its binary product in degree one is h_A0 ×_[h_T] h_A0. Higher degrees use the finite
  proper-face diagram with all pairwise compatibility equations.

Dependency declarations used:

- `def-weil-pbc-sites-and-cohomology`: the record's explicitly documented site interface
  `CategoryTheory.Precoverage`, its four site classes, `Precoverage.toGrothendieck`, and
  `CategoryTheory.Sheaf`; imported from Mathlib's `PrecoverageToGrothendieck` and
  `Subcanonical` modules. The unrelated object-cohomology declaration H' is not used.
- `def-weil-pbc-formal-coproduct`: Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic,
  `CategoryTheory.Limits.FormalCoproduct`, `.Hom`, `.f`, and `.φ`.
- `def-weil-pbc-simplicial-object`: Mathlib.AlgebraicTopology.SimplicialObject.Basic,
  `CategoryTheory.SimplicialObject`, `.δ`, and the functor maps, publicly available through
  the matching-object module.
- Added the already landed `lem-weil-pbc-simplicial-matching-object` to `stmt_deps`, since
  the signature's helper uses `CategoryTheory.SimplicialObject.matchingBoundaryIndex` from
  `Sheaf.CategoryTheory.SimplicialMatchingObject`. Its declaration and full source were read.
- The available proof dependencies are imported: FormalCoproducts.Basic and
  LimitsOfProductsAndEqualizers for formal finite limits; Sheafification and LeftExact for
  sheafification and finite-limit exactness; LocallySurjective for
  `Sheaf.isLocallySurjective_iff_epi`; Sheaf.Paper.SiteSheafificationSectionsLocal for
  `CategoryTheory.sheafification_sections_local`. The matching-object module is already public.

Edge cases checked: n=0 uses no face projection or n-1 subtraction; n=1 has precisely two
unconstrained faces in the slice, hence their fibre product over T. n=2 uses three faces
and all three pairs with the existing d_(j-1)/d_i formula. Empty term index types remain
allowed: their cofans are empty coproducts and their matching-cover conditions remain the
actual empty-family covering conditions. Empty target fibres are tested by the same
Presieve.ofArrows condition. Singleton families reduce to the original representable
objects. No finiteness, splitting, nonemptiness, affine, or scheme assumption is imposed.
The index universe is u, the project's recorded SEMI-REPRESENTABLE HYPERCOVER convention.
The helper has explicit independent category object and morphism universes.

Searches made (all actual tool results, with machine search log in `searches.jsonl`):

- LeanFinder through msearch.py: "Taking disjoint unions of semirepresentable hypercovers
  gives a hypercover of sheaves": eight hits, on zero/one-hypercovers, their families, and
  homotopy quotients; none states the all-degree comparison here.
- Loogle through msearch.py: "FormalCoproduct, SimplicialObject": no hits (unknown
  unqualified identifier FormalCoproduct). Repeated with the fully qualified
  "CategoryTheory.Limits.FormalCoproduct"; see the logged result.
- LeanSearch through msearch.py: "Taking disjoint unions of the terms of a semirepresentable
  hypercover preserves epimorphic matching maps": unavailable, Internal Server Error.
- Mathlib grep through msearch.py: `hypercover|matchingBoundary|FormalCoproduct` in
  CategoryTheory: zero/one-hypercover and formal Cech interfaces, not this theorem.
- Direct rg in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  `IsProperFaceMatchingArrow|site_hypercover_disjoint_union`: no name collision.
- Direct rg in those same three roots for coproduct/disjoint-union hypercover comparisons:
  Mathlib CoproductSheafCondition and zero/one-hypercover coproduct constructions only.
- Direct rg of upstream WeilConjectures for hypercovers and of the exact blueprint id:
  finite zero/one-hypercover constructions only, no declaration for this node.
- Project rg for matching/hypercover interfaces found SimplicialMatchingObject and the
  scheme-specific SemiRepresentableObject. The latter only concerns X.Etale and is not
  substituted for the arbitrary site. DAG records for both notions and formal finite
  limits were read before choosing the existing generic matchingBoundaryIndex interface.

Source read: local Stacks hypercovering.tex, remarks
remark-take-unions-hypercovering (0DB1) and remark-take-unions-hypercovering-X (0DB2).
Working in C/T supplies the terminal object and finite limits needed for the augmented
version of the sheafified finite-limit argument. No source discrepancy or
STATEMENT-DISPUTED issue was found.

Validation: the module compiled cleanly with scompile.py on the server (nice 19,
two threads, 60-second per-file limit); no local compiler or lake build was run.


## Second reading by NQ

I independently read the node and its four proof steps, Stacks hypercovering.tex
remarks remark-take-unions-hypercovering (0DB1) and
remark-take-unions-hypercovering-X (0DB2), the delivered module, and the actual
dependency declarations. No mismatch requiring a Lean or node change was found.
The second reading adds this review only; the worker report remains intact.

Objects, hypotheses, and conclusions, in the node's order:

1. Small site C with fibre products: `{C : Type u} [SmallCategory C]
   [HasPullbacks C]` and `J : Precoverage C` with `HasIsos`,
   `IsStableUnderComposition`, `IsStableUnderBaseChange`, and `HasPullbacks`.
   Verdict: exact recorded site interface of def-weil-pbc-sites-and-cohomology.
   I read Precoverage.lean's class fields; these are the site axioms, not added
   finiteness or geometric hypotheses. Global pullbacks supply the site's
   required pullbacks; the latter binder adds no mathematical restriction.
2. Subcanonical: `[J.toGrothendieck.Subcanonical]`. Its Yoneda functor takes
   values in sheaves of sets with the underlying representable presheaf.
   Verdict: exact; no sheafification of a nonrepresentable substitute is used.
3. Fixed base: `(T : C)`. Families over T and their augmented simplicial
   structure: `K : SimplicialObject (FormalCoproduct.{u} (Over T))`.
   Verdict: exact. Reading FormalCoproduct.Hom and its category instance shows
   the index function and each component arrow are the node's data; being in
   Over T enforces every augmentation equation. The simplicial-object source
   defines a functor from the opposite simplex category, with the stated faces.
4. Componentwise covering matching arrows, including degree zero: `hcover`.
   For target member j its source indices are exactly `{i // μ.f i = j}`.
   The equality transport after `μ.φ i.val` changes only its codomain to
   `M.obj j`; `.left` is the underlying arrow of C. Membership of the resulting
   `Presieve.ofArrows` in `J (M.obj j).left` is precisely a site covering.
   Verdict: exact covering condition, not a replacement by a sheaf epimorphism.
5. Matching targets and canonical arrows: `IsProperFaceMatchingArrow`.
   The zero branch is finality, the one branch a limiting two-member fan with
   both face equations, and the higher branch a limiting cone on the existing
   `matchingBoundaryIndex K n` with all face equations after an isomorphism.
   I read matchingBoundaryShape, matchingBoundaryIndex, and all three
   matching_object statements in SimplicialMatchingObject.lean: the pair i<j
   has arrows d_(j-1) and d_i as required. Verdict: exact boundary limit and
   canonical arrow. The existential cone and isomorphism introduce no arbitrary
   map. Every such choice is projection-compatibly isomorphic to the canonical
   limit. Site coverings are invariant under the corresponding component
   isomorphisms and bijective reindexings. Thus the universal hcover over choices
   adds no hypothesis. Limits exist: Over T has terminal object and pullbacks;
   FormalCoproducts.Basic supplies these for formal families, and finite limits
   follow. In sheaves over h_T finite limits also exist, so the conclusion's
   universal matching-arrow quantifier is not vacuous.
6. Given coproducts in C/T: `a : ∀ n, Cofan (K _⦋n⦌).obj` and
   `ha : ∀ n, IsColimit (a n)`. Verdict: exactly the individual coproducts in
   the slice, with their canonical inclusions; no arbitrary global coproduct
   instance or extra disjointness assumption.
7. Canonical coproduct maps of representable sheaves are isomorphisms:
   `hsheaf` is the colimit property of the Yoneda-image cofan with precisely
   those inclusions. Verdict: equivalent universal-property formulation of
   the canonical map, including its legs, not merely an unspecified isomorphism.
8. Constructed augmented simplicial object: `∃ A : SimplicialObject (Over T)`
   with degreewise `e n : A _⦋n⦌ ≅ (a n).pt`. The equation quantified over every
   simplex operator φ and every summand i says its map is induced from
   `(K.map φ.op).φ i`. Verdict: exact disjoint-union construction; coproduct
   uniqueness determines all maps, and slice morphisms enforce augmentation.
9. Every sheaf matching arrow is epi: the last clause uses the actual functor
   `A ⋙ Over.post J.toGrothendieck.yoneda` and `Epi μ.left`.
   I read Over.post, whose objects and maps apply the supplied functor.
   Verdict: exact epi in sheaves on C. Taking limits over h_T makes the
   degree-zero target h_T and degree-one target h_A0 ×_[h_T] h_A0.

Edge cases: no Nonempty or Fintype assumptions occur on term or fibre indices.
Empty source fibres still demand the actual empty-family covering condition;
empty cofans still require their true colimit property. Empty schemes and zero
objects, where relevant as site objects, receive no extra restriction. Degree
zero is separate, without truncated subtraction; degree one imposes no pairwise
face equation; degree two has three faces and three pair equations. All natural
numbers are covered. There is no characteristic or coefficient-ring assumption.
The site's smallness uses a single universe u, as its dependency specifies;
formal indices and sheaf values use u, the recorded semirepresentable convention.
The helper independently binds object and morphism universes u and v, so sheaf
slice categories are not forced to be small in that same universe. No variable
or universe in the file is unbound.

Independent searches used different phrases from the worker's searches:
LeanFinder via msearch.py, "Simplicial object matching morphism is epimorphic after
replacing families by coproducts of representable sheaves", returned eight hits
on split simplicial objects and unrelated epimorphism constructions, no match.
Loogle via msearch.py, `"matching"`, returned twelve unrelated name hits.
LeanSearch via msearch.py, "Coproducts of representable sheaves turn
semirepresentable hypercoverings into hypercoverings", was unavailable with
Internal Server Error; no absence verdict is inferred from that service.
Direct rg over Mathlib, upstream WeilConjectures, and project lean/Sheaf used
`hypercover.*(coprod|union)|(coprod|union).*hypercover|properfacematching`.
Mathlib provides degree-zero/one hypercover coproduct constructions and
CoproductSheafCondition, not the all-degree theorem. The project's
ProperFaceMatchingObject.lean was opened in full: it constructs the category
and diagram of all injective proper faces and proves their equivalence to the
boundary limits, but does not define the delivered matching-arrow predicate.
MatchingObjectCoskeleton.lean compares matching limits with coskeleton terms,
not this theorem or predicate. SemiRepresentableObject's canonical matching
objects/maps were inspected too: they are restricted to X.Etale, not arbitrary
sites. Thus the helper uses the shared generic boundary diagram without
introducing a second boundary construction, and no existing theorem replaces
this delivery.

No new nodes, dependency modules, or statement corrections are present.
The module and declaration docstrings name the source and blueprint id; the
statement's docstring carries each of the four proof steps with its dependency
ids. Source 0DB1 uses sheafified representable coproducts; subcanonicity gives
exactly the node's sheaf version. Working in C/T supplies finite limits from
fibre products, as the augmented discussion in 0DB2 explains; no global equalizer
hypothesis on C is missing. The helper has genuine Prop data and contains no
sorry; the only theorem proof is sorry, as stage 2 requires.

Validation: scompile.py compiled the delivered file on the server in 1.0 s,
nice 19, two threads, 60-second limit, with no warnings or errors. No local
compiler or lake build was used. I also checked that lean.statement is verbatim
the theorem signature and that all source lines are at most 100 characters.
