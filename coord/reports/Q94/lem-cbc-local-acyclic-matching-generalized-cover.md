## Worker report

Item: lem-cbc-local-acyclic-matching-generalized-cover. Q94, stage 2, 2026-10-17.

The new module Sheaf.CategoryTheory.LocalAcyclicMatchingGeneralizedCover states
CategoryTheory.LocalSimplicialPresheaf.local_acyclic_matching_generalized_cover,
with one postponed theorem and explicit canonical constructions. No mathematical
statement was corrected. The node gains the already landed statement dependency
def-cbc-local-simplicial-presheaf-maps, whose definitions are reused verbatim.
There are no new nodes or dependency repairs.

Hypotheses and clauses, in the order of the node:

- A small category and its covering-sieve topology are `{C : Type u}
  [SmallCategory C] (J : GrothendieckTopology C)`. Mathlib's topology contains
  maximal-sieve, pullback-stability and transitivity axioms; no fibre products,
  subcanonical condition, points, or choice of covering basis is assumed.
- The size convention is explicit `universe u w`, with simplicial values and
  set-valued presheaves in `max u w`. Thus the coefficient universe is at least
  the site universe, with arbitrary extra enlargement and no equality imposed.
- `F G : Cᵒᵖ ⥤ SSet.{max u w}` are the given simplicial presheaves.
  `SSet` is the recorded simplicial-set definition, the functor category on
  SimplexCategoryᵒᵖ; its operators and morphisms are the original ones.
- `(hF : ∀ V : C, SSet.KanComplex (F.obj (op V)))` and the parallel `hG`
  express precisely both objectwise Kan assumptions, at every object.
- `(f : F ⟶ G)` is the given natural transformation.
- `(hf : IsLocalKanFibration J f)` uses the existing horn definition from
  Sheaf.CategoryTheory.LocalSimplicialPresheafMaps. In that definition, n+1
  ranges over all positive horn dimensions, i : Fin (n+2) over all horns;
  restrictions to a covering sieve have strict fillers, independently chosen.
  Yoneda identifies its objectwise squares with the representable-product
  squares in the item. No objectwise fibration is substituted.
- `(hw : IsLocalWeakEquivalence J f)` uses the same module's existing definition.
  Its first clause applies Mathlib's presheafToSheaf to the actual π₀ map.
  Its remaining clauses express local surjectivity and local injectivity on
  positive pointed homotopy classes. Quantification over every object and
  basepoint includes each restriction in every slice C/V. The induced slice
  topology declares a sieve covering exactly when the underlying sieve covers
  its domain in C; the two local criteria are therefore precisely the stated
  isomorphisms of associated homotopy sheaves. The naturality equality of
  basepoints is retained by HEq; homotopic basepoints are not conflated.
- `(n : ℕ)` includes every nonnegative degree.
- `degreePresheaf F n` is F followed by actual evaluation at op [n], so its
  values are F(V)_n, rather than an unrelated isomorphic object.
- `boundaryPresheaf F n` is F followed by coyoneda on the actual boundary
  `SSet.boundary n`. Its values are exactly simplicial maps ∂Δ[n] → F(V),
  and its restriction maps are postcomposition with the restrictions of F.
  Mathlib defines the boundary by nonsurjective operators and proves that
  it is the union of proper faces; the simplex is its standard representable.
- `boundaryRestriction F n` sends x to the boundary inclusion composed with
  `SSet.yonedaEquiv.symm x`, the simplex represented by x.
- `boundaryPresheafMap f n` is whiskering f with that coyoneda functor;
  it acts by postcomposition with f_V on boundary maps.
- `relativeBoundaryMatchingMap f n` is the canonical `pullback.lift` from
  `degreePresheaf F n` into the presheaf pullback of `boundaryPresheafMap f n`
  and `boundaryRestriction G n`. Its first projection is boundary restriction,
  and its second is the actual nth component of f. The commutativity witness
  uses Yoneda naturality and contains no postponed proof or arbitrary choice.
- `Presheaf.IsLocallySurjective J (relativeBoundaryMatchingMap f n)` is precisely
  the recorded generalized-cover notion. Mathlib's imageSieve requires local
  preimages of every target section along every arrow of a covering sieve;
  it imposes no compatibility of distinct preimages.
- In degree zero, Mathlib's `boundary_zero` says the boundary is bottom.
  Maps from it are unique, so the pullback is canonically G_0 and the matching
  map is f_0. No degree-zero case is removed or separately assumed.

The five canonical helpers belong to the matching-map notion introduced in
this very item. Each is listed in lean.declarations, carries this item's source
and blueprint docstring, and has real data. No independent missing notion is
introduced. The sole theorem has a proof docstring following all five node
steps, including the finite prism filtration, horn-by-horn refinements, and
covering-sieve transitivity. The homotopy-lifting proof dependency currently
has no Lean record, so there is no recorded proof module to import. It is
referenced by its node id in the proof docstring, without adding a second
postponed theorem or assuming it as a hypothesis.

Dependency declarations read and used:

- def-weil-size-convention is explicitly a metatheoretic convention, not a
  Lean definiendum; explicit universes implement it.
- Mathlib.CategoryTheory.Sites.Sheafification: CategoryTheory.presheafToSheaf,
  toSheafify and sheafificationAdjunction were read. The first is used inside
  the imported local weak equivalence; its adjunction is the specified
  associated-sheaf construction, not an arbitrary replacement.
- Mathlib.AlgebraicTopology.SimplicialSet.Basic: SSet. The recorded auxiliary
  degenerate/nonDegenerate, Subcomplex, and Finite declarations were also read.
- Mathlib.CategoryTheory.Sites.LocallySurjective:
  CategoryTheory.Presheaf.IsLocallySurjective, with imageSieve read in full.
- Sheaf.CategoryTheory.LocalSimplicialPresheafMaps:
  CategoryTheory.LocalSimplicialPresheaf.IsLocalKanFibration and
  IsLocalWeakEquivalence (and their Pi and piMap constructions). The published
  module was also fetched through scompile.py --source and agrees with the
  shared source. This landed definition node is added to stmt_deps as allowed
  by brief-stage2 section 5.

Edge cases checked before writing: n=0 (empty boundary and f_0); n=1
(two-vertex boundary); empty site (all local assertions vacuous); empty Kan
values (no basepoints to quantify over, while π₀ and local surjectivity still
retain their genuine content); trivial and maximal Grothendieck topologies
(the same sieve predicates apply); arbitrary extra coefficient-universe
size w. No nonemptiness, finiteness, or objectwise surjectivity assumption was
introduced.

Searches performed:

- msearch.py leanfinder: "Relative matching maps of a local acyclic fibration
  of simplicial presheaves are locally surjective" returned eight declarations
  about ordinary local surjectivity; none states this simplicial theorem.
- msearch.py loogle: "CategoryTheory.Presheaf.IsLocallySurjective,
  SSet.yonedaEquiv" returned zero hits.
- msearch.py grep: "local.*[Ff]ibration|relativeMatching" in
  AlgebraicTopology/SimplicialSet returned zero hits.
- msearch.py leansearch: "local acyclic fibration simplicial presheaves
  relative matching maps generalized cover" returned ordinary simplicial
  fibrations, site matching families, and abstract model-category lifting,
  not the local simplicial-presheaf theorem.
- rg in the upstream WeilConjectures tree for the item id and local-fibration /
  matching terminology found no declaration of this result.
- rg in lean/Sheaf found the usable LocalSimplicialPresheafMaps definition
  and the downstream HypercoverRelativeLifting statement. The latter cites
  this item in its proof and is not an existing proof or statement of it.
- rg for the six proposed declaration names in Mathlib/source-facing records,
  lean/Sheaf, and dag/lean_names_upstream.json found no conflicting names.
  Existing generic Reedy relative-matching arrows use arbitrary matching
  diagrams; none defines this boundary-map presheaf and its canonical map.

Source checked directly: DHI, arXiv:math/0205027v2, Section 3,
https://arxiv.org/html/math/0205027v2#S3 . Proposition 3.2 and equation (3.4)
identify precisely the generalized-cover conclusion. No statement dispute.

The earlier BLOCKED report confused a stage-1 merge by Q17 with stage-2
completion: the current item has no lean field. This delivery adds an actual
Lean statement and its record, rather than resubmitting an unchanged node.

Validation is through the prescribed scompile.py file-only wrapper and
`deliver2.py Q94 lem-cbc-local-acyclic-matching-generalized-cover --no-push`.
The final tool output is the dry-run acceptance record. Nothing is pushed;
the independent second reader writes the second-reading section.

## Second reading by Q94

I read the node statement clause by clause against the Lean module and DHI Section 3 (Proposition 3.2 and equation (3.4), arXiv:math/0205027v2). The site is rendered by `{C : Type u} [SmallCategory C]` and `J : GrothendieckTopology C`; no subcanonical, point, fibre-product, or basis hypothesis is added. The explicit universes `u w` and coefficient universe `max u w` implement the size convention without identifying the universes. The objects `F G : Cᵒᵖ ⥤ SSet.{max u w}`, objectwise Kan hypotheses `hF` and `hG`, natural transformation `f`, local Kan fibration hypothesis `hf`, local weak equivalence hypothesis `hw`, and arbitrary degree `n : ℕ` all appear in the same order and with the same scope as the node.

The presheaf clauses are rendered by `degreePresheaf` (evaluation at `[n]`), `boundaryPresheaf` (maps from the actual `SSet.boundary n`), `boundaryRestriction`, and `boundaryPresheafMap`. `relativeBoundaryMatchingMap` is the canonical pullback lift with those two projections, so its codomain is exactly the node's `\widetilde M_nF ×_{\widetilde M_nG} G_n`. The conclusion is `Presheaf.IsLocallySurjective J (...)`, Mathlib's image-sieve generalized-cover predicate; its definition requires a covering lifting sieve for every target section and imposes no compatibility between lifts. Thus it matches `def-cbc-generalized-cover`. The theorem's docstring records the node proof steps (Yoneda identification, homotopy lift, finite prism horn filtration, sieve refinement and transitivity), while the theorem remains postponed with `sorry`.

I checked the source's local-fibration definition: all positive horn dimensions and all horn indices are covered by `n + 1` and `Fin (n + 2)` in `IsLocalKanFibration`; the fillers are independently quantified over arrows of a covering sieve. The local weak-equivalence definition is the imported `IsLocalWeakEquivalence`, whose clauses are the sheafified component isomorphism and local positive homotopy surjectivity/injectivity on every slice. No objectwise fibration or extra finiteness assumption is present. DHI's generalized-cover definition at lines 215--221 and the matching map at lines 217--221 agree with the Lean conclusion.

Edge cases checked are `n = 0` (the boundary is bottom and the matching map reduces to degree-zero `f`), `n = 1` (the two-vertex boundary), empty site, empty Kan values, trivial and maximal topologies, and arbitrary extra universe `w`; none is excluded by the binders.

Searches were rechecked with `msearch.py` LeanFinder, Loogle, LeanSearch and grep over Mathlib, the upstream `WeilConjectures` tree, and `lean/Sheaf`. They found only ordinary `IsLocallySurjective`, generic simplicial matching constructions, and the imported local-map definitions; no declaration of this theorem or its boundary matching construction exists. The exact imported dependency `Sheaf.CategoryTheory.LocalSimplicialPresheafMaps` was read and its four declarations are reused. The source URL was opened directly and confirms Proposition 3.2 and (3.4).

One metadata mismatch was found and repaired: the item node had `lean: null` even though the module supplied the theorem and five canonical helpers, and it omitted the landed `def-cbc-local-simplicial-presheaf-maps` statement dependency used by `hf` and `hw`. I added the complete `lean` record (including the exact theorem signature and declaration list) and added that dependency to `stmt_deps`. The mathematical statement, source, proof data, and all other node fields remain unchanged. There is no statement correction and no new definition or dependency repair.
