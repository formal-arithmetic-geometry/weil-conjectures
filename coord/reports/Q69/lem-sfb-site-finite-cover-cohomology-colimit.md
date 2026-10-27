## Worker report

The module `Sheaf.CategoryTheory.SiteFiniteCoverCohomologyColimit` states
`CategoryTheory.Sheaf.isIso_cohomology_colimit_of_finite_covers`, with its proof
`sorry`. No definition or proof is introduced. The natural-language statement and
the reviewed four-step proof are unchanged.

The current stage-2 handoff in `coord/brief-stage2.md` §0 resolves the previous
worker's stale-dispatch ending: this node is reviewed at stage 1, is queued for
stage 2, and has no Lean record or released repair note. Stage 2 therefore proceeds
on the accepted split; it does not resplit the node.

Clause-by-clause correspondence:

- A small site is `{C : Type u} [SmallCategory C]`, `J : Precoverage C`, and
  `hJ : J.IsSiteForCoverings`. This uses the actual recorded covering-site axioms,
  including only existence of pullbacks along covering arrows. It does not replace
  them by the stronger `IsStableUnderComposition` interface.
- Abelian sheaves are `Sheaf J.toGrothendieck AddCommGrpCat.{u}`, the coefficient
  category specified in the dependency record. `HasSheafify` is the standard
  small-site infrastructure. `HasExt.{u}` chooses the small cohomology universe;
  its existence follows from enough injectives and local smallness, by
  `CategoryTheory.hasExt_of_enoughInjectives`. It adds no mathematical hypothesis.
- The collection of objects is `B : Set C`. The selected covering families are
  `Cov V T W f`, a predicate on a target, index type, members, and arrows. This is
  the same family representation used by the existing site Cech criterion.
- That every selected family is a covering is `hcover`, namely
  `Presieve.ofArrows W f ∈ J V`.
- Finiteness of every selected index set is `hfinite`, with conclusion `Finite T`.
  There is no nonemptiness restriction on a covering index type.
- `hB` asserts the target `V ∈ B`, every member `W t ∈ B`, and every iterated
  overlap `(S V T W f h).W p a ∈ B`.
- `S` uses the existing `SiteCechComplex W f` to specify choices of actual fibre
  products, including projections and universal properties, rather than an
  unrelated family of objects. `p : ℕ` and `a : Fin (p+1) → T` describe exactly
  one or more factors. The tuple may repeat an index. There is no requirement that
  an overlap have nonempty underlying space, and there is no empty product.
  These are choices of the products already required by the statement and site
  axioms, not an extra existence hypothesis on unrelated products.
- Cofinality is `hcofinal`: for every covering of `V ∈ B`, it produces a selected
  family `Cov V K Z g`. Its last clause gives, for each `k`, an original member
  `t` and arrow `a : Z k ⟶ W t` satisfying `a ≫ f t = g k`. This is precisely
  refinement by factorization, not a subfamily requirement.
- The small filtered category is `(D : Type u) [SmallCategory D] [IsFiltered D]`.
  `IsFiltered` includes nonemptiness, common successors and equalization of
  parallel arrows, equivalently cocones on finite diagrams. The index and
  coefficients use the same universe, following the standing size convention.
- The diagram is `F : D ⥤ Sheaf J.toGrothendieck AddCommGrpCat.{u}`; the object
  and degree are `(U : C) (hU : U ∈ B) (q : ℕ)`. Thus every nonnegative degree,
  including zero, is covered.
- The functor `cohomologyPresheafFunctor J.toGrothendieck q` followed by
  evaluation at `op U` is the recorded object cohomology `H' (-) q U`.
- The conclusion is `IsIso (colimit.post F (...))`. Mathlib defines
  `colimit.post F G` as `colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))`;
  its source is `colimit (F ⋙ G)` and target `G.obj (colimit F)`.
  `colimit.ι_post` identifies every composite with `G.map (colimit.ι F d)`.
  Consequently this is the precise map in the node induced by the sheaf colimit
  coprojections, not an arbitrary isomorphism or a noncanonical bijection.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, for
  `def-weil-pbc-sites-and-cohomology`. Its docstring explicitly retains Mathlib
  `Sheaf`, `Sheaf.H'` and `cohomologyPresheafFunctor` for the remaining components.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor` and `Sheaf.H'`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `Cocone`, `IsColimit`,
  `colimit.desc` and `colimit.post`, for `def-weil-pbc-category-colimit`.
  `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsFiltered`.
- `WeilConjectures.CategoryTheory.SiteCechComplex`:
  `CategoryTheory.SiteCechComplex`, especially fields `W`, `pr`, `comm`,
  `universal`, `W_zero`, `pr_zero`, `indexMap` and `indexMap_pr`.
  Its existing node `def-weil-pbc-site-cech-complex` is added to `stmt_deps`,
  as allowed for landed dependencies; this was already a proof dependency.

All currently stated proof dependencies are imported: the existing Cech complex,
`site_injective_cech_acyclic`, `Sheaf.isZero_H'_of_siteCech_vanishing`, and
`Functor.preservesColimitsOfShape_rightDerived_succ`; the Mathlib filtered-colimit
finite-limit theorem, abelian-group AB5, sheaf Grothendieck and exact-colimit
instances, and `Precoverage.isSheaf_toGrothendieck_iff` are available from their
recorded modules. The not-yet-stated
`lem-sfb-site-quasi-compact-section-colimit` has no module to import.
The existing Cech proof interfaces still use stronger historical precoverage
classes; this statement uses the current recorded site interface without assuming
those classes. No proof-interface repair is needed to state the item.

Source checked: `literature/stacks-project/sites-cohomology.tex`,
`lemma-colim-works-over-collection` (Tag 0739), full statement and proof. It matches
both finite cofinal coverings and all iterated overlaps. The docstring contains
all four accepted DAG proof steps and names their inputs.

Edge cases checked before writing: empty `B` gives no object to which the
conclusion must apply; an empty selected covering is allowed (`Finite Empty`),
with no positive-length tuples; repeated factors are allowed; the empty product
is not required. A one-object filtered diagram is allowed and its comparison is
the usual identity comparison. Degree zero, zero sheaves, non-injective transition
maps, and parallel arrows in `D` are retained. No terminal object, global finite
products, torsion condition, or assumption that injective colimits are injective
is added.

Searches (via `msearch.py`, with results retained in `searches.jsonl`):

- LeanFinder: “Cohomology over a basis object of a site with cofinal finite coverings
  closed under iterated fibre products commutes with filtered colimits of abelian
  sheaves”: eight hits, including `Sheaf.ab5ofSize`, existence of filtered colimits,
  and `cohomologyPresheafFunctor`; none asserts this preservation theorem.
- LeanFinder: “Higher derived sections on coherent sites preserve filtered
  colimits”: eight hits on AB5, colimit existence and condensed objects; no match.
- Loogle: `CategoryTheory.Sheaf.H, CategoryTheory.Limits.colimitComparison`:
  zero hits (the guessed second identifier is unknown). A corrected query,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`, finds the exact bifunctor used.
- Mathlib grep: `cohomology.*colimit|colimit.*cohomology|H.*preservesColimits`,
  restricted to `CategoryTheory/Sites`: five hits, on point functors, nonabelian
  H1 and subcanonical topology, not the statement here.
- Project `rg` with the same pattern in `lean/WeilConjectures` and `lean/Sheaf`
  found specialized topological and etale continuity statements and
  `WeilConjectures.CategoryTheory.Sites.CohomologyFilteredColimit`.
  That module's full `H_map_isColimit_of_isFiltered_small` signature and docstring
  were read: it assumes a terminal object and finite products in every slice and
  describes global `H` elementwise. It does not state this general `H'` theorem
  under covering-pullback-only site axioms, so it cannot be an existing attachment.
- `rg` for this node id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no existing declaration for the node.

Validation: `scompile.py Q69 lem-sfb-site-finite-cover-cohomology-colimit` compiled
both its sandbox form and its actual library module form cleanly (3.9 s and
4.9 s). No diagnostic commands, extra axioms, or definition placeholders remain.

No statement correction, new node, dependency-module repair, or unresolved
statement dispute is present. The only additional statement dependency is the
already recorded and landed Cech-complex definition.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
