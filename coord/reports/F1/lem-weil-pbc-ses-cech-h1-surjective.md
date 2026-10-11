## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1`.
Declaration: `AlgebraicGeometry.Scheme.surjective_sections_of_cech_h1_vanishing`.
It states the node, with a single `sorry`; it introduces no new definition and proves nothing.
The node copy changes only `lean`.

Source read: Stacks Project, Lemma 03F8, statement and proof,
https://stacks.math.columbia.edu/tag/03F8 . The literature checkout is absent on this machine;
the official source was opened directly. The node agrees with that lemma specialized to
the small étale site. The module docstring gives the node's six-step proof, with its
sectionwise-kernel and local-surjectivity dependencies named.

Hypothesis and clause correspondence:

- The scheme is `(X : Scheme.{u})`, with no finiteness, separation, or characteristic assumption.
- Its small étale site is the category `X.Etale` and topology `X.smallEtaleTopology`.
- Abelian sheaves are `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The sequence `0 → F → G → H → 0` is `S : ShortComplex (...)` with `hS : S.ShortExact`.
  Its three sheaves are `S.X₁`, `S.X₂`, `S.X₃`; its maps are `S.f` and `S.g`.
  `ShortExact` means exactness, a monomorphism at the left, and an epimorphism at the right.
- The object of the site is `(U : X.Etale)`.
- The system Σ is its membership predicate `Cov I V f` on arbitrary indexed families
  `f : ∀ i : I, V i ⟶ U`. This is the same encoding used by the landed sibling
  `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion`; it does not assume a finite system
  or finite covering families. All data live in fixed universes, hence form a set.
- Every member is a covering by `hcover`, namely `Sieve.ofArrows V f ∈ X.smallEtaleTopology U`.
  Mathlib's `Scheme.ofArrows_mem_smallEtaleTopology_iff` identifies this with joint surjectivity.
- Cofinality is `hcofinal`: every covering `f` has a family `g` satisfying `Cov K W g`;
  for each `k` there is `i` and `t : W k ⟶ V i` with `t ≫ f i = g k`, exactly the
  refinement-over-U clause. No requirement of a unique refinement or a surjective index map.
- Čech H¹ vanishing is `hcech`: the homology in degree `1` of the recorded
  `cechComplexFunctor` is `IsZero`. The complex is formed from `Over.mk (f i)` in `Over U`
  and applied to `(Over.forget U).op ⋙ S.X₁.obj`; therefore its products are fibre products
  over U and its coefficients are the kernel sheaf F. This is the recorded dependency's
  specialization, not a new Čech construction. `IsZero` is on an abelian-group object,
  not a bare type.
- The conclusion is `Function.Surjective (S.g.hom.app (op U))`: surjectivity of the map
  `G(U) → H(U)` on underlying elements, rather than only an epimorphism of sheaves.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Scheme.Etale`, with finite limits.
  Both are supplied by the used import `Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
  which also supplies the abelian sheaf-category structures.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` (the full subcategory of
  presheaves satisfying the topology's sheaf condition).
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`: `CategoryTheory.cechComplexFunctor`.
  Its docstring and full signature were read; it takes products of evaluations over tuples.
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Products` supplies the local finite
  products instance on `Over U`, as in the landed Čech siblings.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: `ShortComplex.ShortExact`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`: `HomologicalComplex.homology`.

Edge cases checked before writing:

- Empty covering indices are allowed: no `Nonempty` or `Fintype` binder occurs. An empty
  covering can cover only the empty étale object, on which an abelian sheaf has zero sections,
  so the conclusion remains true.
- The empty scheme and zero sheaves are included; no extra nonemptiness assumption occurs.
- An empty Σ fails cofinality, since the identity covering of U exists; the formulation does
  not accidentally make cofinality vacuous.
- Infinite coverings are admitted (`I : Type (u + 1)`) and use the full product Čech complex.
- The universe convention matches the site's objects and the landed sibling criterion;
  all schemes X and all sheaves in the project's standard abelian étale-sheaf encoding occur.
- Only degree one vanishes, with no assumption on other Čech degrees or on intersections.

Searches for an existing statement (actual service calls logged in `searches.jsonl`):

- LeanFinder: "short exact sequence of abelian sheaves with vanishing first Cech cohomology
  on cofinal coverings implies surjectivity on sections". Eight hits: local surjectivity,
  Mayer–Vietoris, concrete short exact sequences, and topological stalk results; no site
  Čech H¹/cofinal-system section-lifting theorem.
- Loogle: `CategoryTheory.cechComplexFunctor`. The expected existing definition was found;
  it is used, not copied.
- msearch grep: `cech.*surject|surject.*cech|structure.*(Cover|Hypercover)|def.*Refine`
  in `CategoryTheory/Sites`. Hypercover/refinement infrastructure and no theorem matching
  this statement. No new covering/refinement notion is needed: it is expressed inline.
- LeanSearch: "short exact sequence of abelian sheaves vanishing first Cech cohomology
  implies surjective sections". Service unavailable (Internal Server Error); no verdict
  inferred from that unavailable search.
- rg of `WeilConjectures` for the item id and Čech/surjectivity names: no item-id declaration.
  `TopCat.Presheaf.surjective_app_of_exactAt_cechComplex_one` and
  `TopCat.Sheaf.surjective_app_of_exactAt_cechComplex` are finite topological-open-cover
  statements; the affine-scheme analogues specialize them. They do not state the étale-site
  result here. The node's split report independently records this distinction.
- rg of `lean/Sheaf`: the sibling étale criterion cites this item in its proof, and the
  injective-sheaf Čech-acyclic theorem uses the same existing Čech specialization;
  neither states the requested short-exact-sequence result.
- rg of Mathlib, upstream sources, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  proposed full declaration's last component: no name collision.

No statement fault, correction, or disputed statement was found. No new nodes or dependency
modules were required. Compilation is performed solely by `scompile.py` on the server.

## Second reading by F1

I read `dag/nodes/sec-proper-base-change/lem-weil-pbc-ses-cech-h1-surjective.json`, the
Stacks Project source at Lemma 03F8, and the Lean declaration
`AlgebraicGeometry.Scheme.surjective_sections_of_cech_h1_vanishing` item by item.

- The scheme `X` is rendered by `(X : Scheme.{u})`; no finiteness, separation,
  characteristic, or nonemptiness assumptions are added.
- The small étale site is rendered by `X.Etale` and `X.smallEtaleTopology`; the
  sheaf category is `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The short exact sequence `0 → F → G → H → 0` is rendered by
  `S : ShortComplex (...)` and `hS : S.ShortExact`; its kernel, middle, and
  quotient sheaves are exactly `S.X₁`, `S.X₂`, and `S.X₃`, with maps `S.f` and
  `S.g`.
- The object `U` is `(U : X.Etale)`. The cofinal system Σ is represented by the
  predicate `Cov` on arbitrary indexed families over `U`; `hcover` says every
  member is a covering, and `hcofinal` gives exactly the source's refinement
  maps over `U`, with the same quantifier order.
- `hcech` requires `IsZero` of degree-one homology of Mathlib's
  `cechComplexFunctor` applied to the restriction of `S.X₁` along `Over U`; this
  is the recorded Čech-complex dependency and therefore uses the kernel sheaf
  and fibre products over `U`. It applies to every `Cov` member and imposes no
  extra finiteness condition.
- The conclusion is exactly `Function.Surjective (S.g.hom.app (op U))`, hence
  surjectivity on sections of `G` to sections of `H`.

Edge cases were checked: empty index types are permitted; no `Nonempty` or
`Fintype` hypothesis is present; zero sheaves and the empty scheme are allowed;
`n = 0` is not asserted (only degree one vanishing); arbitrary/infinite covering
families are allowed; and the universe `Type (u + 1)` matches the étale-site
encoding used by the dependency and compiles without unbound variables.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` using LeanFinder,
Loogle, LeanSearch, and `rg` for the theorem and for alternative Čech,
cofinality, and surjectivity declarations. Mathlib provides only
`CategoryTheory.cechComplexFunctor`; the source repository has finite
TopCat analogues but no small-étale theorem. No existing declaration matches,
and no new definition or dependency module is needed.

No mismatch was found. The worker module already renders the node verbatim,
contains only the required `sorry` proof, and compiled cleanly with
`scompile.py`; no changes were required in the Lean statement or node fields.
