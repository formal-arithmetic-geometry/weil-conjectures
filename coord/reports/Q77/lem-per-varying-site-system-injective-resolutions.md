## Worker report

The delivery adds the actual category of coherent varying-site abelian-sheaf systems
and states `CategoryTheory.varyingSiteSystem_injective_resolutions`. All theorem
proofs are `sorry`; definition data are explicit. The item's natural-language
statement and proof are unchanged. Its only additional statement dependency is the
new definition node `def-per-varying-site-system`.

Sources read: Stacks `sites-cohomology.tex`, Tag 0EXZ,
`lemma-colim-sites-injective` (statement and product construction), and `derived.tex`,
Tag 013K, `lemma-injective-resolutions-exist` (3). Also read the current blueprint
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md`
and its proof. The arbitrary small-index system-category strengthening is already
explicitly agent-authored in this item's source and proof; no claim is made that
0EXZ itself states all of the strengthened conclusion.

Hypothesis and clause correspondence:

- Small index category: `{I : Type u} [SmallCategory I]`. The common chosen size
  bound is `u`, the convention of `def-weil-size-convention`; each site has objects
  in `Type u` and `SmallCategory`. This covers set-sized diagrams by choosing a
  common bound for the index and its small sites. No nonemptiness or filteredness
  instance is requested. The system objects live in the next universe, as do the
  usual sheaf objects; no smallness of the category of all sheaves is assumed.
- Sites: `D.site`, `D.category`, `D.covering`, `D.site_axioms` use the recorded
  `Precoverage.IsSiteForCoverings`, including only covering pullbacks, rather than
  requiring all site pullbacks or the obsolete composition-of-families class.
  `D.Ab i` is Mathlib's `Sheaf (D.covering i).toGrothendieck AddCommGrpCat`.
- Morphisms of sites: `D.functor a : D.site i ⥤ D.site j` is continuous and its
  set-valued inverse image preserves finite limits (`D.set_exact`). As a left
  adjoint it already preserves finite colimits. `D.pull a` is Mathlib's actual
  `Functor.sheafPullback`, not an arbitrarily supplied functor. `D.additive` and
  `D.exact_limits` express the node's exact additive abelian inverse image; its
  right-adjoint construction implies finite-colimit preservation.
- Specified identity and composition identifications and their coherence:
  `VaryingSiteCoherence.unit`, `.comp`, `.unit_left`, `.unit_right`, `.associativity`.
  The last three are component equations, with `eqToHom` for associativity/identity
  equalities of base arrows. The node supplies these identifications as data.
- Objects and transitions: `VaryingSiteSystem.obj`, `.transition`, `.identity`,
  `.cocycle`, with exactly the direction `D.pull a (F_i) ⟶ F_j`. No transition is
  required invertible. Morphisms are subtypes of component families with the
  precise square in `VaryingSiteSystem.Hom` (the node's equation with its sides
  exchanged). Category identity/composition are explicit componentwise data.
- Abelian category: the outer existential supplies `Abelian (VaryingSiteSystem D e)`;
  this is a conclusion, not a hypothesis. The additive evaluations are also
  conclusions, and provide zero-preserving evaluation on complexes.
- Componentwise kernels and cokernels: for every kernel fork / cokernel cofork,
  `Nonempty (IsLimit c)` / `Nonempty (IsColimit c)` is equivalent to the same
  universal property after every evaluation. Together with the Abelian conclusion,
  these equivalences say kernels and cokernels are computed at each vertex.
- Enough injectives: `EnoughInjectives (VaryingSiteSystem D e)` is a conclusion.
- Exact evaluation: each evaluation preserves finite limits and finite colimits.
  Injectivity preservation is `∀ F, Injective F → Injective (F.obj i)`.
- Arbitrary lower bound and complex: `∀ (b : ℤ) (K : CochainComplex ... ℤ)` with
  `∀ n, n < b → IsZero (K.X n)`. No degree-zero normalization is imposed.
- Resolution: `∃ J s` in the same system category, `IsZero (J.X n)` below the same
  `b`, injectivity of every `J.X n`, `Mono (s.f n)` at every integer, and `QuasiIso s`.
- Both final clauses are explicit: `Injective ((J.X n).obj i)` for all `i,n`, and
  `QuasiIso` of the evaluation functor's `mapHomologicalComplex` applied to `s`.
- No finite-cover, colimit-site or filteredness condition occurs anywhere.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, the recorded site interface.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`:
  `CategoryTheory.sitePullback_abelian_exact`, imported for the exact-inverse-image
  proof step. Its conclusion is the property explicitly supplied in the item's
  hypothesis; the system definition uses Mathlib's same actual inverse image.
- `Mathlib.CategoryTheory.Sites.Pullback`: `Functor.sheafPullback` and its
  `sheafAdjunctionContinuous`; continuous pushforward is its actual right adjoint.
- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`, the exact match
  recorded for `def-sp-abelian`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective`, `EnoughInjectives`, and `InjectiveResolution` (the latter read for the
  dependency's notion; the result uses the integer complex formulation explicitly).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the imported complex/quasi-isomorphism notions from
  `def-weil-abstract-derived-category`. The theorem concerns actual complexes and
  `QuasiIso`, so needs no localization-size assumption.
- Proof imports: Mathlib Grothendieck-category `EnoughInjectives`, sheaf AB axioms
  (including `Sheaf.hasExactColimitsOfShape`),
  `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono` with
  `CochainComplex.exists_mono_quasiIso_injective_boundedBelow`, and
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` with
  `Functor.preservesHomologyOfExact`. Right-adjoint injectivity, injectivity of
  products, and exact sheafification come through their Mathlib modules.
  `lem-per-varying-site-evaluation-adjoints` has no current Lean record or Mathlib
  match and is only a proof dependency: it is named in the complete proof docstring,
  not imported through an invented module. None of its constructions is assumed in
  the theorem signature.

Edge cases checked before writing: empty `I` (one empty family and one map; zero
category), one vertex with identity transition (ordinary abelian sheaves), discrete
index sets (products of sheaf categories), nontrivial endomorphisms (cocycle laws
remain present), empty sites, zero sheaves, zero complexes, and arbitrary negative,
zero or positive lower bounds. Noninvertible transitions remain allowed. Mono and
zero assertions are categorical, not sectionwise surjectivity claims. The fork
reflection clauses remain correct for the empty index.

Searches performed with `msearch.py`:

- LeanFinder: "Varying site systems of abelian sheaves category sections
  contravariant pseudofunctor enough injectives": 8 hits, ordinary sheaf
  Grothendieck and cohomology declarations, no system category or theorem.
- Loogle: `CategoryTheory.Pseudofunctor, CategoryTheory.Functor`: 12 hits for
  pseudofunctor conversions and object-property restrictions, no system category.
- LeanSearch: "Category of compatible families of abelian sheaves with
  noninvertible inverse image transition maps for a coherent diagram of sites":
  8 hits for ordinary sheaf categories and compatible elements, no exact match.
- Mathlib grep `([Vv]arying|[Ll]ax[Ss]ection|[Ss]heaf[Ss]ystem|[Ss]ection[Cc]ategory)`
  in CategoryTheory: one unrelated comment in filtered colimits. Targeted grep
  `VaryingSiteDiagram|VaryingSiteSystem|LaxSection|laxSection`: zero hits.
- `rg` through the project's `lean/WeilConjectures` and `lean/Sheaf`, including
  `VaryingSite`, `SystemCategory`, `CoefficientSystem`, and structure/section
  patterns: coefficient towers are for a fixed site and are not this notion.
  Read `TotalSitePseudofunctor` (its total site is a different construction) and
  `SystemLevelLeftExtensionBasic` (fixed-site scalar restriction, not this notion).
  Exact searches for the chosen declaration names gave no match. The upstream
  search for this item's blueprint id gave no match.
- DAG grep for varying-site systems found this item and its as-yet-unstated
  evaluation-adjoint proof lemma, no definition node.
  `tools/blueprint_refs.py search 'varying site'` and `search 'system category'`
  both returned zero blueprint nodes; `ancestor` returned
  `lem-per-artin-gabber-affine-curve`. Exact JSON search logs are in the new node.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py` against the server's live published build, with no errors or warnings.
The definitions contain no `sorry` data. Three named elementary category-law
obligations are postponed in the definition node's module, each with its full
proof docstring; their assertions are the identity/composition and category-law
clauses of that same node. The item's single theorem is also postponed.

## New nodes

`def-per-varying-site-system` introduces exactly the coherent diagram and compatible
families required by the item, with their category and evaluations. Its source is
Stacks Tag 0EXZ, `lemma-colim-sites-injective`, system data and maps, with the
already specified arbitrary-small-index generalization of the item. Mathlib's
`Sheaf`, continuous pushforward and actual `sheafPullback` are reused. The site
axioms are the recorded project declaration. New declarations supply only the
missing coherent system interface, and component operations are real data. The
identity/composition proof obligations carry docstrings and are recorded in
`lean.declarations`; the new node states those laws. Searches above found no
existing node or declaration for this notion. No unit statement or existing
statement is corrected.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
