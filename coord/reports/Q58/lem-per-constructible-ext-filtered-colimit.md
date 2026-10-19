## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit` states
`AlgebraicGeometry.Etale.isIso_sheafExt_filteredColimit`. Its only theorem has proof
`sorry`. The helper `sheafExtCoefficientFunctor` has real functor data: the composite of
`DerivedCategory.singleFunctor _ 0`, the recorded `Etale.derivedHom` at `op K`, and
`DerivedCategory.homologyFunctor _ n`. It introduces no alternative derived-Hom construction.

Source checked directly: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
PDF page 331, printed p. 325, Expose XVII Proposition 10.1.1, first proof paragraph.
It explicitly asserts filtered-inductive-limit continuity of Ext^q(X,-) for X in D_c^-.
The additional assumptions concerning Y and the tensor comparison in the proposition are
not assumptions of this intermediate assertion. The eight-step proof of this node is
included in the theorem docstring, including simultaneous injectivity before the five lemma,
sheafification on the affine etale basis, and the finite truncation window for fixed n.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| X is a scheme | `(X : Scheme.{u})` |
| X has a finite affine cover with Noetherian coordinate rings | `[IsNoetherian X]`; Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` gives exactly this equivalent definition |
| A is a commutative Noetherian ring | `(A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]` |
| Ordinary derived category of A-module sheaves on the small etale site | `(K : DerivedCategoryModule A X)`, the recorded abbreviation for `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))` |
| Cohomology vanishes above some integer r | `_hbounded : ∃ r : ℤ, ∀ j : ℤ, r < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj K)` |
| Each cohomology sheaf has a finite locally closed stratification | `_hconstructible : ∀ j : ℤ, ∃ S : Scheme.FiniteLocallyClosedStratification X, ...`; S records all subsets, finite partition, immersed stratum schemes, and their image equalities |
| Restrictions to every stratum are locally constant with finite-type A-module stalks | `∀ i : Fin S.n, Scheme.IsFiniteLocallyConstantSheaf ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj ((DerivedCategory.homologyFunctor _ j).obj K))` |
| Every integer n | `(n : ℤ)`, with no sign restriction |
| Every small filtered diagram of module sheaves | `{J : Type (u + 1)} [SmallCategory J] [IsFiltered J] (G : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))` |
| Ext^n(K,G) is H^n RHom(K,G[0]) | `sheafExtCoefficientFunctor X A K n`, with the degree-zero single functor and ordinary etale internal Hom |
| Canonical map from colimit of Ext to Ext of colimit | `colimit.post G (sheafExtCoefficientFunctor X A K n)` |
| Isomorphism in module sheaves | `IsIso` of that map, whose domain and codomain are the actual module-sheaf objects |

`colimit.post` is defined by `colimit.desc` on the image of the chosen colimit cocone.
Its equation `colimit.ι_post` identifies each leg with Ext applied to `colimit.ι G i`.
Thus the statement is about the specified comparison, not the existence of an unspecified
isomorphism. No extra map, closed-structure assumption, representative, resolution, Tor bound,
or lower cohomology bound is quantified.

Dependency declarations used (the recorded modules are publicly imported):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `Scheme.smallEtaleTopology`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  exposing `Etale.DerivedCategoryModule`, `DerivedCategory.singleFunctor`, and
  `DerivedCategory.homologyFunctor`. The current module was read through
  `scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategories`, since the older
  slopmaster2 checkout does not contain that source module.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `constantSheaf`.
  The ModuleCat-valued sheaf encoding is the recorded fixed-coefficient presentation of
  modules over the constant sheaf; no new ring-sheaf encoding is introduced.
- `def-constructible-stratification`:
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `Scheme.FiniteLocallyClosedStratification`, used directly in the hypothesis.
- `def-weil-pbc-locally-constant-finite-type-modules`:
  `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`, exposing the dependency's
  already recorded `Scheme.IsFiniteLocallyConstantSheaf` etale specialization.
  The generic equal-universe `SheafOfModules.IsLocallyConstantFiniteTypeModules` does not
  apply to the small etale category; the existing dependency record already documents
  and exposes the appropriate specialization, so no dependency repair is necessary.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
  `IsFiniteLocallyConstantSheaf` extends local constancy and `IsFiniteSheaf`; the latter
  is finite generation at every geometric stalk, equivalent to `Module.Finite` for modules.
  It does not require finite underlying stalk sets for arbitrary Noetherian A.
- `def-weil-size-convention`: universe u for schemes and u+1 for coefficients, sheaf values,
  homs, and small diagram indices; u+2 for derived-category objects. This is the recorded
  convention, not an additional Lean object or assumption. The small etale site's object
  and arrow universes are not identified.
- `def-pur-derived-internal-hom`:
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, exposing the already recorded
  `AlgebraicGeometry.Etale.derivedHom`. The generic definition remains imported unchanged;
  the etale specialization supplies the ordinary fixed-coefficient internal Hom.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `colimit`, `colimit.post`, `colimit.ι`, `colimit.desc`, and `CategoryTheory.IsFiltered`.

Every stated proof dependency's recorded module is imported non-publicly unless already
publicly imported as a statement dependency. `lem-per-noetherian-constructible-flat-lifting`
has no Lean record yet; there is no module to import. It is a proof-only dependency and is
named in the proof docstring. No statement dependency is missing or repaired.

Searches for an existing declaration:

- `msearch.py ... leansearch "Sheaf Ext from bounded above constructible etale complexes
  commutes with filtered colimits"`: eight hits, including `Sheaf.ab5ofSize`,
  `Sheaf.hasFilteredColimitsOfSize`, `Point.sheafFiber` colimit preservation, module-sheaf
  colimits, and `Sheaf.isColimitSheafifyCocone`; no constructible internal-Ext theorem.
- `msearch.py ... leanfinder "Derived internal Hom from a bounded above constructible etale
  complex commutes with filtered colimits of sheaves"`: eight hits, including light-condensed
  internal Hom, `Sheaf.H`, and `Sheaf.cohomologyPresheafFunctor`; no matching theorem.
- `msearch.py ... loogle "CategoryTheory.Limits.colimitComparison"`: no hits, unknown identifier.
  Direct source inspection found the canonical map under its actual name `colimit.post`.
- `msearch.py ... grep "Ext.*[Cc]olimit|[Cc]olimit.*Ext" Algebra/Homology`: 25 generic hits
  concerning exact sequences, homology, and colimit cocones, not this assertion.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
  constructible Ext, Ext-colimit, derivedHom, and this node id: the nearby
  `TraceFormula.ConstructibleEtaleExtContinuity` and
  `TraceFormula.BoundedConstructibleDerivedHomContinuity` concern affine inverse systems
  of schemes and finite coefficient rings, not filtered coefficient sheaves on one scheme.
  `ConstructibleExtContinuityStratum` concerns varying coefficient rings on strata.
  The node id appears in `Paper.ConstructibleRHomCoproductContinuity` only as its unprovided
  proof input. None supplies the present statement.
- Exact proposed names and the item id searched in `dag/lean_names_upstream.json`, upstream,
  and side-project sources: no declaration collision or already stated item found.

Edge cases checked before writing: empty scheme; zero ring; zero K; zero coefficient
sheaves; a cohomology sheaf supported on a single stratum; empty strata; potentially
unbounded negative cohomology of K; n<0, n=0, and n>0; non-poset filtered categories with
parallel arrows; singleton diagrams. `IsFiltered` correctly excludes an empty index category.
The stratification may depend on j and no uniform rank, uniform number of strata, or finite
Tor dimension is required. No finite or torsion condition is imposed on A or the G_i.

Validation: the initial module compiled through `scompile.py` in both sandbox and library
modes (5.0 s and 5.7 s), with no warnings or errors. The final explicit-dependency import
list also compiled cleanly in both modes (4.0 s and 4.4 s), with no warnings or errors. No node correction, new node, dependency module,
or STATEMENT-DISPUTED issue is needed.

## Second reading by Q58

Worker self-check; independent review is supplied by the maintainer under the dispatch
brief, which forbids starting other agents. I reopened the node statement and the actual
Lean signature and matched every row above: X Noetherian, A commutative Noetherian, ordinary
D(X_et,A), the existential upper bound only, one finite locally closed stratification per
cohomology degree, finite-generated locally constant restrictions, arbitrary integer n,
and an arbitrary small filtered diagram of coefficient module sheaves. I checked the
helper's three composite functors and the defining formula and leg equation of
`colimit.post` in Mathlib. Its target is precisely H^n RHom(K,(colim G)[0]).

The initial draft used a generic preserves-limits import for the comparison map. On reading
its actual definition in `Limits.HasLimits` I replaced that import with the defining module
and made all recorded statement-dependency module imports explicit. No hypothesis or
conclusion changed. I checked that the finite-type condition is finite generation of
module stalks, not finiteness of the underlying sets, and that stratifications do not
require extra constructibility of strata. All universes and variables are explicitly
bound under `autoImplicit false`; the module has no private notation or local instance,
no hollow construction, and only the one named theorem is postponed. Every Lean line has
at most 100 characters. The JSON changes only the item's `lean` field and records the
signature verbatim.
