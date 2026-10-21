## Worker report

The module `Sheaf.Paper.FiniteScalarPerfectRefinement` states
`AlgebraicGeometry.Scheme.finite_scalar_perfect_refinement`, with proof `sorry`.
No mathematical statement has been corrected, and no new DAG nodes are needed.
The theorem's local model is the actual constant-module sheaf followed by ordinary
sheafified scalar extension, including the differentials. Its finite-free
comparison is normalized on pure tensors, rather than left as an arbitrary
identification of free modules.

Hypotheses, in the order of the node:

- `S : Scheme.{t}`, `[Nonempty S]`, and `[CompactSpace S]` give the nonempty
  quasi-compact scheme. `CompactSpace` has no separation assumption. The site is
  exactly `Scheme.ProEt.topology S`, whose objects are weakly etale maps and
  whose generating covers are the fpqc weakly etale families.
- `R : Type r` with `[CommRing R]` and
  `B : Sheaf (ProEt.topology S) CommRingCat.{r}` are the arbitrary
  coefficient ring and commutative ring sheaf. The size convention places
  coefficients in a universe containing the small site's objects and morphisms;
  `[UnivLE.{t + 1, r}]` expresses only this size convention: the coefficient
  universe contains the site-object universe. It is automatically available at
  `r = max (t + 1) s` for any independent scalar size s. The site is unchanged;
  neither an equality of site universes nor an equality with coefficients is imposed.
  This standard sizing class supplies essentially-small models and sheafification,
  whose instance data is constructed explicitly in the module.
- `φ : scalarPerfectRing (ProEt.topology S) R ⟶ B` is the specified map from
  the constant commutative ring sheaf. `scalarPerfectRing` is exactly
  `(constantSheaf J CommRingCat).obj (CommRingCat.of R)`.
- `P` belongs to the unbounded `DerivedCategory` of the recorded
  `SheafOfModules` category over the underlying ring sheaf of B. The two
  `HasDerivedCategory` binders choose the localization sizes globally and on
  slices, independently (`w`, `w'`). They are categorical construction data,
  obtainable by `HasDerivedCategory.standard`, not geometric restrictions.
- `I : Type i` and `U : I → S.ProEt` introduce the original family without a
  finiteness assumption on I or a quasi-compactness assumption on its members.
  `_hcover` is membership of its underlying family in
  `Scheme.proetalePrecoverage.coverings S`; this retains the finite-refinement
  fpqc condition, rather than replacing it by joint surjectivity.
- `F` is the specified family of integer-indexed cochain complexes of R-modules.
  `_hbounded` is strict vanishing of the terms outside some finite interval.
  `spl k : ModuleCat.StrictPerfectCoefficientPackage (F k)` is exactly the
  degreewise finite-free retraction data specified in the node. This encodes
  finite projectivity by the node's direct-summand convention, with no chain-map
  requirement for the inclusions or projections.
- `_hrep` is the given family of representing isomorphisms. Restriction is
  `ringedSiteDerivedRestrictionOfUniverses`; the model is
  `scalarPerfectLocalModel`, hence `scalarPerfectChartComplex`. This first
  restricts the constant module sheaf to the slice and then changes rings along
  the restricted φ. Thus its terms are B|U tensor over underline R|U with the
  constant scalar modules. Constant sheaves on the slice are presented by
  restriction of the global constant sheaf, canonically identified with
  sheafification of the same constant presheaf by the slice comparison.

Conclusion, clause by clause:

- The witnesses `n`, `_hn : 0 < n`, `α : Fin n → I`, and `V` are the finite
  nonempty indexing set, selection function, and opens inside the selected
  original charts. `IsAffineOpen (V j)` imposes affineness. The next precoverage
  membership says that the actual composite maps `(V j).ι ≫ (U (α j)).hom`
  form a pro-etale covering of S.
- `lo`, `hi`, their ordered-interval conjunct, and strict term-vanishing
  conjunct give the a_j, b_j and the stated bounds on the original F terms.
- The lower-bound inequalities together with `∃ j, a = lo j` specify the
  attained minimum exactly. The upper-bound inequalities together with
  `∃ j, b = hi j` specify the attained maximum exactly. These avoid proof terms
  for a partial minimum operation in the statement. Together with
  `lo j ≤ hi j`, they give each interval's inclusion in `[a,b]`. The explicitly
  requested `a ≤ b` is also present.
- For every j, the first local conjunct gives the representing derived
  isomorphism for P on the actual open chart; the next gives strict vanishing
  of the resulting E terms outside `[lo j, hi j]`.
- `pkg : StrictPerfectCoefficientPackageOnSite ... E` gives, in each degree,
  the finite rank, inclusion, projection and split identity. The equality
  `hN : pkg.N = (spl (α j)).N` identifies its ranks with the given scalar
  splittings. The isomorphisms `e q` identify scalar extension of each selected
  finite free scalar module with the finite tuple sheaf over B_j. The two
  displayed equations identify `pkg.i` and `pkg.p` with the actual images of
  the given scalar inclusion and projection under this identification.
- The last equation fixes the canonical identification: after any coordinate
  projection it sends `s tensor x` to `s * φ(underline(x_k))`. The helper
  `scalarPerfectChartSection` uses the module-sheafification units, and
  `scalarPerfectRingUnit` is the ring-sheafification unit. Thus these are the
  specified constant-sheaf scalar extensions, including the chosen maps.
- The entire conclusion is existential before any possible test module sheaf;
  no test object occurs in the hypotheses or choices. No flatness, exactness
  of tensor, Noetherian, separatedness, or quasi-separatedness is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  scheme opens and open immersion maps.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, without a Hausdorff condition.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`,
  `ProEt.topology`, `ProEt.precoverage`, and `Scheme.proetalePrecoverage`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the existing Mathlib `SheafOfModules` (objects, linear natural
  morphisms and abelian structure).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the bounded finite-projective-model
  convention. The hypothesis uses its supplied strict model with splittings,
  rather than merely asserting existence of a perfect representative.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor and independent-universe structures, retaining the imported actual
  sectionwise/sheafified change-of-rings constructors.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` and its imports:
  `ModuleCat.StrictPerfectCoefficientPackage`,
  `SheafOfModules.StrictPerfectCoefficientPackageOnSite`, and the original
  general representation definitions. The dependency repair below supplies
  their missing independent-universe constant scalar extension interface.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`, the restricted
  canonical representative followed by localization on the slice.
- The already recorded proof modules are imported for the finite-affine-cover,
  fpqc composition, weakly-etale stability, slice sheafification, natural tensor
  restriction, exact module restriction and sheafification/tensor comparisons.
  Mathlib geometric proof dependencies are supplied by the Proetale and
  QuasiCompact imports; none is replaced by a newly stated geometric lemma.

Edge cases checked against the statement and the source: S is explicitly
nonempty, so an empty refined family is excluded legitimately; I need not be
finite. Zero F is allowed and admits the interval [0,0]. Endpoints of distinct
models may be disjoint, which is why attained extrema are used. Splitting ranks
may be zero, and `Fin 0` gives the zero finite free module and empty tuple
sheaf. The zero ring and zero module remain allowed. Nonflat scalar extension,
for example Z to Z/2, preserves a split identity without preserving arbitrary
exact sequences. No quasi-separatedness of S or compactness of U_i was used.
The site retains object universe t+1 and morphism universe t; neither is equated
with the other. Localization universes are also independent.

Searches actually run for this delivery:

- msearch LeanFinder: "A pro etale cover of a quasi compact scheme with bounded
  finite projective scalar complexes admits finite affine charts with common
  degree bounds and scalar extended splittings". Eight hits, principally
  `QuasiCompactCover`/affine-transition-limit infrastructure; no combined
  scalar-perfect refinement statement.
- msearch Loogle: `AlgebraicGeometry.QuasiCompactCover`. Twelve hits describing
  the geometric cover and its refinements; none includes scalar models,
  uniform complex bounds or the extended splitting packages.
- msearch grep, AlgebraicGeometry:
  `proetale.*(finite|refin)|scalar.*(retract|splitting)`. No hits.
- msearch LeanSearch: "Constant sheafification and scalar extension of finite
  projective complexes on a quasi compact pro etale site admit a finite uniform
  refinement". Eight hits concerning module sheafification and constant
  sheaves, including `PresheafOfModules.sheafify` and
  `SheafOfModules.sheafificationCompPullback`; no theorem matching the item.
- Direct rg on `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name
  inventory for the node id and `finiteScalarPerfect`: no existing declaration
  of the item. Concept searches found and led to reading the package modules,
  `SiteConstantModuleFunctorGeneral`, `CommutativeSiteDerivedConstantModuleFunctor`,
  `ProEtaleLocallyConstantSheafOfUniverses`, `TensorProductOfUniverses`,
  `ScalarExtensionBinaryCoherence`, and the derived/slice interfaces. The
  existing general constant functors use coefficient size `max siteObj siteHom`;
  the pro-etale-specific objects use a lifted coefficient presentation and do
  not give a termwise functor on this node's supplied R-complexes and maps.
  The dependency repair generalizes the recorded package's actual construction.

The source read was `proetale.tex`, labels `definition-fpqc-covering`,
`lemma-recognize-proetale-covering`, and `lemma-proetale`, and the current
blueprint's `sk-thm-sf-ctf-stability-internal-hom.proof.md`, paragraphs 2--3.
The geometric finite refinement uses condition (4) of 098A and transitivity,
so it does not use the quasi-separated condition attached only to condition (5).
There is no STATEMENT-DISPUTED finding.

## Dependency modules

`def-weil-pbc-strict-perfect-coefficient-package`: the sandbox extends its
recorded `StrictPerfectCoefficientPackageOfUniverses` module; all three original
definitions are retained verbatim, as are their public imports. The original
ring-module package and the independent-site degreewise package are reused.
The unusable part was the constant-module functor in the earlier package
module, which fixes all three universes equal; the current general-universe
representation wrapper does not repair it. The added actual functors form the
constant presheaf with identity maps, sheafify it over the constant commutative
ring sheaf, and apply the existing `changeOfRingsOfUniverses` and
`changeOfRingsHomOfUniverses`. The localized construction restricts the constant
sheaf first, then changes rings along the actual restricted φ. Its pure
sections use the actual units, without arbitrary maps or choices from mere
existence. Proof obligations for local bijectivity of the ring unit and
additivity of the constant, scalar-extension and composite functors are named
theorems with `sorry`, source references and complete proof docstrings. These
are precisely the functoriality obligations of the same package construction,
not additional independent mathematical notions. All helper declarations are
listed in this node's `lean.declarations`. No dependency statement changes.

Validation: both delivered files compile separately through `scompile.py` against
the server published build (including the dependency overlay), with no errors or
unexpected warnings. The main module compiles in under six seconds.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
