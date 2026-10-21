## Worker report

The module `Sheaf.Algebra.Homology.FlatScalarCyclicResolution` states
`SheafOfModules.flat_scalar_cyclic_resolution`. Its only postponed proof is that named
theorem, whose docstring carries all six steps of the DAG proof. The six auxiliary
constructions have actual data and reuse existing categorical constructions. No source
statement correction, new definition node, or dependency repair was needed.

The source read was `literature/stacks-project/sites-cohomology.tex`,
`lemma-bounded-flat-K-flat` (06YQ, lines 3120 onward) and the construction immediately
preceding `definition-derived-tor` (06YU, lines 3270 onward). The first applies to every
bounded-above complex of flat modules; the second explicitly computes derived tensor by
replacing one factor. The point-site scalar injectivity is the domain cancellation
argument in the node; exact constant sheafification and flat extension transport it to
the site without requiring points.

Hypothesis and conclusion correspondence:

- The small site is `{C : Type u} [Category.{v} C]`, its topology `J`, and
  `[EssentiallySmall.{r} C]`. Object, morphism, coefficient, and derived Hom universes
  `u v r w` are explicitly declared and are not equated. Relative smallness is the
  size convention of the recorded K-flat and derived-tensor interfaces.
- The commutative integral domain is `(A : Type r) [CommRing A] [IsDomain A]`.
- Its constant ring sheaf is `scalarCyclicBase J A`, a transparent abbreviation of
  `(constantSheaf J CommRingCat).obj (CommRingCat.of A)`. The explicit
  `[HasWeakSheafify J CommRingCat]` is the infrastructure for this already-recorded
  constant-sheaf construction, not a flatness or points hypothesis.
- The commutative sheaf algebra is `(R : Sheaf J CommRingCat.{r})` with the actual
  ring-sheaf morphism `α : scalarCyclicBase J A ⟶ R`. For commutative rings, this
  morphism is precisely the algebra structure; no independently chosen action occurs.
- Flatness over the constant base is `hflat : IsFlatOnSite (...)`, applied to the
  regular `R` module after `restrictScalars` along the image of `α` under
  `sheafCompose J (forget₂ CommRingCat RingCat)`. This is exactness of the specified
  sheaf tensor functor, rather than the stronger condition that every section module
  is flat.
- The scalar and its nonvanishing are `(a : A) (ha : a ≠ 0)`.
- Injectivity is `Mono (scalarCyclicMultiplication R α a)`. The scalar morphism is
  constructed using the constant-presheaf map adjoint to `α`, followed by
  `unitHomEquiv.symm`. On sections it sends `x` to `x * α(a)`, equal to `α(a) * x`
  since `R` is commutative. Monomorphisms of module sheaves are sectionwise injective
  because their kernels are computed sectionwise.
- The displayed complex is `scalarCyclicComplex R α a`, defined as
  `CochainComplex.mappingCone ((singleFunctor _ 0).map (scalarCyclicMultiplication ...))`.
  In Mathlib's cohomological cone convention its source summand is in degree -1 and
  target summand in degree 0, with differential the specified positive scalar map;
  the remaining summands are zero. Thus it is the displayed complex up to the
  canonical zero-biproduct identifications, with no shift or sign reversal.
- The quotient is `scalarCyclicQuotient R α a := cokernel (scalarCyclicMultiplication ...)`
  in the category of sheaves of `R`-modules. It is the sheaf quotient, including when
  evaluation does not preserve cokernels.
- The augmentation is an actual cochain map `ε` from that cone to the degree-zero
  quotient. Its equation `mappingCone.inr (...) ≫ ε = singleFunctor.map (cokernel.π ...)`
  specifies its degree-zero component as the quotient projection. All other target
  degrees are zero, so this equation specifies the canonical augmentation uniquely.
- `IsKFlatResolutionIndependentCoefficients ε` asserts both the augmentation
  quasi-isomorphism and K-flatness of the displayed complex, using the dependency's
  exact definition.
- The separate `IsKFlatIndependentCoefficients (singleFunctor.obj (unit ...))`
  conjunct asserts that `R[0]` is K-flat over `R`.
- Finally, for every unbounded complex `M`, the `Nonempty` isomorphism identifies
  the existing `siteDerivedTensorIndependentCoefficients J R` applied to `Q(M)` and
  `Q((R/aR)[0])` with `Q(mapBifunctor M (scalarCyclicComplex ...) (curriedTensor _))`.
  This is precisely computation by direct-sum total tensor with the displayed complex.
  `HasDerivedCategory.{w}` supplies the existing derived category in the chosen
  universe; no resolution, comparison map, or derived tensor is an input hypothesis.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the constant presheaf, and `sheafificationAdjunction` for its
  canonical sections.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of `siteSheafTensorRight`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`, respectively acyclicity
  of total tensor against every acyclic complex, and quasi-isomorphism plus K-flatness.
- `Sheaf.Paper.ProjectionMateExact`: the recorded ringed-site module/derived tensor
  framework and `SheafOfModules.ringedProjectionMateExact`; imported as required by
  the statement dependency. Its shift and projection-mate conclusions are not added
  as hypotheses to this scalar-resolution statement.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, defined by the resolving
  localization's universal property. Its already-landed node
  `lem-weil-pbc-site-derived-tensor-descent` is added to `stmt_deps` to record the
  concrete derived tensor occurring in the signature. This does not change the
  natural-language statement or its proof route.
- Proof-only imports include
  `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` with
  `CochainComplex.isKFlat_of_boundedAbove_flat`, exact sheafification from
  `Mathlib.CategoryTheory.Sites.Sheafification`, acyclicity/homology from
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, and
  `Mathlib.Algebra.Homology.QuasiIso`. The module-category and tensor dependencies
  are publicly available via the recorded framework; the independent-universe
  monoidal structure is imported from the recorded `CochainTensorUniverses` module.

Edge cases checked before writing: `a` a unit gives a contractible cone and zero
quotient; `R = 0` is permitted and all conclusions hold; on the point site `R = A`
this is the usual two-term resolution. An empty site, or an object with an empty
cover, causes no failure because no enough-points or nonempty-sections hypothesis is
used. `a = 0` is deliberately excluded: for nonzero `R`, the negative cohomology
would be `R`. For `A = ℤ`, `R = (ℤ/2)_C`, and `a = 2`, injectivity fails, showing
why the base-flatness hypothesis cannot be dropped. Arbitrary characteristics and
unbounded test complexes are retained. No statement is disputed.

Searches actually run:

- `msearch.py leanfinder`: “A flat sheaf algebra over a constant integral domain has
  a K-flat two-term scalar quotient resolution”. Eight hits, including ordinary
  `Module.Flat.tfae_equational_criterion`, flat localized modules, and flat ring maps;
  none states the site-level scalar resolution.
- `msearch.py leansearch`: “A two term free complex of sheaves resolves the quotient
  by a nonzero scalar over a flat sheaf algebra”. Eight hits, including
  `SheafOfModules.free`, `ModuleCat.smulShortComplex`, ordinary module flatness, and
  sheafification scalar compatibility; no exact match.
- `msearch.py loogle`: `"smulShortComplex"`. Ten hits describing the ordinary-ring
  short complex, exactness and its quotient. These neither state K-flatness nor
  concern a sheaf algebra over a constant ring sheaf.
- `msearch.py grep`: `KFlat|kFlat|smulShortComplex`. Thirteen Mathlib hits, all uses
  or declarations of the ordinary-ring scalar short complex; no sheaf resolution.
- `rg` in both project roots searched scalar/cyclic resolutions, two-term complexes,
  scalar quotient, and scalar multiplication. The node-id grep in
  `lean/WeilConjectures` returned no match. Candidate ordinary module derived-base
  change, fixed-ring `Sheaf (ModuleCat A)` scalar multiplication in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction`, and constant-left-module
  predicates were read: none constructs this general ring-sheaf algebra scalar map
  or states this theorem. The construction uses the existing `unitHomEquiv` rather
  than copying a sectionwise module morphism implementation.

Validation: the prescribed `scompile.py Q24 lem-sfb-flat-scalar-cyclic-resolution`
compiled both its sandbox name and actual library module name cleanly (8.2 and 8.1
seconds); there were no errors or warnings. Every variable and universe is explicit.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
