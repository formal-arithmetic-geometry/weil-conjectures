## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGeneratorDetectsLowerBound` states
`AlgebraicGeometry.AlgebraicSpace.generator_detects_lower_bound`, with a single
`sorry` and no new definitions. Its docstring carries all eight steps of the
accepted node proof. I read Stacks `spaces-perfect.tex`, Tag 0GFI,
`proposition-detecting-bounded-below`, including its equivalences and proof;
the node selects exactly conditions (1), (2)/(3), and (6). I also read the current
blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/` unit
`sk-thm-sf-ctf-stability/_section.md` and its direct-images proof (3).

Hypotheses and objects, clause by clause:

- The size convention is implemented by explicitly declared universes `u w`,
  `{S : Scheme.{u}}`, and `[HasDerivedCategory.{w} X.SmallModules]`. No equality
  between the geometric and localization universes is imposed. The small affine
  etale model is the existing equivalent ringed topos, with coefficients and
  module sections in the original `u`, rather than a coefficient enlargement.
- The scheme and algebraic space over it are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. The algebraic-space type already includes the fppf
  sheaf, representable diagonal and representable surjective etale atlas.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)`, precisely the finite
  subcover property for its point topology.
- Quasi-separatedness is `hqs : X.IsAbsolutelyQuasiSeparated`. Its recorded
  affine-test definition is equivalent to quasi-compactness of the absolute
  diagonal (0AHR), with no quasi-separatedness assumption on S.
- `G : X.DerivedQCoh` gives an ambient unbounded derived object `G.obj` whose every
  cohomology sheaf, transported through the module equivalence, satisfies the
  recorded Mathlib `SheafOfModules.IsQuasicoherent` predicate. The same full
  subcategory is used for `K : X.DerivedQCoh` and every test `F`.
- `hG : SheafOfModules.IsPerfectOnRingedSiteOfUniverses ... G.obj` says that G is
  represented by a complex etale locally quasi-isomorphic to bounded complexes
  of finite free retracts. The local bounds and ranks can vary over the cover.
- The exact generator hypothesis is
  `hgen : ∀ F : X.DerivedQCoh, (∀ n : ℤ, Subsingleton (G.obj⟦n⟧ ⟶ F.obj)) →
  IsZero F.obj`. A Hom group vanishes exactly when its type is subsingleton;
  additive Hom types are inhabited by zero. `IsZero` expresses isomorphism to zero.
- Clause (i) is `∃ c : ℤ, ∀ j : ℤ, j < c → IsZero
  ((DerivedCategory.homologyFunctor X.SmallModules j).obj K.obj)`. In Mathlib
  integer cochain homology is cohomology. Transport by the exact module
  equivalence preserves zero cohomology sheaves.
- Clause (ii) is `∃ c : ℤ, ∀ j : ℤ, j < c →
  Subsingleton (G.obj ⟶ K.obj⟦j⟧)`. The target-shift sign agrees with the source's
  `Hom(G[-j],K)`, not its opposite. The existential bound is allowed to depend on K.
- The dual in (iii) is `X.derivedHom.obj (op G.obj, X.derivedStructure)`:
  precisely the recorded K-injective internal Hom into the structure sheaf in
  degree zero. The tensor with K is `X.derivedDualityModel.closed.tensor.obj
  (..., K.obj)`. This is the existing normalized K-flat tensor presentation,
  not a newly supplied functor or arbitrary morphism.
- Clause (iii) is the existence of an integer c such that for every j<c the
  recorded `ringedSiteZerothHypercohomologyOfUniverses` of the j-shift of that
  tensor is zero. This is H^j RΓ of that tensor, since H⁰ RΓ(L[j]) = H^j RΓ(L).
  It is exactly cohomological boundedness below of RΓ; it does not assert a
  bound on the underived sections complex or impose boundedness on K.
- All three conditions are equivalent: the conclusion is `(i ↔ ii) ∧ (ii ↔ iii)`.
  The three existential integer bounds are independent. No uniform bound or
  additional cohomological amplitude assumption has been added.

Dependency declarations read and used (including publicly imported specializations):

- `def-weil-size-convention`: a metatheoretic convention, with no declaration;
  its explicit universe and localization binders are given above.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`, `structureSheaf`,
  `Modules`, and the small etale site from `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` in
  `Sheaf.CategoryTheory.RingedSiteModules`, transparently `SheafOfModules`.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.homologyFunctor`, from Mathlib's derived category modules.
- `def-trf-space-quasi-coherent-module`: `AlgebraicGeometry.AlgebraicSpace.QCoh`
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` and its underlying
  Mathlib `SheafOfModules.IsQuasicoherent` predicate, used by `derivedQCohProperty`.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its defining
  `IsLocallyStrictPerfectComplexOfUniverses` in
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.
- `def-pur-derived-internal-hom`: publicly import its recorded module
  `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, which preserves
  `CategoryTheory.derivedInternalHomOfUniverses` from
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`. The existing
  algebraic-space `derivedHom` is exactly its small-ringed-model specialization;
  the ordinary ModuleCat abbreviation is not used on sheaf objects.
- `def-pur-ringed-site-zeroth-hypercohomology`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses` in
  `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`.
- Added already-landed `def-sfb-space-derived-module-calculus`:
  `DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`, `derivedStructure`,
  `derivedHom`, `derivedDualityModel` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`. The underlying
  `smallStructureSheaf`, `SmallModules`, and `smallModuleEquivalence` are from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`.
- Added already-landed `def-sfb-space-absolute-quasi-separated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`.

Only the item's `lean` record and addition of these two landed definition nodes
in `stmt_deps` change. There is no statement correction, new node or dependency
repair. No target statement changes.

All currently recorded proof-dependency modules are plain imports. The following
proof dependencies have neither a Lean record nor a Mathlib match and therefore
have no module to import yet: `lem-sfb-space-perfect-ext-window`,
`lem-sfb-space-perfect-generator-thick`, `lem-sfb-space-supported-koszul-low-localization`,
`lem-sfb-space-perfect-open-retract`, `lem-sfb-space-derived-pushforward-coproducts`.
The Hom-triangle Mathlib leaves share the imported Pretriangulated module.

Edge cases checked before writing and again against the final signature:

- Empty X and the zero ring affine: all module cohomology and Hom groups vanish;
  the zero object can generate the zero category and all three conditions hold.
  No nonemptiness, nonzero-ring, or nonzero-generator condition is present.
- On Spec A with G=O, clause (ii) is eventual negative cohomology vanishing.
  Shifting K changes a lower bound by the expected integer and keeps equivalence.
- K=0 satisfies all conditions, and no boundedness of an arbitrary K is assumed.
- A zero G on a nonzero derived category fails `hgen`; perfection alone would
  not suffice. This shows the generator hypothesis is substantive.
- An arbitrary, possibly non-quasi-separated base S is allowed; absolute
  quasi-separatedness is imposed on X, not on S or only on its relative diagonal.
- The cohomology functors and Hom conditions quantify over every integer,
  including degree zero and arbitrarily negative degrees; no natural-number
  restriction has slipped in.

Searches actually run through `msearch.py Q56 <item>`:

- LeanFinder: "Perfect generator of the derived category of a quasi compact
  quasi separated algebraic space detects bounded below complexes by eventual
  negative Hom vanishing". Eight hits, including `DerivedCategory.isGE_iff`,
  `IsGE`, `IsLE`, and bounded representative lemmas; none is the theorem.
- Loogle: `DerivedCategory.IsBoundedBelow, IsPerfectOnRingedSite, IsGenerator`.
  Zero hits; unknown identifier `DerivedCategory.IsBoundedBelow`.
- Mathlib grep: `generator.*bounded|bounded.*generator|IsBoundedBelow` in
  `Algebra/Homology`. Zero hits.
- LeanSearch: "perfect generator detects bounded below derived category
  algebraic space". Eight hits on strong generators, localizations and bounded
  representatives; none is this algebraic-space detection theorem.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id and `generator.*bounded|Generator.*Bounded|generatorDetects`:
  unrelated bounded-resolution/constructibility hits, no exact existing statement.
- Direct rg of algebraic-space modules for generator, perfectness, QCoh,
  quasi-compactness, quasi-separatedness, tensor, dual and global sections:
  found the reused derived calculus and the compact/perfect weak generator siblings,
  which assert existence of a generator rather than the present lower-bound test.

Validation: prescribed scompile.py compiled this module in both sandbox and library
mode against the live published build, in 4.4 and 4.5 seconds, with no errors or
warnings. There are no auto-implicit variables, local notation, new instances,
auxiliary theorem obligations, or lines over 100 characters.

## Second reading by Q56

This is a second pass by the same dispatcher worker: the task explicitly forbids
starting other agents; the maintainer supplies the independent review after delivery.
I reopened the node, Stacks 0GFI, the actual perfectness and derived calculus
definitions, the zeroth-hypercohomology construction, and the final theorem signature.

The second pass matched S/X to the scheme/algebraic-space binders, qc/qs to the
point-topology compactness and absolute affine-test predicate, G/K/F to the full
subcategory with quasi-coherent cohomology, local finite-free retract models to
hG, and all shifted-source zero tests to hgen. Each of (i), (ii), (iii) has its
own existential integer bound and tests every j below it. The two iff clauses
express precisely three-way equivalence. In (iii), the source is RHom(G,O), then
the fixed tensor with K, then H⁰ RΓ after shifting by j. This agrees with RΓ being
bounded below; it neither replaces the dual by G nor reverses the shift.

I checked the selected tensor's `RingedSiteDualityModel` fields: its closed
structure is tied to the existing derived internal Hom and its representative
comparisons are normalized on K-flat tensors. Thus the statement uses the shared
construction. I also compared the small-model version with the original etale
topos: the recorded module equivalence preserves cohomology, zero objects and local
finite-free splittings, while the shared duality model and sections are the derived
operations on that same equivalent ringed site. No mathematical mismatch or required
statement correction was found. The only graph completion was adding the two
already-landed owning definition nodes, rather than introducing duplicate notions.
