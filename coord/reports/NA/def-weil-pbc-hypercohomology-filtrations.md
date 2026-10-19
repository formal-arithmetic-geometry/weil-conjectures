## Worker report

Item: def-weil-pbc-hypercohomology-filtrations. Group NA, 2026-10-17.
Module: Sheaf.AlgebraicGeometry.HypercohomologyFiltrations.

This restores the withdrawn module's statement against the current published interfaces.
The node's natural-language statement, statement dependencies and proof are unchanged.
Definitions have explicit data; the three named theorems are stated with `sorry`:
`CategoryTheory.hypercohomology_maps_exact`,
`CategoryTheory.hypercohomology_images_antitone`, and
`AlgebraicGeometry.Etale.hypercohomologyFiltrations_spec`. They belong to this node,
and their docstrings describe the corresponding exactness, antitonicity and specification
proofs. The specification docstring follows all eight steps of the node's current proof.
No theorem is proved in this delivery.

The old failure was `DecreasingFiltration.step` not existing. The published generic
`DecreasingFiltration` uses `F` and `F_succ_le`; the published exact-couple convergence
interface instead returns `PBCDecreasingFiltration`, with `step` and `antitone_step`.
The repair uses that existing upstream representation everywhere, constructs the exact
couple directly with its published fields (rather than the retired side-only
`ofShifted` wrapper), and replaces duplicated side imports with the upstream modules.
The square parameter now uses the recorded `ChosenCartesianSquare` declaration, rather
than the former unchosen `IsPullback` parameter. This retains the node's chosen Cartesian
identification; its choice does not enter the three truncation constructions.

Hypotheses and the preliminary conventions are rendered as follows:

- The four arbitrary schemes and the four arrows are the explicitly bound
  `X X' Y Y' : Scheme.{u}`, `f`, `f'`, `g`, `g'` of the module's étale section.
  `sq : ChosenCartesianSquare g' f' f g` includes commutativity, a specified isomorphism
  with `pullback f g`, and both projection equations, exactly as the square node requires.
- The bounded-below derived object is `L : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`. Its chosen bounded-below
  representing complex is the module parameter `K : CochainComplex.Plus ...`;
  `e : DerivedCategory.Q.obj K.obj ≅ L.obj` records the representation. All constructed
  objects are on this representative, as the node requests; transport along `e`
  identifies their abutments with those of `L`.
- `hT : ∀ q, CategoryTheory.Sheaf.IsTorsion
  ((DerivedCategory.homologyFunctor _ q).obj L.obj)` is precisely torsion cohomology.
  The definitions themselves do not require torsion, as the node explicitly permits.
- `a : ℤ` and `ha` give cohomological vanishing below `a`; `hterms` gives zero terms
  of the selected representative below `a`. These are the stated choice of representative,
  not a new condition on the derived object.
- `TruncationCouple.truncation K q` is the recorded smart truncation, and
  `TruncationCouple.cohomologyComplex K q` is the single cohomology complex in degree `q`,
  representing `H^q(K)[-q]`. `TruncationCouple.triangle K q` supplies the canonical
  distinguished triangle. The structure maps have the node's bidegrees:
  `hypercohomologyAlpha` has `(-1,+1)`, `hypercohomologyBoundary` has `(+2,-1)`,
  and `hypercohomologyG` has `(0,0)`.
- `hypercohomologyCouple` is a real `BigradedExactCouple B 0` constructed from these
  maps and the separately named exactness theorem. `pageCouple r` is page `r+2`;
  `.page r` uses the actual page number, and the specification requires `2 ≤ r` there.

Clause 1, the sequence on Y:

- `hypercohomologyFirstFunctor f` is `(lowerStar AddCommGrpCat f).rightDerivedFunctor`.
  The generic definitions `hypercohomologyD` and `hypercohomologyE` apply `H^(p+q)`
  to its values on the displayed truncation and single cohomology complexes. These
  are exactly the node's D and E formulas, with their triangle-induced maps.
- The three bridge equations in `hypercohomologyFiltrations_spec` conjugate alpha,
  the boundary and `initialG` by the dependency's `TruncationCouple.bridgeIso`.
  Thus this is the recorded truncation couple for `f_*`, using the same K-injective
  construction, rather than an unrelated isomorphic bigraded datum.
- The first `∀ (p : ℕ) (q : ℤ), Nonempty (...)` clause identifies E2 with
  `((lowerStar ... f).rightDerived p).obj (K.obj.homology q)`. Negative `p` is covered
  separately by all-page vanishing.
- `hypercohomologyAbutmentMap F K n q` is literally `H^n(F(Q(ιTruncLE q)))`.
  `hypercohomologyFiltration F K n` has `step p := imageSubobject
  (hypercohomologyAbutmentMap F K n (n-p))`. No existential or arbitrary subobject
  is used to define its data.
- The first specification block gives `IsFinite`, fullness for `p ≤ 0` and zero
  inclusion for `n-a+1 ≤ p` (equivalently the bottom subobject). Its page-vanishing
  block kills every page unless `p ≥ 0` and `q ≥ a`. In degree `n=p+q`, this says
  exactly that only `a ≤ q ≤ n` can contribute.
- The existential alpha colimit `T`, limit-subobject datum `Z`, and equality `hT`
  identify the abutment with the actual `H^n(Rf_* QK)`. `ConvergesTo Z T` is the
  recorded convergence predicate, not just an E-infinity existence claim. The
  equation for every `(T n).ι p` specifies the actual truncation-to-abutment map,
  and the subobject equation identifies the convergence image filtration with the
  explicitly constructed hypercohomology filtration.

Clause 2, exact base change along g:

- `hypercohomologyBaseChangeFunctor f g` is precisely the composite of `Rf_*` with
  `(upperStar ... g).mapDerivedCategory`. Its D and E terms are consequently the
  node's `H^(p+q)(g⁻¹Rf_* truncation)` and shifted-cohomology formulas.
- The middle E2 clause is `g⁻¹((f_*).rightDerived p (K.obj.homology q))`.
  The middle finite-filtration, vanishing, `AlphaColimit`, `ConvergesTo`, actual-map
  and image-identification blocks repeat all the claims on `Y'`, with this functor.
- The existential `δ` compares every mapped D term with that middle D term.
  Its normalization is the actual `mapDerivedCategoryHomologyFunctorIso` at the
  chosen truncation. The page comparisons `φ r p q` exist for every page; their
  page-zero normalization is the same canonical homology comparison on the single
  cohomology complex. The alpha, boundary and initial-G equations identify all
  the structure maps, and the last equation gives every differential square.
  Thus applying the exact inverse image gives the asserted spectral sequence,
  with the specified canonical comparison at E2.
- In the final clause, `c` is required to equal the canonical homology comparison
  on `Rf_* QK`. The equation for every `p` takes the image of the mapped filtration
  inclusion followed by `c.hom` and equates it to the middle filtration step.
  This is exactly the transported filtration `g⁻¹F^p`, expressed as subobjects
  of the actual middle abutment, using exactness of inverse image.

Clause 3, the second sequence on Y':

- `hypercohomologySecondFunctor f' g'` is the composite
  `(upperStar ... g').mapDerivedCategory ⋙ (lowerStar ... f').rightDerivedFunctor`.
  Its D and E definitions are exactly the two displayed formulas involving
  `Rf'_*g'⁻¹` on the original truncations and shifted cohomology objects.
- The third E2 identification is
  `((lowerStar ... f').rightDerived p).obj ((upperStar ... g').obj (K.obj.homology q))`.
  The third finite-filtration, all-page vanishing and convergence blocks specify
  the image filtration on `H^n(Rf'_*g'⁻¹ QK)`, with the same range `a ≤ q ≤ n`.
- The termwise inverse-image complex is explicitly
  `((upperStar ... g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj`.
  The next clause gives its zero terms for `i<a`. The truncation comparison is an
  isomorphism of these actual complexes with the equation commuting with their
  canonical inclusions. This is the node's equality of truncations expressed by
  its canonical isomorphism. The following homology isomorphism states exactly
  `H^q(g'⁻¹K) ≅ g'⁻¹H^q(K)`.
- Finally `hypercohomologyFiltrations` returns the three explicitly constructed
  filtrations as a product, in the order (1), (2), (3).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` (including its inherited `CommSq`).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, and its coefficient imports:
  `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.homologyFunctor`,
  and `CategoryTheory.Sheaf.IsTorsion` for the abelian-sheaf specialization.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`,
  with its strictly bounded representatives and cohomological description.
- `WeilConjectures.CategoryTheory.TruncationCouple`:
  `TruncationCouple.truncation`, `cohomologyComplex`, `transition`, `projection`,
  `triangle`, `bridgeIso`, `alpha`, `f`, and `g` (the recorded `truncationCouple` data).
- `WeilConjectures.CategoryTheory.ExactCouple`:
  `BigradedExactCouple`, its fields, `pageCouple`, and `page`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`, and the ordinary `rightDerived`;
  right derived functors are used in the full derived category on bounded-below objects,
  compatible with `rightDerivedLowerStarPlus` by the recorded compatibility interface.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryHomologyFunctorIso`,
  `isGE_mapDerivedCategory_obj`, and the restriction `mapDerivedCategoryPlus`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`:
  `AlgebraicGeometry.Etale.upperStar_abelian_exact` and the exactness instances.
- `WeilConjectures.CategoryTheory.PBCFiltration` and `ImageFiltration`:
  `PBCDecreasingFiltration`, `IsFinite`, and `PBCDecreasingFiltration.image`.
  The image-filtration construction for a decreasing system of maps is the
  explicitly stated extension described in the image-filtration node's own note.
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`:
  `BigradedExactCouple.AlphaColimit`, `LimitSubobjects`, `imageFiltration`, and `ConvergesTo`.
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`:
  `CategoryTheory.exists_truncationHypercohomology` (proof import).
- `Sheaf.CategoryTheory.ExactFunctorCouple`:
  `CategoryTheory.BigradedExactCouple.exactFunctor_couple` (proof import).
- `def-sp-etale-dictionary` is explicitly recorded as a convention with null
  module/declaration. Its substitutions are instantiated by the three actual functors above.

The remaining available proof dependencies (right-derived lower bounds, compatibility,
K-injective bridge, half-plane convergence and abutment-image identification) are imported.
The recorded `Sheaf.CategoryTheory.ExactCoupleMorphism` is intentionally omitted: its current
source imports the retired side `Sheaf.CategoryTheory.ExactCoupleConvergence` and
`HalfPlaneConvergence`, and constructs a second `BigradedExactCouple` via the generic upstream
`ExactCouple`. This conflicts with the published `WeilConjectures.CategoryTheory.ExactCouple`
used by this node's recorded statement dependencies. The specification directly states all
required comparison squares; its docstring retains the couple-morphism proof step. Replacing
that unrelated proof-only dependency is outside this item's dependency-repair scope.

Edge cases checked before editing:

- The zero complex and empty schemes give zero D/E terms and zero abutments; fullness
  and vanishing of a filtration then agree, since top equals bottom on the zero object.
- If `n<a`, no pair on the total-degree diagonal survives. The simultaneous full and
  zero step bounds correctly force the abutment to be zero. No nonempty degree range
  or nonnegative lower bound is assumed.
- `p=0` is allowed in every E2 identification; negative `p` and `q<a` are killed by
  the explicit all-page statement. The bound is zero already at `p=n-a+1`.
- The integer `a` is unrestricted. Every natural-number page and every integer total
  degree and bidegree are included. Actual pages start at 2; pageCouple starts at 0.
- No properness, smoothness, finiteness of dimension, or bounded-above hypothesis is added.
  Inverse image is exact for arbitrary scheme morphisms; identity arrows are included.
- All category, derived-category and scheme universes are explicitly bound;
  `set_option autoImplicit false` checks against accidental implicit variables. The
  coefficient category remains `AddCommGrpCat.{u+1}` on the small étale sites.

Searches for an existing statement:

- `msearch.py ... leanfinder "hypercohomology spectral sequence truncation image filtration
  derived direct image"`: eight hits on smart truncation inclusions and their short
  complexes; no construction of these three étale sequences and canonical comparisons.
- `msearch.py ... loogle "DecreasingFiltration, BigradedExactCouple"`: no hits;
  DecreasingFiltration is unknown to the Mathlib index.
- `msearch.py ... grep "hypercohomology|truncation.*spectral|DecreasingFiltration"
  Algebra/Homology`: no Mathlib match.
- `rg` in `WeilConjectures/` for `hypercohomologyFiltrations`,
  `hypercohomologyFiltration`, and the item id: no defining upstream match in the old
  source checkout; only a descriptive reference in DeligneLaumon/Reduction/FormalSteps.
- `rg` in `lean/Sheaf`: the withdrawn module for this very item and consumers in
  HypercohomologyConvergence; no other owner of the notion. The current server source
  of `WeilConjectures.AlgebraicGeometry.HypercohomologyFiltrations` is unavailable.
  The existing withdrawn text cannot be rebound: its specification is the faulty
  declaration this task must restore.
- `scompile.py --source` read the current published TruncationCouple,
  TruncationHypercohomology, ExactCouple, ExactCoupleConvergence, PBCFiltration,
  ImageFiltration, DerivedCategories, EtaleInverseImageExact, ExactFunctorCouple,
  and ExactCoupleMorphism sources. These establish the precise signatures used here.
  The unavailable ExactCoupleShifted wrapper was replaced by direct construction
  from the published exact-couple fields, with no new helper definition.

No disputed statement, source-based statement correction, or new node is needed.
The current blueprint main-20261015 and the item's recorded source both give the same
truncation spectral sequences and image filtrations. The detailed three-sequence
statement retained by the DAG is implemented in full.

## Dependency modules

`def-sp-filtration`: lean-only repair to the existing upstream
`CategoryTheory.PBCDecreasingFiltration` in `WeilConjectures.CategoryTheory.PBCFiltration`.
The former record points at the generic `DecreasingFiltration`, whose fields and
auxiliary API cannot be used as the return type of the recorded exact-couple
`imageFiltration` or `ConvergesTo` interface. The PBC declaration is the same family of
subobjects with the same decreasing condition, in the representation that those
interfaces require. No module or definition is duplicated, and no mathematical
statement or other field of the dependency is changed.

`def-sp-image-filtration`: lean-only repair to the existing upstream
`CategoryTheory.PBCDecreasingFiltration.image` in
`WeilConjectures.CategoryTheory.ImageFiltration`. The former generic
`DecreasingFiltration.image` consumes the other representation and cannot transport
these PBC filtration objects. The selected declaration is exactly the image of each
filtration step under the given morphism. No file or extra theorem is introduced.

## Second reading by NA

I read the node statement, its source place, every recorded statement dependency, and
the delivered Lean module. The matching is as follows.

- The square is rendered by `X X' Y Y' : Scheme.{u}`, arrows `f`, `f'`, `g`, `g'`,
  and `sq : ChosenCartesianSquare g' f' f g`. The published square structure extends
  `CommSq` and contains the chosen pullback isomorphism and both projection equations,
  so it supplies exactly the node's cartesian square and chosen identification.
- `L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`,
  `K : CochainComplex.Plus ...`, and `e : Q.obj K.obj ≅ L.obj` render the bounded-below
  derived object and its chosen complex representative. `hT` is torsion cohomology,
  `a` and `ha` give the lower cohomological bound, and `hterms` gives the required
  representative with zero terms below `a`; no properness, smoothness, finiteness,
  characteristic, or bounded-above assumption is added.
- `TruncationCouple.truncation`, `cohomologyComplex`, `triangle`, `transition`, and
  `projection` render the canonical truncations and triangles. The definitions
  `hypercohomologyD`, `hypercohomologyE`, `hypercohomologyAlpha`,
  `hypercohomologyBoundary`, and `hypercohomologyG` have respectively the node's
  D/E formulas and bidegrees `(-1,+1)`, `(+2,-1)`, and `(0,0)`.
- `hypercohomology_maps_exact` and `hypercohomologyCouple` render the exact couple;
  `pageCouple` and `.page` use the recorded convention whose first page is `E₂ = E`.
  `hypercohomologyAbutmentMap` and `hypercohomologyFiltration` are the actual
  truncation-to-abutment map and its image filtration, with no arbitrary subobject.
- The first, middle, and second functors are exactly `Rf_*`, `g⁻¹Rf_*`, and
  `Rf'_*g'⁻¹` in `hypercohomologyFirstFunctor`, `hypercohomologyBaseChangeFunctor`,
  and `hypercohomologySecondFunctor`. The three finite-filtration and page-vanishing
  blocks give the node's finite range `a ≤ q ≤ n` (the displayed conditions are the
  equivalent `q < a ∨ p < 0` vanishing and the zero upper step).
- The three `AlphaColimit`/`LimitSubobjects`/`ConvergesTo` blocks identify each
  abutment with the corresponding derived homology and identify every limiting step
  with `hypercohomologyFiltration`, exactly as the node's image-filtration and
  convergence clauses require.
- The bridge equations conjugate the first couple's maps by the recorded
  `TruncationCouple.bridgeIso`; the three E₂ clauses are the canonical derived-functor
  comparisons (represented as `Nonempty` isomorphisms, as in the dependency theorem).
  The middle `δ` and page maps `φ` are normalized by
  `mapDerivedCategoryHomologyFunctorIso`, commute with all structure maps and
  differentials, and the final canonical `c` equation identifies the transported
  filtration `g⁻¹F` with the middle image filtration.
- The final termwise inverse-image clauses explicitly give zero terms below `a`, the
  canonical truncation comparison, and `H^q(g'⁻¹K) ≅ g'⁻¹H^q(K)`, which are the
  node's second-sequence compatibility assertions. `hypercohomologyFiltrations`
  returns the three filtrations in the stated order.

Edge cases checked: zero and empty schemes/complexes make all D/E terms and abutments
zero; `n < a` gives an empty surviving diagonal and forces the top filtration step to
be zero; `p = 0` is included, while negative `p` and `q < a` vanish; `a` is any integer;
all natural pages and integer bidegrees are quantified; identity arrows and empty index
or object cases are not excluded; the coefficient category and all scheme/derived
universes are explicit (`AddCommGrpCat.{u + 1}` and `Scheme.{u}`).

I repeated the existing-notion searches: `msearch.py` LeanFinder for truncation
hypercohomology/image-filtration spectral sequences, `msearch.py` Loogle for
`BigradedExactCouple`/`PBCDecreasingFiltration`, and `rg` over Mathlib, the source
`WeilConjectures/`, and project `lean/Sheaf`. Only canonical truncation ingredients,
the generic filtration family, and unrelated termwise hypercohomology presentations
were found; no declaration states this three-sequence construction. The published
`PBCDecreasingFiltration` and `.image` declarations were checked directly and are the
repaired dependency interfaces, not duplicate definitions.

No mismatch remained after the worker's repairs: the retired `DecreasingFiltration`
fields were replaced by the published `PBCDecreasingFiltration` representation, the
direct exact couple uses the published fields, and the square uses
`ChosenCartesianSquare`. No node statement, dependency list, or source-based
correction was changed. `scompile.py` compiled the module both in the sandbox and
under its library name with no errors or non-sorry warnings.

## Validation

The prescribed scompile.py compiled the delivered module individually in its sandbox
and under its library module name, using the published-source overlay (about five
seconds per invocation). Early missing retired imports and a docstring-spacing warning were repaired.
The delivery dry run is run below after this second reading; the module compilation
and dependency `#check` probes are already clean with no non-sorry warnings.
