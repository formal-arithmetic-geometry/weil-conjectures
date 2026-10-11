## Worker report

The module `lean/Sheaf/AlgebraicGeometry/HypercohomologyFiltrations.lean` defines
`AlgebraicGeometry.Etale.hypercohomologyFiltrations`: the ordered triple of image
filtrations on the three abutments. The first is on Y; the base-changed first and
the second are on Y'. All data is explicit. Three named theorems have `sorry`:
`CategoryTheory.hypercohomology_maps_exact`,
`CategoryTheory.hypercohomology_images_antitone`, and
`AlgebraicGeometry.Etale.hypercohomologyFiltrations_spec`. Their docstrings give
complete natural-language proofs and their blueprint tags refer to this node.
The first two postpone only the exactness and antitonicity proofs needed by the
definitions; neither supplies unspecified objects or maps.

Hypothesis and clause correspondence:

* Schemes X, X', Y, Y' are `Scheme.{u}`; their four named maps are `f`, `f'`, `g`,
  `g'`. The hypothesis `sq : CartesianSquare f f' g g'` in the specification
  includes the chosen identification alpha with `pullback f g`, its agreement
  with both projections, and the commutative-square equality. No properness or
  coefficient-ring restriction is added.
* The derived object of the node is named `L` in Lean, to distinguish it from
  its representative `K`. `L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1})` is precisely D^+(Ab(X_et)). The chosen complex is
  `K : CochainComplex.Plus` of the same abelian sheaves, with
  `e : DerivedCategory.Q.obj K.obj ≅ L.obj`. This is the node's chosen
  representative, not a restriction to derived objects already given as complexes.
* Torsion cohomology is `hT : ∀ q, CategoryTheory.Sheaf.IsTorsion (H^q L.obj)`.
  The chosen integer is `a : ℤ`; `ha` states H^q(L)=0 for q<a. `hterms` says
  that each term of the chosen complex below a is `IsZero`. As the node says,
  torsion is not needed to define the filtrations, and it is retained in the
  specification's context. The complex, the isomorphism, and the term bound are
  exactly the choices the node makes after its standard-t-structure assertion.
* Canonical truncations are `TruncationCouple.truncation K q`, whose underlying
  complex is `K.obj.truncLE q`. The shifted cohomology term is
  `TruncationCouple.cohomologyComplex K q`, the single complex in degree q.
  `TruncationCouple.triangle K q` is the dependency's canonical triangle.
* The three actual triangulated functors are `hypercohomologyFirstFunctor f`
  = `(lowerStar AddCommGrpCat f).rightDerivedFunctor`,
  `hypercohomologyBaseChangeFunctor f g` = that functor followed by
  `(upperStar AddCommGrpCat g).mapDerivedCategory`, and
  `hypercohomologySecondFunctor f' g'` =
  `(upperStar AddCommGrpCat g').mapDerivedCategory` followed by
  `(lowerStar AddCommGrpCat f').rightDerivedFunctor`. These are the existing
  total derived functors, restricted in the node to bounded-below inputs;
  their restriction agrees with `rightDerivedLowerStarPlus` and
  `mapDerivedCategoryPlus`. The node's bounded-below object is supplied as L.
* For any of these functors F, `hypercohomologyD F K p q` is exactly
  H^(p+q)(F(Q(tau_le_q K))) and `hypercohomologyE F K p q` is exactly
  H^(p+q)(F(Q(H^q(K)[-q]))). These give the D,E; D_A,E_A; D',E' displayed
  in clauses (1), (2), (3), respectively. `hypercohomologyAlpha` is the
  cohomology of the truncation inclusion, `hypercohomologyG` of the projection,
  and `hypercohomologyBoundary` is the connecting homomorphism of the image
  triangle. `hypercohomologyCouple` bundles precisely these maps in the shared
  `BigradedExactCouple` structure. This uses the dependency's triangle rather
  than another truncation convention or a freely chosen exact couple.
* The spectral sequence in every clause is that couple's existing `.page r`
  and `.pageCouple (r-2)`. Initial E is E_2, with differentials of bidegree
  (r,1-r), by `BigradedExactCouple`'s shared recursion. The three E_2 clauses
  in `hypercohomologyFiltrations_spec` identify E(p,q) for p : Nat with,
  respectively, R^p f_*H^q(K), g^-1 R^p f_*H^q(K), and
  R^p f'_*g'^-1 H^q(K). Negative p is included in the integer-indexed pages
  and explicitly vanishes; it is not omitted from the sequence.
* `hypercohomologyAbutmentMap F K n q` is H^n of F applied to Q of the
  actual inclusion `K.obj.ιTruncLE q`. `hypercohomologyFiltration F K n`
  has step p equal to `imageSubobject` of that map at q=n-p. The triple
  definition uses this filtration for each of the three actual functors.
  Hence every displayed filtration formula in the node is definitionally
  present, without an arbitrary filtration as a substitute.
* Each of the three convergence clauses supplies `AlphaColimit` objects T(n),
  identified by `hT n` with H^n(F(QK)), and `LimitSubobjects` Z. Their canonical
  maps `T(n).ι p` are identified with the exact truncation-to-abutment maps.
  The image of the dependency's `imageFiltration` under this identification
  equals the explicitly defined filtration, step by step. `ConvergesTo Z T`
  is the existing notion, including regularity, the canonical E_infinity/graded
  comparison, separatedness, exhaustiveness, and the inverse-limit condition.
* Each filtration is `.IsFinite`, is the whole object for p<=0, and has zero
  inclusion for p>=n-a+1. A monomorphism with zero inclusion represents the
  bottom subobject, so this last clause says exactly F^p=0. The zero-inclusion
  form avoids an expensive search for `HasInitial` on this sheaf category.
  The pages vanish when q<a or p<0. Since n=p+q, these are precisely the
  bounds a<=q<=n in total degree n. No particular value or sign of a or n
  has been imposed.
* The last part of the specification supplies the canonical D-comparisons
  `δ`, using `mapDerivedCategoryHomologyFunctorIso` on F(tau_le_q K), and
  the canonical initial E-comparisons `φ 0` on F(H^q(K)[-q]). The three
  structure-map squares commute, including the cohomological boundary.
  The comparisons `φ r` identify each later E-page with the inverse image
  of its original page and commute with its differential.
* The cohomology comparison `c` on the first abutment is explicitly the
  dependency's `mapDerivedCategoryHomologyFunctorIso`. The last equality
  says the middle filtration step is the image of g^-1 applied to the first
  step's inclusion, followed by c. Because g^-1 is exact, this is precisely
  g^-1F^p transported to H^n(g^-1 Rf_*K). This is the first sequence after
  inverse image, as the node explicitly requires for subsequent comparison.
* The termwise g'^-1 complex has zero terms below a. The specification
  includes an isomorphism from g'^-1(tau_le_q K) to tau_le_q(g'^-1 K),
  commuting with their inclusions into g'^-1 K, and an isomorphism from
  its H^q to g'^-1H^q(K). The termwise representative and its derived
  interpretation use the recorded exact-functor factorization. Thus clause
  (3) is formed from the same triangles, and its E_2 formula uses the
  specified inverse image rather than an independently chosen complex.

Dependency declarations read and used, or used as the stated proof's shared API:

* `Sheaf.AlgebraicGeometry.EtaleCartesianSquare`: `AlgebraicGeometry.Etale.CartesianSquare`
  (dependency repair in this packet). Its `comm` uses the existing square
  comparison `AlgebraicGeometry.Etale.squareUpperStarIso` from
  `WeilConjectures.SixFunctors.BaseChange.Square`.
* `Sheaf.AlgebraicGeometry.DerivedCategories`: the encoding documented there
  for D(Ab(X_et)), D^+, `DerivedCategory.homologyFunctor`, and
  `CategoryTheory.Sheaf.IsTorsion`. The module's coefficient-ring torsion
  predicate is not substituted for the abelian-sheaf predicate.
* `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `DerivedCategory.isGE_iff`, with the
  strictly bounded representative described in their full signatures/docstrings.
* `Sheaf.CategoryTheory.TruncationCouple`: `TruncationCouple.truncation`,
  `cohomologyComplex`, `transition`, `projection`, `triangle`, and `bridgeIso`.
  The source complex-level construction and its K-injective bridge were read.
* `Sheaf.CategoryTheory.ExactCouple`: `BigradedExactCouple`, `pageCouple`,
  `initialG`, and the actual page-minus-two convention.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar` and their exactness/additivity
  instances. `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `rightDerivedLowerStar`, `rightDerivedLowerStarPlus` (their existing underlying
  `rightDerivedFunctor` is used directly).
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryPlus`, and
  `mapDerivedCategoryHomologyFunctorIso` (including its orientation).
* `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`:
  `AlgebraicGeometry.Etale.upperStar_abelian_exact`; its property classes are
  already source instances, used during elaboration.
* `Sheaf.CategoryTheory.TruncationHypercohomology`:
  `exists_truncationHypercohomology` (specification proof's first/third sequences).
* `Sheaf.CategoryTheory.ExactFunctorCouple`:
  `BigradedExactCouple.exactFunctor_couple` (specification proof's second sequence).
* `Sheaf.CategoryTheory.Filtration`: `DecreasingFiltration` and `IsFinite`;
  `Sheaf.CategoryTheory.ImageFiltration`: `DecreasingFiltration.image` describes
  image transport in the convergence proof. The node itself explains that the
  images from a truncation tower need not be images of subobjects of one fixed
  filtered source. Here they are defined directly from their truncation maps.
* `Sheaf.CategoryTheory.ExactCoupleConvergence`: `AlphaColimit`,
  `LimitSubobjects`, `imageFiltration`, `ConvergesTo`.
* `def-sp-etale-dictionary` is a reading convention without a declaration:
  this module uses its actual sheaf categories and functors directly.

Edge cases checked before and during writing: arbitrary universe u with the
small-etale site's AddCommGrpCat.{u+1}; zero complex and empty schemes; arbitrary
negative lower bound a; degrees n<a; n=a; negative p and all pages r>=2. For n<a
the full and zero steps force the abutment to be zero, as expected. For n=a the
only potentially nonzero graded piece is p=0. The generic helper imposes no
positive bound, finite coefficient group, nonempty scheme, proper map, or
characteristic hypothesis. Its objects and maps are full definitions; its only
postponed internal obligations are the two named proof theorems.

Searches performed (2026-10-11):

* `msearch.py ... leansearch "hypercohomology spectral sequence filtration canonical truncations"`:
  service unavailable (HTTP Internal Server Error). Recorded as unavailable,
  with no negative-search verdict inferred from it.
* `msearch.py ... leanfinder "hypercohomology filtrations from canonical truncations of a bounded below complex and a derived direct image"`:
  eight hits, all general cochain/complex truncation declarations; none defines
  these three filtrations or the proper-base-change spectral sequences.
* `msearch.py ... loogle "DerivedCategory.TStructure.t, truncLEι, imageSubobject"`:
  zero hits, unknown identifier truncLEι. Exact t-structure and complex
  truncation declarations were then inspected by source search.
* `msearch.py ... grep "hypercohomology|truncationFiltration|HypercohomologyFiltrations" Algebra/Homology`:
  zero hits.
* `rg` for hypercohomology filtration names in Mathlib, `WeilConjectures`, and
  `lean/Sheaf`: no existing declaration of the three filtrations. Existing
  `TruncationHypercohomology` supplies the abstract theorem, not this definition;
  `HypercohomologyFirstPage` concerns a different Cartan--Eilenberg sequence.
  The source's `DeligneLaumon/Reduction/FormalSteps.lean:117` mentions this node
  in a compact-support weight-bound docstring, not a matching definition.
* `tools/blueprint_refs.py search "hypercohomology filtrations"`: exactly this node.
* `rg` for `structure CartesianSquare`, `def CartesianSquare`, and
  `Etale.CartesianSquare` across Mathlib, source, and project: no collision.
  The recorded `squareUpperStarIso` was opened in full: it takes only a CommSq
  and does not encode its being cartesian or a chosen fibre-product identification.

The copied blueprint literature path is not present on this machine. The node's
full statement/proof and the primary Stacks sources were inspected:
[0DDE](https://stacks.math.columbia.edu/tag/0DDE) for the two étale sequences and
[015J](https://stacks.math.columbia.edu/tag/015J) for their finite filtrations and
convergence. The explicit truncation-couple refinement follows the detailed node
and its recorded spectral-sequence dependencies. No statement correction or
STATEMENT-DISPUTED issue is needed.

Validation: the two modules compile together on the server, dependency first,
with no errors or warnings (4.0 seconds in the last combined check). All theorem
proofs are `sorry`; no stage-3 proof is supplied. The delivery dry run printed OK: compilation and preflight pass except for the
second reading, which the designated second reader supplies. Nothing was pushed.

## Dependency modules

`def-weil-pbc-cartesian-square`: the recorded
`AlgebraicGeometry.Etale.squareUpperStarIso` constructs the inverse-image functor
comparison for any commutative square, so it cannot supply the chosen cartesian
square required by this item. The new dependency module
`Sheaf.AlgebraicGeometry.EtaleCartesianSquare` defines `CartesianSquare` with a
chosen scheme isomorphism to `pullback f g`, both projection equalities, and
`CommSq g' f' f g`. Its inverse-image comparison is the existing
`squareUpperStarIso` on that `comm` field, using the source's canonical composition
isomorphisms and their identity/pasting coherence. The node copy changes only
`lean`, with the required explanation in `lean.note`; its mathematical statement
and all dependencies remain intact. This is rule (B), not a new definition node.

## Second reading by C1

I reread the node statement and both delivery modules against the source place.
The node's introduced objects are schemes X, X', Y, Y' and maps f, f', g, g',
a chosen cartesian identification, a bounded-below derived object K, an integer a,
a representative complex Kᵇ and its canonical truncations.  These render as
`CartesianSquare f f' g g'`, `L`, `e`, `a`, `K`, `TruncationCouple.truncation`,
and `TruncationCouple.cohomologyComplex` in the specification.  The module's
`hypercohomologyFiltrations` definition itself is the requested triple of
`DecreasingFiltration`s, one for `Rf_*`, one for `g⁻¹Rf_*`, and one for
`Rf'_*g'⁻¹`, with each step definitionally the image of the canonical
truncation-to-abutment map.  This is exactly the node's final notion and does
not add hypotheses to the definition.

The three node clauses are rendered by `hypercohomologyD`, `hypercohomologyE`,
`hypercohomologyCouple`, and `hypercohomologyFiltrations_spec`: clause (1) uses
`hypercohomologyFirstFunctor`, clause (2) uses
`hypercohomologyBaseChangeFunctor`, and clause (3) uses
`hypercohomologySecondFunctor`.  The specification includes the node's E₂
identifications, page vanishing bounds, finite image filtrations, convergence
objects and image-filtration equalities, as well as the base-change page,
differential, boundary, and abutment comparison maps.  The `p : ℕ` binders in
those E₂ clauses are coerced to the integer bidegree expected by
`BigradedExactCouple`; negative integer page indices remain present in the
vanishing clauses.  The lower bound is expressed by `hterms` and `ha` with no
sign or positivity restriction on `a`; torsion is retained as `hT` exactly as
in the node, although it is not used by the raw filtration definition.

The dependency repair was also reread.  `AlgebraicGeometry.Etale.CartesianSquare`
introduces precisely the four scheme morphisms, a chosen isomorphism
`X' ≅ pullback f g`, both projection equations, and the commutative square.
Its comparison is the recorded `squareUpperStarIso` applied to `comm`; no
second inverse-image comparison is defined.  This supplies the dependency's
chosen cartesian-square notion and its required comparison data.

Edge cases checked: arbitrary universe `u`, empty schemes and zero complexes,
empty/zero sheaves, negative `a`, `n<a`, `n=a`, `n=0`, negative `p`, and every
page index `r ≥ 2`.  The formulas retain all integer indices and impose no
nonemptiness, properness, coefficient-characteristic, or finiteness hypothesis.

Searches were independently repeated with `rg` over Mathlib, the source
`WeilConjectures`, and `lean/Sheaf`, plus LeanFinder/Loogle searches for
hypercohomology, truncation filtrations, and image filtrations.  Only the
abstract truncation-hypercohomology and exact-couple APIs were found; no
matching three-filtration declaration exists.  The unavailable LeanSearch
service was recorded in the worker search log.  No mismatch was found, so no
statement, definition, or dependency field was changed in this second reading.
