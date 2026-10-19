## Worker report

Delivered module: `Sheaf.CategoryTheory.BoundedBelowCechConeComparison`.
Main declaration: `HomologicalComplex₂.boundedBelow_cech_cone_comparison`.
The two auxiliary definitions `cechTotalMapCone` and `cechTotalMapConeStep` have real data:
they use the existing total map, ordinary mapping cone and finite suprema of canonical
summand images. They are helpers of this node, not independent replacement notions.
The single theorem is postponed with `sorry`; no theorem is proved here.

I read the complete node and its four proof steps, every statement dependency and its
recorded interface, Stacks `homology.tex` Tags 0130/0132 (in particular
`lemma-first-quadrant-ss`, which assumes finite diagonals), and the ordinary cone convention
of Tag 014E. I also read the current source through `scompile.py --source` for the upstream
filtration, convergence, and double-complex spectral-sequence modules missing or stale in
the older local checkout. No mathematical correction is needed. The natural statement,
source, proof, and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The commutative coefficient ring is `{R : Type u} [CommRing R]`. Module objects have the
  independent explicit universe `ModuleCat.{v} R`. There is no finiteness, nonzero-ring,
  Noetherian, injectivity or derived-category assumption.
- The commuting double cochain complexes are the existing
  `HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)`.
  The outer index is horizontal `q`; the inner index is internal `j`.
  The binder `f : A ⟶ B` is exactly a morphism commuting with both differentials.
- The common integer lower bound is `a : ℤ`. The hypotheses `hA` and `hB` state, separately
  for both complexes, `q < 0 ∨ j < a → IsZero ((A.X q).X j)` (and the same for B).
  They do not replace termwise support by cohomological support or require `a ≥ 0`.
- The ordinary total is Mathlib `total (ComplexShape.up ℤ)`, with canonical map
  `total.map f (ComplexShape.up ℤ)`. Its sign convention is horizontal coefficient 1,
  vertical coefficient `(-1)^q`. ModuleCat colimits provide the actual diagonal coproducts;
  no extra `HasTotal` assumption is inserted. Under hA/hB only `0 ≤ q ≤ n-a` contribute
  to degree n, so these are precisely the finite diagonal sums of the node.
- The total cone is the real definition `cechTotalMapCone f`, using the canonical total map.
  Column cones are the existing `CochainComplex.mappingCone (f.f q)`. Mathlib orders its
  biproduct as source shifted by one followed by target; swapping these two factors gives
  exactly the node's `B^(q,j) ⊕ A^(q,j+1)` with the ordinary cone differential. No arbitrary
  comparison morphism or alternative cone is assumed.
- The column filtration is the existential `F`, uniquely specified degreewise by
  `F.complexStep p n = cechTotalMapConeStep f a p n`. The latter is the finite supremum,
  for `p ≤ q ≤ n-a+1`, of the images of the B diagonal summand followed by `mappingCone.inr`,
  and the A diagonal summand in degree n+1 followed by `mappingCone.inl`.
  This is the image of the column filtration of the column-cone bicomplex under the signed
  total-cone identification. Multiplication of the A summand by `(-1)^q` leaves its image
  subobject unchanged. Terms at q<0 and beyond the upper bound are zero, by the support
  assumptions. No globally finite filtration over all complex degrees is imposed.
- The spectral sequence is `E : CohomologicalSpectralSequence (ModuleCat.{v} R) 1`.
  The first-page clause gives
  `Nonempty ((E.page 1).X (q,j) ≅ (mappingCone (f.f q)).homology j)` for all integers q,j.
  This includes the displayed range q≥0,j≥a-1; outside it both sides are zero. Extending
  the page by those forced zero entries adds no mathematical assertion.
- To specify that this is the spectral sequence of F, `e₁` identifies its first page with
  `(F.gradedPiece q).homology (q+j)`. The existential exact couple X is identified with
  filtration-step cohomology by eD. Its alpha maps are identified with the inclusions by
  the alpha equation; its initial gamma maps are identified with the canonical graded
  projections by the initialG equation. The derived couple pages are identified by eC
  with E's pages, compatibly with their differentials. These equations specify the
  filtration construction rather than quantify over an arbitrary unrelated spectral sequence.
- The abutment is the cohomology of the actual total-map cone: `eH n` identifies the
  alpha-colimit `(H n).obj` with `(cechTotalMapCone f).homology n`. Its cocone equation
  identifies every canonical colimit leg with the cohomology map of the appropriate
  filtration inclusion. Coordinates `(P,Q)=(2q+j,-q)` preserve total degree P+Q=q+j;
  colimit index P corresponds to filtration index P-n in total degree n.
- Convergence is the recorded `X.ConvergesTo L H` of `def-sp-convergence`, including
  regular cycles, weak convergence via the canonical quotient maps, separated/exhaustive
  image filtration, and its inverse-limit completeness. It is not replaced by a bare
  existence of isomorphisms between arbitrary objects.
- `G n` is pinned by `(G n).step p = imageSubobject (homologyMap (F.step p).arrow n)`.
  The explicit clause `(G n).IsFinite` is the node's finite abutment filtration in every
  integer total degree. The stable exact-couple term at `(2q+j,-q)` is identified with
  `(G (q+j)).gradedPiece q`.
- Stabilization is the final existential block: for every q,j there is an integer N≥1
  such that for every s≥N both incoming and outgoing differentials are zero, the page-s
  entry is isomorphic to the fixed page-N entry and to the corresponding graded abutment
  piece. This states stabilization in every bidegree, including the forced zero entries.
- The last conjunct quantifies over *every* `r : ℤ`, assumes precisely column-cone
  cohomology vanishing for `0 ≤ q` and `j ≤ r`, and concludes
  `∀ n : ℤ, n ≤ r → IsZero ((cechTotalMapCone f).homology n)`.
  There is no quasi-isomorphism hypothesis or loss of the degree n=r endpoint.

Dependency interfaces reused:

- `def-sp-double-complex-total`: `Sheaf.CategoryTheory.DoubleComplexTotal`, reusing
  Mathlib's `HomologicalComplex₂`, `total`, `total.map`, and `ιTotalOrZero`.
  Its `firstFiltration` formula is specifically first-quadrant (upper bound n); it is
  not applied incorrectly to a negative internal lower bound. Our node's explicit
  cone-tail helper supplies the needed upper bound n-a+1.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  importing the existing cochain, cohomology, and ordinary `CochainComplex.mappingCone`
  constructions. The theorem itself concerns complexes and needs no localization choice.
- `def-sp-spectral-sequence`: `Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `CategoryTheory.SpectralSequence` and its `CohomologicalSpectralSequence` specialization.
- `def-sp-filtration`: `WeilConjectures.CategoryTheory.Abelian.Filtration`,
  `CategoryTheory.DecreasingFiltration`, its steps and graded quotients; `IsFinite` is
  provided by its existing compatibility module imported through DoubleComplexTotal.
- `def-sp-convergence`: `WeilConjectures.CategoryTheory.ExactCoupleConvergence`,
  `BigradedExactCouple.ConvergesTo`, `LimitSubobjects`, `AlphaColimit` and `pageInfinity`.
  Its exact-couple input is the existing `WeilConjectures.CategoryTheory.ExactCouple`.
  The recorded convergence module uses PBCDecreasingFiltration internally. We use that
  interface directly for its canonical colimit filtration; G is identified with the
  corresponding reindexed image filtration via the displayed cocone and graded comparisons.
  No competing convergence or filtration definition is introduced.
- Added already-landed statement dependency `def-sp-filtered-complex-subquotients`:
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`, using `complexStep` and
  `complexQuotientπ` for the canonical degreewise filtration and graded projection.
  This is the authorized addition of an existing landed definition dependency, with no
  new node or dependency repair.
- Proof import: `WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex` contains the
  current `HomologicalComplex₂.exists_spectralSequence` and the first-quadrant filtration
  construction used by `thm-sp-double-complex-spectral-sequences`. The old recorded
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` now explicitly directs readers
  to this module; I read the current source rather than relying on the stale local file.

Edge cases checked before and after writing:

- A=B=0, the zero coefficient ring, and f the identity: all relevant column/total cone
  cohomology vanishes and the assertion gives the expected zero spectral sequence.
- A=R concentrated at (q,j)=(0,a), B=0: its cone has nonzero cohomology in degree a-1.
  The upper bound n-a+1 includes q=0 at n=a-1; this tests the crucial cone shift and
  rules out the incorrect lower bound a. At r=a-1 the vanishing hypothesis correctly fails.
- Any negative a is permitted, and total degrees below a-1 have zero cone terms.
  If r<a-1, the vanishing conclusion holds with no missing lower-degree exception.
- If n-a+1<p the finite index interval is empty, giving bottom; for sufficiently
  negative p the whole cone term is included. Negative horizontal indices contribute zero.
- The argument n=q+j≤r with q≥0 gives j≤r even when n or r is negative. In particular
  n=r is covered. All integer degrees are explicit, with no natural-number truncation.
- All universes and variables are explicitly declared. No extra equality between the
  coefficient and module universes, no finite-generation hypothesis and no nonempty-index
  hypothesis is used.

Searches (fresh, with the prescribed wrapper):

- LeanFinder: "bounded below double complex column mapping cones spectral sequence E1
  cohomology converges cone total map vanishes through degree r". Eight hits: mapping-cone
  homology-sequence lemmas, ordinary cone component identities and a factorization lemma;
  none states the column-cone spectral sequence or vanishing through a fixed degree.
- Loogle: `CochainComplex.mappingCone, HomologicalComplex₂.total`: OK, zero hits.
- Mathlib grep: `cone.*total|total.*cone|column.*spectral` in `Algebra/Homology`: OK, zero hits.
- LeanSearch: "mapping cone total map bounded below double complex column spectral sequence".
  Eight hits include `CochainComplex.mappingCone`, `HomologicalComplex₂.total`, spectral
  objects of ordinary mapping cones and tensor-bifunctor summand maps; none is the theorem.
- `rg` in the upstream project and `lean/Sheaf` for the item id, bounded-below cone and
  column-cone names found no exact existing declaration. The nearby
  `FirstQuadrantVerticalConeFiltration` handles natural-indexed bicomplexes and the cone
  filtration, without this arbitrary integer internal bound and truncated vanishing theorem.
- DAG/blueprint searches for bounded-below cones and column-cones found this node and
  related first-quadrant cone filtration/graded lemmas. None is the full assertion here.
  A final name search for `cechTotalMapCone` and `boundedBelow_cech_cone_comparison` in
  Mathlib, the upstream project and `lean/Sheaf` had no pre-existing match.

Compilation: `scompile.py Q13 lem-trf-bounded-below-cech-cone-comparison` on the delivered
module succeeded cleanly (only the expected postponed theorem). The final import version
is compiled again by the required dry-run preflight. All lines are at most 100 characters.
The record contains the exact multiline theorem signature, all three declaration names,
branch `newtargets-dag`, group Q13 and the UTC date. No source or shared repository file
was edited directly; all work is in the prescribed sandbox.

## Signed cone-total identification

For completeness, the source's omitted comparison is the map T on the summand of column
q given by T(b,x)=(b,(-1)^q x). Let e=(-1)^q. In Tot D, the differential of (0,x)
has components e*f*x in B^(q,j+1), d_h*x in A^(q+1,j+1), and -e*d_v*x in A^(q,j+2).
Applying T multiplies the horizontal A component by (-1)^(q+1) and the vertical A
component by e. Thus T*d has components e*f*x, -e*d_h*x and -d_v*x. The differential
of the ordinary cone of Tot f applied to (0,e*x) gives exactly those same components.
On B summands both sides are d_h*b+e*d_v*b. Since e squared is 1, T is invertible by
the same formula. It preserves each column sum and hence its induced cohomology image
filtration. Relabeling j=k+a-1 leaves the horizontal sign e unchanged and makes D
first-quadrant. This is exactly the four-step proof recorded in the node and docstring.

## New nodes

None. The two auxiliary definitions belong to the item's own cone-filtration construction.
The only added statement dependency is the already-landed filtered-complex subquotient node.
No statement dispute, unit change, or dependency repair is needed.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
