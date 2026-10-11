## Worker report

The module `Sheaf.CategoryTheory.TruncationHypercohomology` states
`CategoryTheory.exists_truncationHypercohomology`. It binds abelian Grothendieck
categories `A` and `B`, a left exact additive functor `F`, a bounded-below complex
`K`, an integer lower bound `a`, and `ha : ∀ q < a, IsZero (H^q K)`. Its witness
`X : BigradedExactCouple B 0` is identified with the recorded truncation-couple
terms and maps. The first conjuncts give exact-couple structure maps and the
naturality equations for `alpha`, `f`, and `g`.

The E2 clause is the existential natural comparison for every `p : ℕ` and
`q : ℤ`; its component is written with the shift isomorphism, the right-derived
comm-shift isomorphism, the homology shift isomorphism, and
`homologyRightDerivedFunctorObjSingleFunctorIso`. The final `eK` equation identifies
`X.E p q` with `(F.rightDerived p).obj (H^q K)`. The following clauses render,
in order, negative-p vanishing, lower-row vanishing, page quadrant and total-degree
bounds, finite diagonal support, differential stabilization, eventual cycle and
boundary constancy, regularity, alpha-image vanishing, completeness, and the
existence of limiting subobjects and abutment data.

The abutment witness `H` is definitionally `H^n(RF K)`. `j` is the map induced by
`K.truncLE q -> K`, and `c` is its `q=n` specialization. The clauses state that
`c` is an isomorphism, that `FA` is the alpha-image filtration and `FH` is its
image filtration, that the filtration is finite/exhaustive/separated and inverse
complete, and that negative graded pieces vanish. The final existential records the
iterated-alpha map `lambda`, the quotient-to-page isomorphism `psi`, the graded
comparison `grc`, the stable-page identification, `Theta`, and their commuting
relations; it ends with `X.ConvergesTo` for the diagonal alpha-colimit.

The initial statement's stable-page index was corrected to
`max 2 (max (q-a+2) (p+1))`: the spectral sequence begins at page 2, so the
unclamped formula can be below 2 for negative indices. The regular/coregular wording
was corrected to match `def-sp-convergence`, whose `IsRegular` is eventual constancy
of cycles; boundary constancy is also asserted separately. The already cited shift
identification node was added to `stmt_deps`.

Dependencies used: `Sheaf.CategoryTheory.TruncationCouple` (`CategoryTheory.truncationCouple`,
`CategoryTheory.TruncationCouple.D/E/alpha/f/g`, `bridgeIso`); 
`Sheaf.CategoryTheory.ExactCouple` (`CategoryTheory.BigradedExactCouple`, `pageCouple`,
`page`, `pageDifferential`); `Sheaf.CategoryTheory.ExactCoupleConvergence`
(`IsRegular`, `IsComplete`, `LimitSubobjects`, `ConvergesTo`, filtrations and pages);
`Sheaf.CategoryTheory.Filtration` and `ImageFiltration`;
`Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
(`exists_rightDerived_shift_identification_nonneg` and
`isZero_rightDerived_shift_identification`); and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
(`homologyRightDerivedFunctorObjSingleFunctorIso`). Grothendieck enough-injective
instances are imported from Mathlib.

Edge cases checked: `p<0`, `q<a`, `n<a`, zero cohomology objects, negative total
indices, and page indices below 2. The latter motivated the recorded correction.
The empty/zero abelian categories are permitted by the explicit typeclass binders;
no nonemptiness or nonzero hypothesis is introduced.

Searches made: `msearch.py leanfinder` for “truncation hypercohomology spectral
sequence E2 derived functors cohomology convergence” (truncation lemmas only, no
spectral-sequence statement); `msearch.py loogle` for
`CategoryTheory.Functor.rightDerived` (right-derived declarations only);
`msearch.py grep` for truncation/spectral/exact-couple keywords (no matches in
Mathlib); `msearch.py leansearch` for exact-couple hypercohomology (service
unavailable, recorded as such); `rg` over `WeilConjectures` and `lean/Sheaf` found
only the dependency declarations and no existing theorem of this statement.

No `STATEMENT-DISPUTED` remains after the page-index correction.

## Statement corrected

The old statement used `r_0(p,q):=max(q-a+2,p+1)`, which can be less than 2,
although `E_r` is defined only for `r≥2`; it also called eventual boundary
constancy “regular” although the recorded convergence definition calls cycle
constancy regular. The source is the blueprint node and Stacks 0BDU/0BDV. Fourteen
nodes cite this theorem; all uses concern the E2 page, quadrant, finite filtration,
or convergence and hold after the correction. None is edited.

Citer names and status: cor-fin-deligne-open-finite-coefficients (holds true);
def-weil-pbc-hypercohomology-filtrations (holds true); lem-fin-lisse-field-dual (holds true);
lem-fin-proper-bounded-constructible (holds true); lem-pc-derived-direct-image-preserves-direct-sums (holds true);
lem-pc-derived-direct-image-preserves-qcoh (holds true); lem-pc-direct-image-bounded-coherent (holds true);
lem-sc-qcoh-acyclic-derived-sections-comparison (holds true); lem-sf-projection-finite-constant (holds true);
prop-sf-localization-all-stages (holds true); prop-weil-pbc-restriction-direct-image (holds true);
thm-fin-deligne-generic-open (holds true); thm-sf-direct-image-tor-amplitude (holds true);
thm-weil-etale-geometric-biduality (holds true).

## Earlier second reading (a previous round; superseded)

I reread the corrected node and module independently. The binders match the node's
functor, categories, bounded-below complex, lower bound, and all stated indices. The
module renders exactness, the E2 comparison, quadrant and finite-support clauses,
cycle/boundary stabilization, completeness, the image filtrations, graded-piece
isomorphisms, and convergence. The only mismatch found was the unclamped stable page
and the regular/coregular terminology; both are corrected in the node and Lean.
Every citer remains valid: cor-fin-deligne-open-finite-coefficients,
def-weil-pbc-hypercohomology-filtrations, lem-fin-lisse-field-dual,
lem-fin-proper-bounded-constructible, lem-pc-derived-direct-image-preserves-direct-sums,
lem-pc-derived-direct-image-preserves-qcoh, lem-pc-direct-image-bounded-coherent,
lem-sc-qcoh-acyclic-derived-sections-comparison, lem-sf-projection-finite-constant,
prop-sf-localization-all-stages, prop-weil-pbc-restriction-direct-image,
thm-fin-deligne-generic-open, thm-sf-direct-image-tor-amplitude, and
thm-weil-etale-geometric-biduality.

## Citer check

The correction holds for cor-fin-deligne-open-finite-coefficients;
def-weil-pbc-hypercohomology-filtrations; lem-fin-lisse-field-dual;
lem-fin-proper-bounded-constructible; lem-pc-derived-direct-image-preserves-direct-sums;
lem-pc-derived-direct-image-preserves-qcoh; lem-pc-direct-image-bounded-coherent;
lem-sc-qcoh-acyclic-derived-sections-comparison; lem-sf-projection-finite-constant;
prop-sf-localization-all-stages; prop-weil-pbc-restriction-direct-image;
thm-fin-deligne-generic-open; thm-sf-direct-image-tor-amplitude; and
thm-weil-etale-geometric-biduality.

## Second reading by G1

Independent second reading of the sandbox node and the 211-line module, with
`TruncationCouple.lean`, `KInjectiveBridge.lean`, `ExactCouple.lean`,
`ExactCoupleConvergence.lean`, `Filtration.lean`, `ImageFiltration.lean`,
`DerivedCategory/ShiftIdentification.lean`, and upstream
`RightDerivedFunctor/PlusCompatibility.lean` open. There are no new nodes or
replacement dependency modules in this delivery.

Source reading first: the local literature tree omits the Stacks checkout, so I
read the available Stacks TeX copies `/home/ubuntu/c1-stacks-review/derived.tex`
and `/home/ubuntu/c1-stacks-review/homology.tex`: labels
`lemma-two-ss-complex-functor` (015J), `lemma-negative-vanishing` (05TC),
`definition-bounded-ss` (0BDU), `lemma-relate-boundedness` (0BDV),
`definition-filtered-complex-ss-converges` (012U), and
`lemma-biregular-ss-converges` (012W). 015J assumes a left exact functor between
abelian categories and a bounded-below complex with a Cartan-Eilenberg resolution;
it gives the second page, bounded convergence, and finite abutment filtrations.
The node uses the blueprint's truncation-couple route, rather than claiming that
Stacks constructs this exact couple. Grothendieck hypotheses provide the required
resolutions. 05TC gives negative vanishing and the canonical truncation comparison.
0BDU/0BDV identify regularity with eventual cycle constancy and coregularity with
boundary constancy. 012U includes exhaustiveness, separatedness and the quotient
inverse limit; 012W explains why finite filtrations give that limit.

The existing correction agrees with these sources. The old stable-page expression
can be negative (p=-2, q=a-4 gives -1), although the spectral sequence starts at 2.
The corrected `max 2 (max (q-a+2) (p+1))` retains the original differential bound
and all nonzero terms. The terminology correction retains both stabilization
assertions. I checked the correction's citer set against every repository node:
exactly 14, with none missing. I opened in full
`def-weil-pbc-hypercohomology-filtrations` (statement and proof): its sequences (1)
and (3) use the E2 comparison, the truncation-image filtration, its finite range,
and convergence, all unchanged. I also opened
`lem-pc-derived-direct-image-preserves-qcoh` (statement and both proof steps): its
bounded truncation uses clauses 3, 5 and 6 and a finite stable page to propagate
quasi-coherence. The corrected page bound supplies precisely that page. Both
`holds: true` verdicts are justified; neither citer needs an edit.

Object/hypothesis/conclusion checklist, written from the node before matching:

- Two Grothendieck abelian categories: `{A : Type u₁}` and `{B : Type u₂}` with
  independent `Category.{v₁}`, `Category.{v₂}`, `Abelian`, and
  `IsGrothendieckAbelian.{v₁/v₂}` binders. Verdict: exact. The dependency's
  Mathlib match explicitly uses the hom universe for Grothendieck smallness.
  `HasDerivedCategory.{w₁/w₂}` chooses the derived-category models; Mathlib's
  `HasDerivedCategory.standard` supplies them at `max u v`. These structural
  binders impose no extra geometric, finiteness, or ring assumptions.
- A left exact additive functor v: `(F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F]`. Verdict: exact by the recorded
  `def-sp-left-exact-additive` match (additivity and preservation of kernels are
  equivalent to this finite-limit formulation in abelian categories).
  `F.rightDerived p` is the recorded ordinary derived functor, with p natural;
  enough injectives and K-injective resolutions come from Grothendieck instances.
- Bounded-below complex, integer cohomological lower bound: `(K :
  CochainComplex.Plus A) (a : ℤ)` and `ha : ∀ q, q < a → IsZero
  (K.obj.homology q)`. Verdict: exact. The Plus definition requires some strict
  termwise lower bound, independently of a; the statement does not incorrectly
  require the terms below a to vanish.
- Canonical truncations and chosen-resolution RF: `TruncationCouple.truncation`
  is the smart `K.obj.truncLE`; `D/E` use the recorded
  `rightDerivedCohomologyWithResolution` and Grothendieck resolution choice.
  `bridgeIso` identifies those cohomologies with `F.rightDerivedFunctor`.
  Verdict: the dependency's objects, not private substitutes.
- Initial maps and every exact couple: existential `X : BigradedExactCouple B 0`,
  `hD/hE`, and the three equations for `X.alpha`, `X.f`, `X.initialG` identify
  the terms and arrows with the dependency's truncation couple. Exactness is
  carried by the structure fields, and every `pageCouple` is again such a
  structure. Verdict: clause 1, including all iterated couples, is present.
  The dependency defines `page r` as `(pageCouple (r-2)).E`; its differential
  has bidegree `(r,1-r)` for r>=2.
- E2 natural comparison and negative-p vanishing: `∀ p : ℕ, ∀ q : ℤ, ∃ e :
  ... ≅ ...` is a natural isomorphism on all Plus complexes. The equation for
  each `e.app L` specifies the single-complex shift identification, RF's shift
  comparison, cohomology's shift comparison and the upstream ordinary-derived
  comparison in that order. `eK` then transports `X.E p q` through `bridgeIso`
  to that component. The separate integer-p `IsZero (X.E p q)` clause handles
  p<0. Verdict: clause 2, both naturality and the specified composite, exact.
  The worker report's assertion that the ShiftIdentification declarations are
  directly used is imprecise: their signatures were checked, but this module
  spells out their composite in the ambient derived category using the shared
  upstream definitions and PlusCompatibility. It defines no second shift or RF.
- Quadrant and finite diagonals: `q<a → IsZero (X.D p q)`; for every r>=2,
  `(p<0 ∨ q<a) → IsZero (X.page r p q)`; and the nonzero-page implication
  `a≤q ∧ q≤p+q ∧ 0≤p ∧ p≤p+q-a`. `X.IsBounded` is precisely finite support
  of the initial page on each total-degree diagonal. Verdict: clause 3 exact;
  later-page finite support follows from its displayed integer interval.
- Stabilization and limiting page: the two zero differential equations use
  `pageCouple (r-2)` and the original strict bound `max (q-a+1) p < r`.
  The Z/B equations use tower index `t-2` and the clamped integer bound;
  `X.IsRegular` is eventual Z constancy, as its dependency now defines it.
  `L : X.LimitSubobjects` carries the GLB of Z and LUB of B; the subsequent
  `pageInfinity L ≅ page r₀` clause identifies the quotient with the stable
  page. Verdict: clause 4 exact, including coregularity through B constancy.
- Completeness: `imageSubobject (X.incomingAlphaIter r p q) = ⊥` for
  `q-a<r`, and `X.IsComplete`. The dependency's iterate has source
  `D (p+r) (q-r)`; its completeness predicate expresses zero intersection
  without assuming an unrelated complete lattice. Verdict: clause 5 exact.
- Canonical abutment and maps: `H` and `hH` identify H^n with
  `H^n(F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj))`.
  The equation for `j n q` is cohomology of RF applied to `K.obj.ιTruncLE q`,
  transported by `hD`, `bridgeIso`, and `hH`. `c n` is the q=n specialization,
  and `IsIso (c n)` asserts the required comparison isomorphism. Verdict: the
  node's maps, with no arbitrary morphism hypothesis.
- Filtrations: `FA.step p` is the incoming-alpha image for p>=0 and top for
  p<=0; `FH = FA.image c` uses the recorded image-filtration definition.
  `FH.step p = imageSubobject (j n (n-p))` fixes the requested formula for
  every integer p. The top and bottom bounds and `IsFinite`, `IsExhaustive`,
  `IsSeparated`, `IsInverseLimit` assert every remaining part of clause 5.
  The inverse-limit predicate is the canonical quotient-cone universal
  property, so existence is included. Verdict: exact.
- Graded abutment: for p>=0 the existential lambda has the prescribed u,v
  at r=max(p+3,q-a+2), equals the iterated alpha map, and is an isomorphism.
  The recursive equations for `inc` fix the inclusions of derived D-terms.
  `IsIso lift` and its inclusion equation identify F^p with D_r^{u,v}.
  The cokernel equation for `psi.hom` specifies the map induced by g_r,
  rather than just an unrelated graded isomorphism. The two `cStep` equations
  specify the restriction of c and its induced map `grc` on the quotient.
  The projection equation for `stable` identifies the stable page with the
  limiting quotient through `hZ`. `Theta = grc.symm ≪≫ psi ≪≫ stable`
  is exactly the node's Theta. For p<0 both graded pieces and infinity-page
  terms are asserted zero. Verdict: every map and clause of part 6 present.
- Unconditional convergence: `AH : ∀ n, X.AlphaColimit n`, `hAH`, and the
  equation for its cocone maps identify the diagonal colimit with H and the
  same j maps. `X.ConvergesTo L AH` uses the recorded convergence definition
  (regularity, canonical weak convergence, separated/exhaustive filtration,
  quotient inverse limit), without a lim¹ hypothesis. Verdict: exact.

Edge cases: p=0 is represented by the natural index 0 and alpha iterate 0;
q=a is allowed; n=0 and all negative integers are unrestricted. If n<a, every
page on the diagonal vanishes, and the overlapping full/zero filtration bounds
are consistent because H^n=0. For p<0 or q<a the stable bound remains >=2;
for p>=0 the graded-comparison bound is >=3 and u<=-1. All uses of `toNat`
for positive iterates/pages are guarded by these bounds. A zero complex, zero
functor, or trivial abelian category is allowed; no nonzero objects are assumed.
Empty index sets, schemes and characteristic are not parameters of this abstract
categorical statement. Independent object, hom and derived universes are bound
explicitly, with no equality between A and B universes. There is no hidden finite
cohomological-dimension assumption.

Independent searches: `msearch.py leanfinder` with “bounded below hypercohomology
derived functor spectral sequence finite filtration” returned eight elementary
truncation/vanishing declarations, no theorem matching this node; `loogle` with
`"spectral"` returned unrelated topological spectral-map declarations.
`msearch.py leansearch` with “right derived functor of cohomology truncation spectral
sequence” reports Internal Server Error (unavailable, no mathematical verdict).
`msearch.py grep` with `hypercohomology|truncation.*spectral|spectral.*truncation`
returned zero Mathlib hits. Direct `rg` for hypercohomology, spectral sequence and
the proposed declaration name in Mathlib/Algebra/Homology, upstream
WeilConjectures/CategoryTheory and project lean/Sheaf/CategoryTheory found the
shared spectral-object machinery and upstream
`CategoryTheory/SpectralSequence/Grothendieck.lean`. I opened its hypotheses and
construction: that theorem concerns two composable functors, an acyclicity
condition, and RF(X) for an object X, not an arbitrary bounded-below K with these
six truncation-couple assertions. Mathlib's general spectral-object page
construction also does not state the present theorem. There is no exact existing
match to record instead of this module, and no new/private definitions here.

No mathematical or Lean repair was needed beyond the worker's already recorded
correction. I appended this independent reading and clarified above the actual
use of the shift-comparison definitions. The header, source docstring and all
seven natural-language proof steps are present. There is one named theorem with
`by sorry`, no new data definition, no private/local notation or instance, and
no proof added. I checked the stored `lean.statement` character-for-character
against the signature: equal. Every Lean line is <=100 characters. The explicit
single-file compile with `scompile.py G1 thm-sp-truncation-e2` returned exit 0,
compiled in 2.8 seconds with no errors or warnings.
