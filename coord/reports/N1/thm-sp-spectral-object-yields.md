## Worker report

Module: `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`.
Declaration: `CategoryTheory.boundedFilteredComplex_spectralSequence`.
This is one theorem, with proof `sorry`; it introduces no definitions, instances, or
local notation. All universes and object/index variables are bound explicitly.

I read the item's statement and all six proof steps, the three original statement
dependencies and their recorded declarations, the added landed dependency declarations,
and the CompactObject example with its node's `lean` record. The node's six proof steps
are reproduced in the declaration docstring. The source file named in `source.document`
is absent in this clone; the attempted raw GitHub URL returned 404. For the mathematical
source I opened https://stacks.math.columbia.edu/tag/012K, reading the cycle/boundary
formulas and Lemmas 12.24.2--12.24.4, Definition 12.24.5, and convergence definitions
and Lemma 12.24.11. The blueprint unit record `dag/units/sk-prop-av-pqf-finite.json`
is about proper quasi-finite morphisms, not this spectral-sequence statement; no unit
statement or item statement is changed.

Hypotheses and clauses, in the order of the node:

- Abelian category: `(C : Type u) [Category.{v} C] [Abelian C]`. Object and morphism
  universes are arbitrary; no enough-injectives, countable coproducts, or complete
  subobject lattice is assumed.
- Complex with bounded decreasing filtration by subcomplexes: the domain of `S` is
  `ObjectProperty.FullSubcategory (fun U : FilteredObject (CochainComplex C ℤ) =>
  U.filtration.IsFinite)`. For its object `U`, `U.obj.obj` is the complex,
  `U.obj.filtration` is a `DecreasingFiltration` in the abelian category of complexes,
  and `U.property` is boundedness. `IsFinite` gives arbitrary integer bounds, with the
  lower step top and upper step bottom; it is not the special convention F⁰=K.
  The bound applies to the filtration of the complex, as in the node's wording
  and the existing ZB-description delivery. In particular all degreewise filtrations
  are finite, as needed by Stacks Lemma 12.24.11.
- `X^[a,b]`: the imported `DecreasingFiltration.complexQuotient a b h` is exactly
  the cokernel of the inclusion FᵇK→FᵃK. Its projection is `complexQuotientπ`.
  `gradedPiece p` is definitionally this quotient for b=p+1.
- Cohomological sequence for r≥1 and the differential bidegree: the codomain of `S`
  is Mathlib's `CohomologicalSpectralSequence C 1`, i.e. pages of complex shape
  `ComplexShape.up' (r,1-r)`, with the homology-to-next-page isomorphisms of the
  recorded `SpectralSequence` definition. Pages are used only with `hr : 1 ≤ r`.
- E₁=H^(p+q)(X^[p,p+1])=H^(p+q)(grᵖK): `e₁ U p q` is the indicated isomorphism.
  Equality of abstract categorical objects is rendered as their natural isomorphism.
  The first-page/image-page compatibility equation ties `e₁` to the same canonical
  cohomology-image realization used on every other page.
- d₁ connecting map: the witnesses `i,j,hij,hS` form a short exact short complex
  with objects gr^(p+1)K, X^[p,p+2], grᵖK. The two projection equations fix i and j
  as the canonical inclusion and projection. The equation using `hS.δ (p+q)
  (p+1+q)` identifies the page differential with its connecting map under `e₁`.
  The spelling `p+1+1` in one projection avoids a non-definitional arithmetic cast;
  it is the same integer p+2.
- Zᵣ and Bᵣ inside grᵖK^(p+q): these are the imported `complexCycles p (p+q) r`
  and `complexBoundaries p (p+q) r`, whose full definitions were read. They use
  intersections/pullbacks, images, addition by F^(p+1), and the graded projection,
  with exactly the tails p+r and p-r+1 and degrees p+q+1 and p+q-1 in the node.
  The theorem's `hBZ` gives Bᵣ≤Zᵣ, and `eZ` identifies the page with
  `cokernel (Subobject.ofLE Bᵣ Zᵣ hBZ)`, the categorical quotient Zᵣ/Bᵣ.
- Equivalent natural image description: `φ U p r hr` has exactly the source
  X^[p,p+r] and target X^[p-r+1,p+1]. Its projection equation makes it the
  inclusion-induced map. `eI` identifies Eᵣ with `image (homologyMap φ (p+q))`.
  The witnesses `z,g` and their equations express the same representative as a
  graded cycle and as a cocycle of X^[p,p+r]. The last equation pins the composite
  of `eZ.inv` with `eI` to that representative's cohomology image. Thus the two
  descriptions compare via the natural quotient map, not an unrelated object iso.
- Induced image filtration on cohomology: `G n : DecreasingFiltration
  (U.obj.obj.homology n)` has step p exactly `imageSubobject (homologyMap
  (U.obj.filtration.step p).arrow n)`. It satisfies `IsFinite`, `IsSeparated`,
  and `IsExhaustive` (the latter is also part of the cited convergence convention).
- Infinite page and convergence: the existential `X : BigradedExactCouple C 0`
  is the standard reindexed couple. `eD P Q` fixes its D term as
  H^(P+Q)(F^(-Q)K); the alpha equation fixes its inclusion maps, and the initialG
  equation fixes its g as H of the graded projection. `eC s p q` identifies the
  standard derived page s+2 with filtered page s+1 at (P,Q)=(2p+q,-p), and its
  equation intertwines the differentials. `A n : X.AlphaColimit n` and `aH n`
  identify the colimit with Hⁿ(K); the iota equation fixes every colimit leg to
  the canonical Hⁿ(F^(P-n)K)→Hⁿ(K). Hence its image filtration has index P=p+n,
  precisely the shift explained in the node's proof. `X.ConvergesTo L A` uses
  the original dependency's full convergence predicate, including regularity,
  weak convergence through canonical maps, separated/exhaustive abutment, and
  the inverse-limit universal property. The final isomorphism identifies
  `X.pageInfinity L (2*p+q) (-p)` with `(G (p+q)).gradedPiece p`.
- Eventual stability: there are R≥1 with Zᵣ=Z_R, Bᵣ=B_R, both outgoing and incoming
  differentials zero at (p,q), and Eᵣ≅E_R for all r≥R. Vanishing of both
  differentials expresses actual stabilization via the next-page homology iso,
  rather than accidental isomorphism of objects.
- Functoriality: `S` is a functor on all bounded filtered complexes and their
  filtration-preserving maps. It sends these to morphisms of spectral sequences,
  which in Mathlib includes compatibility with the next-page homology isos.
  The naturality clause provides the restricted maps `s`, quotient maps `a,b`,
  and graded map `g`, fixed by projection equations, and requires naturality
  of both `e₁` and `eI`. The cohomology filtration is fixed as canonical images.
- Optional FᵖK=K for p≤0: `∀ p, p ≤ 0 → filtration.step p = ⊤`.
- Optional support Hⁱ(grᵖK)=0 outside [p,p+1]: `∀ p i,
  (i < p ∨ p+1 < i) → IsZero ((filtration.gradedPiece p).homology i)`.
- First-quadrant conclusion: `∀ p q r hr, (p < 0 ∨ q < 0) →
  IsZero (((S.obj U).page r hr).X (p,q))`.
- Stabilization for r>max(p,q)+1: the final clause has `max p q+1 < r`,
  both incident differentials zero, and Eᵣ≅E_t for all t≥r.

Dependencies used:

- `Sheaf.CategoryTheory.Filtration`: `CategoryTheory.DecreasingFiltration`,
  `FilteredObject`, the category and morphisms of filtered objects, `IsFinite`,
  `IsSeparated`, `IsExhaustive`, `gradedPiece`.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`:
  `CategoryTheory.SpectralSequence`, its morphisms and page homology isos,
  and `CategoryTheory.CohomologicalSpectralSequence`.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`:
  `CategoryTheory.BigradedExactCouple.ConvergesTo`, `LimitSubobjects`,
  `AlphaColimit`, `initialG`, `pageInfinity`.
- Landed node `def-sp-filtered-complex-subquotients`, module
  `Sheaf.Algebra.Homology.FilteredComplexSubquotients`: `complexQuotient`,
  `complexQuotientπ`, `complexCycles`, `complexBoundaries`,
  `complexCycleRepresentatives`. This existing node is added to `stmt_deps`.
- Landed node `def-sp-exact-couple`, module `Sheaf.CategoryTheory.ExactCouple`:
  `CategoryTheory.BigradedExactCouple`, `pageCouple`, `d`, `alpha`.
  This existing node is also added to `stmt_deps`, to record the explicit witness.
- Mathlib's `ShortComplex.ShortExact.δ` supplies the connecting map; its full
  signature and docstring were read in `Mathlib/Algebra/Homology/HomologySequence.lean`.
  `ObjectProperty.FullSubcategory` supplies the full category of the bounded objects.

Searches performed (also recorded by msearch in searches.jsonl):

1. LeanFinder: "bounded filtered cochain complex spectral sequence convergence first
   page cohomology graded pieces". Eight hits, ordinary cochain-complex and HomComplex
   homology declarations; none states the filtered-complex theorem.
2. Loogle: `CategoryTheory.CohomologicalSpectralSequence`. One exact hit for the
   spectral-sequence type, not the theorem.
3. msearch grep: `filteredComplex|FilteredComplex|filtered complex` in
   `Mathlib/Algebra/Homology`. Zero hits.
4. LeanSearch: the same natural-language query as (1). HTTP Internal Server Error;
   recorded as unavailable, not as a negative search result.
5. Direct rg in `WeilConjectures`: the node id and filtered-complex/spectral-object
   keywords. The spectral-object and Grothendieck-sequence APIs found there do not
   construct the full bounded filtered-complex sequence with these clauses.
6. Direct rg in `lean/Sheaf/CategoryTheory`: found the existing construction starting
   at page zero, FilteredPageTwoModel starting at page two, and subquotient definitions.
   The construction theorem lacks the first connecting map, convergence and
   functoriality, so it is not an exact match. The page-two model lacks page one,
   bounded convergence and the stated first-quadrant assertion. Their underlying
   notions are reused rather than redefined.
7. Direct rg of Mathlib, `WeilConjectures`, and `lean/Sheaf` for the full name
   `boundedFilteredComplex_spectralSequence`: no existing declaration.

Edge cases checked before the final statement:

- Zero complex and zero filtration: arbitrary equal finite bounds allowed; all
  pages, images and quotients vanish. No nonzero-object hypothesis occurs.
- Constant nonzero filtration is not bounded, and is correctly outside the domain.
  A filtration with its only jump at any integer is included, not only at zero.
- r=1: φ is the identity map on grᵖK up to integer indexing; its cohomology image
  is H(grᵖK). The representative equation reduces to the usual cycles/boundaries
  quotient. The e₁/eI compatibility handles this endpoint explicitly.
- r=2 with K⁰→K¹ the identity and F¹=(0,K¹), F²=0: E₂=0, as does the image in
  H(X^[p-1,p+1]); the target is not the former erroneous X^[p-1,p+2].
- Arbitrary negative p,q are admitted. The optional hypotheses imply grᵖ=0 for
  p<0 and E₁ support q=0 or 1 for p≥0, so first-quadrant vanishing is consistent.
  The bound r>max(p,q)+1 kills the outgoing target's negative q and the incoming
  source's negative p; r=1 itself is not prematurely assumed stationary.
- Infinite/unbounded cochain degree range is admitted: boundedness is only in the
  filtration direction. No finiteness or countable sums in C are imposed.
- The reindexing preserves total degree: P+Q=p+q and P-(p+q)=p.
  The differential vector (r,1-r) becomes (r+1,-r), matching standard page r+1.

No disputed statement or correction. No new definition nodes or dependency modules.
The server compiler accepted the final 215-line file in 4.1 seconds, without errors
or warnings (the theorem proof is the stage-2 `sorry`). The only scratch module is
outside lean/ and is not part of the delivery. The delivery dry run is the final check.

## Second reading by N1

I independently read the sandbox node and the entire 215-line module, then opened
all five statement dependency nodes and their recorded declarations. The original
blueprint source path is absent locally. I obtained Stacks `homology.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex into
`scratchpad/homology.tex` and read lines 5955--6175 and 6317--6415, alongside
https://stacks.math.columbia.edu/tag/012K. These contain the filtered-complex
hypotheses, both displayed formulas, the first connecting map, functoriality,
image filtration and finite-filtration convergence. No item statement correction
or new node/dependency module is present in this delivery.

My object/hypothesis/conclusion inventory and its Lean match:

1. Arbitrary abelian category A: `C : Type u`, `Category.{v} C`, `Abelian C`.
   Verdict: exact; independent object and morphism universes, no ring, field,
   injectives, products, or coproduct assumptions.
2. Integer cochain complex K with bounded decreasing subcomplex filtration F:
   `U.obj.obj : CochainComplex C ℤ`, `U.obj.filtration`, and `U.property` in
   the full subcategory selected by `filtration.IsFinite`. I read `IsFinite`:
   it is `∃ n m : ℤ, step n = ⊤ ∧ step m = ⊥`. Verdict: exactly boundedness
   as a filtered object of complexes under def-sp-filtration; arbitrary integer
   endpoints, no convention F⁰=K. Stacks 12.24.11 also covers degreewise finite
   filtrations; the node here specifies a bounded filtration by subcomplexes,
   using def-sp-filtration, whose notion is reused without a private variant.
3. X^[a,b] = FᵃK/FᵇK: `complexQuotient a b h`, for a≤b, is the cokernel
   of `Subobject.ofLE (step b) (step a)`. `complexQuotientπ` is its projection.
   Verdict: exact; `gradedPiece p` is the same cokernel for b=p+1.
4. Cohomological pages for every r≥1 and differential (r,1-r): codomain
   `CohomologicalSpectralSequence C 1`, with integer p,q,r and `hr : 1 ≤ r`.
   I read Mathlib Basic's page, iso, Hom.comm and cohomological abbreviation.
   Verdict: exact, including the homology-to-next-page identifications.
5. E₁ = H^(p+q)(grᵖK): `e₁ U p q`. Verdict: exact categorical isomorphism;
   the following eI/e₁ equation fixes compatibility with the canonical image
   description at r=1, rather than leaving unrelated identifications.
6. d₁ is the connecting morphism of the three quotient complexes: witnesses
   `i,j,hij,hS`, the two quotient projection equations, and the equation
   with `hS.δ (p+q) (p+1+q)`. Verdict: exact, with the correct degree n+1.
   Stacks temporarily assumes exact countable sums for its direct-sum argument
   and states its d₁ lemma under countable sums. Its construction lemma gives
   the general abelian case by bigraded objects. Here the node's own exact-couple
   proof and this finite short exact sequence supply the general d₁ clause:
   countable sums are unnecessary and are not added to the node's hypotheses.
7. Zᵣ,Bᵣ inside grᵖK^(p+q): `complexCycles` and `complexBoundaries`.
   I read their definitions: pullback/intersection in Kⁿ, inverse image under d
   of F^(p+r)K^(n+1), respectively image of d on F^(p-r+1)K^(n-1), join with
   F^(p+1), restriction to Fᵖ, and image under the graded projection.
   `hBZ` and `eZ` give Bᵣ≤Zᵣ and Eᵣ≅cokernel(Bᵣ→Zᵣ). Verdict: exact.
8. Equivalent natural cohomology-image description: `φ U p r hr` has source
   X^[p,p+r] and target X^[p-r+1,p+1]. Its projection equation fixes the
   inclusion-induced morphism. `eI` gives its homology image. The `z,g`
   projection equations and the equation through `eZ.inv` identify the same
   cycle representative with its cohomology image. Verdict: exact, including
   the target endpoint p+1 and canonical comparison.
9. Induced finite separated filtration on Hⁿ(K): `G n`, the equation setting
   each step to `imageSubobject (homologyMap (step p).arrow n)`, and
   `IsFinite ∧ IsSeparated ∧ IsExhaustive`. Verdict: exact image filtration;
   exhaustiveness follows from the finite lower endpoint and is also required
   by the cited convergence convention.
10. E∞≅grᵖH^(p+q)(K), and convergence: witnesses `X,L,A,aH,eD,eC`,
    `X.ConvergesTo L A`, and the final `pageInfinity` comparison. I read
    `LimitSubobjects`, `AlphaColimit`, `WeaklyConvergesTo`, `AbutsTo`,
    `IsInverseLimit`, and `ConvergesTo`. The alpha and initialG equations fix
    the inclusions and graded projections; the eC equation fixes every page
    differential. With (P,Q)=(2p+q,-p), total degree P+Q=p+q, filtration
    index P-(p+q)=p, and standard page s+2 is filtered page s+1. The aH/iota
    equation fixes the colimit to H(K). Verdict: exact convergence in the
    recorded dependency's sense, not mere abstract graded-object isomorphisms.
11. Eventual stabilization: integer R≥1 for each p,q, then all r≥R have the
    same Z and B, zero incoming/outgoing differentials, and Eᵣ≅E_R.
    Verdict: correct bounded-filtration stabilization; page homology isos
    identify successive stable terms when both differentials vanish.
12. Functoriality: `S` is a single functor on all bounded filtered complexes.
    For every filtered morphism t, witnesses `s,a,b,g` have projection
    equations fixing the restrictions and quotient maps, and the e₁/eI
    naturality equations identify its page maps. Verdict: exact; Mathlib's
    spectral-sequence morphisms also preserve successive homology isos.
13. Optional FᵖK=K for p≤0: the first premise of the last implication is
    `∀ p, p ≤ 0 → step p = ⊤`. Verdict: exact, not imposed globally.
14. Optional Hⁱ(grᵖK)=0 outside [p,p+1]: the second premise uses
    `(i < p ∨ p+1 < i) → IsZero ((gradedPiece p).homology i)`.
    Verdict: exact inclusive endpoints in every integer degree.
15. First-quadrant conclusion: `p < 0 ∨ q < 0` implies the page object is
    `IsZero` for all r≥1. Verdict: exact; genuine categorical zero objects.
16. Bound r>max(p,q)+1: final strict inequality, zero outgoing and incoming
    maps, and Eᵣ≅E_t for every t≥r. Verdict: exact stabilization; outgoing
    target has negative q and incoming source has negative p under this bound.

Edge cases independently checked: zero complex and filtration permit equal
bounds; nonzero constant filtrations correctly fail boundedness. A single jump
at any negative or positive index is admitted. r=1 gives the identity comparison
on grᵖ and its homology image. At r=2, K⁰→K¹=id and F¹=(0,K¹), F²=0
have E₂=0, consistent with target X^[p-1,p+1]. All negative p,q and n=0
are included. No cochain-degree bound is imposed. For p=q=0 the strict
stabilization bound is r>1, so d₁ is not prematurely forced to vanish.
There is no index set of variable cardinality, scheme, or characteristic
assumption; the relevant index sets are the nonempty integers and natural
numbers. Universes u,v are declared and no object variable is auto-implicit.

Independent H4 searches (recorded by msearch in searches.jsonl): LeanFinder
`finite filtration cohomology spectral sequence abutment naturality` returned
eight ordinary homology/naturality results and no matching theorem. Loogle
`CategoryTheory.CohomologicalSpectralSequence` returned the existing type,
which this statement uses. LeanSearch `spectral sequence associated to finite
filtered complex` returned Internal Server Error; recorded as unavailable.
Direct rg with `filtered.*[Ss]pectral|[Ss]pectral.*filtered|[Aa]but|[Ff]iltered[Cc]omplex`
and `spectralObject|SpectralObject|filteredComplex|FilteredComplex|imageFiltration`
in Mathlib homology, WeilConjectures and lean/Sheaf found the landed
`filteredComplex_associated_spectralSequence` and `FilteredPageTwoModel`.
I opened both complete signatures: the former lacks connecting-map,
functoriality and convergence clauses; the latter starts at page two and has
no bounded convergence assertion. I also opened upstream SpectralObject
SpectralSequence's signatures: its input is an EInt-indexed spectral object
with first-quadrant assumptions, not a bounded filtered complex. None is an
exact existing realization of this node. No definitions are introduced here.

No mathematical mismatch requiring a Lean repair was found. I retained the
statement and docstring. The six proof steps and their cited nodes are all
present in the docstring; the sole theorem proof is `sorry`, with no hollow
definitions, local notation, private copies, or new instances. The node's
`lean.statement` was checked byte-for-byte against the signature before `:=`.
The two extra statement dependencies are already-landed definitions and have
been inspected, not new nodes of this delivery. Independent server compilation
with scompile passed in 3.6 seconds, exit 0, with no warnings or errors.
