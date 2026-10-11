## Worker report

The delivery states `CategoryTheory.DecreasingFiltration.filteredComplex_ZB_description`
in `Sheaf.Algebra.Homology.FilteredComplexZBDescription`. Its proof is `sorry`; no theorem
is proved. The supporting module defines the quotient-complex and subobject notation in
full, with no postponed data or well-definedness proofs.

The item statement is unchanged. Its `stmt_deps` gains the new definition node
`def-sp-filtered-complex-subquotients`, which makes the notation needed in the statement
available to other nodes too.

Hypothesis and clause correspondence:

- An arbitrary abelian category is `{C : Type uZ} [Category.{vZ} C] [Abelian C]`.
  Both object and morphism universes are explicitly bound; no concreteness, enough
  injectives, direct sums, or restriction to modules is assumed.
- The cochain complex is `(K : CochainComplex C ℤ)`, including unbounded complexes.
- The decreasing filtration by subcomplexes is `(F : DecreasingFiltration K)`.
  Mathlib makes the category of cochain complexes abelian. Thus `F.step p` is a subobject
  in that category, its chosen underlying object is a cochain subcomplex, and
  `F.antitone_step` expresses all decreasing inclusions. This is the equivalent
  formulation explicitly mentioned in Stacks Definition 12.24.1.
- The finite filtration assumption is `hfinite`: for each degree `n` there are integers
  `a,b` such that `F.complexStep a n = ⊤` and `F.complexStep b n = ⊥`.
  This is exactly the degreewise finiteness used by the item's last proof step and by
  Stacks Lemma 12.24.11. It does not impose a uniform bound over all degrees.
- All integers `p,q,r` with `r ≥ 1` occur in the third conjunct as
  `∀ (p q r : ℤ) (hr : 1 ≤ r)`, with total degree `n := p + q`.
- The stated cycle numerator is the meet of `complexStep p n` with the pullback of
  `complexStep (p+r) (n+1)` along `K.d n (n+1)`. In `complexCycles`, its join with
  `complexStep (p+1) n` is pulled back into the selected object `(F.step p).X n`,
  then mapped by `Subobject.«exists»` along the graded quotient projection.
  Since `Fᵖ⁺¹ ≤ Fᵖ`, this is precisely the displayed quotient by `Fᵖ⁺¹`, as a
  subobject of `(F.gradedPiece p).X n`.
- `complexBoundaries` performs the same operations on the meet with the image under
  `K.d (n-1) n` of `complexStep (p-r+1) (n-1)`; the signs and shifts match the node.
- `∃ hBZ : B ≤ Z` states the inclusion. Its proof also supplies the canonical
  subobject inclusion `Subobject.ofLE B Z hBZ`, whose cokernel is `Z/B`.
- `E : CohomologicalSpectralSequence C 0` is a spectral sequence with the usual
  bigraded shapes, including the initial page and differentials of bidegree `(r,1-r)`.
  The third conjunct identifies every page `r ≥ 1` at `(p,q)` with the displayed
  `Z/B` by `Nonempty (... ≅ cokernel (Subobject.ofLE B Z hBZ))`.
- The quotient-complex description uses `S = Fᵖ/Fᵖ⁺ʳ` and
  `T = Fᵖ⁻ʳ⁺¹/Fᵖ⁺¹`. `ha` and `hb` are witnesses of the integer inequalities
  already implied by `hr`; they are not additional assumptions. `hs` and `ht`
  supply the inclusion proofs needed by the quotient definitions.
- `φ : S ⟶ T` is specified by the equation
  `π_source ≫ φ = inclusion ≫ π_target`. The inclusion is exactly
  `Fᵖ → Fᵖ⁻ʳ⁺¹`. Since `π_source` is an epimorphism, this equation specifies
  the induced map uniquely, rather than admitting an arbitrary map.
- `Hφ := HomologicalComplex.homologyMap φ n` is the requested map on cohomology.
  `∃ e : cokernel (Subobject.ofLE B Z hBZ) ≅ image Hφ` identifies its image with
  the page quotient. The comparison is specified on cycle representatives by the
  final commuting equation involving `z`, `g`, `e.hom`, and `image.ι Hφ`.
  The equation for `z` specifies the image of a representative in the graded cycles;
  the equation for `g` specifies its cocycle class in `S`. Both are uniquely
  determined by their monomorphism inclusions. Consequently `e` is the comparison
  induced by the representative, rather than just existence of an unrelated
  isomorphism. The representative map onto `Z/B` is epi, so this characterization
  is unique and is preserved by filtration-preserving maps (the natural comparison).
- The first conjunct explicitly asserts that `Z₁` is the kernel subobject and `B₁`
  the image subobject of the differential in `F.gradedPiece p`. The second conjunct
  explicitly identifies `E₁` with `(F.gradedPiece p).homology (p+q)`.
- The final conjunct asserts, for each fixed `p,q`, an integer `R ≥ 1` such that
  every `r ≥ R` has equal cycle and boundary subobjects to those at `R`, as well
  as isomorphic page objects. No uniform bound over all bidegrees is required.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; its complete class signature and explanatory
  docstring were read, including the finite products, kernels, cokernels and normal
  mono/epi fields.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration`,
  `Sheaf.CategoryTheory.Filtration`; the complete module was read, including
  `step`, `antitone_step`, `IsFinite` and `gradedPiece`. The filtration is used
  on the abelian category of cochain complexes, not redefined privately.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence`,
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`; the structure, pages, homology
  isomorphisms and `CohomologicalSpectralSequence` abbreviation were read.
- Supporting Mathlib API: `HomologicalComplex` and `CochainComplex`,
  the abelian instance from `Mathlib.Algebra.Homology.HomologicalComplexAbelian`,
  `kernelSubobject`, `imageSubobject`, `Subobject.pullback`, `Subobject.«exists»`,
  `Subobject.ofLE`, `cokernel`, `cokernel.π`, `image`, `image.ι`,
  `HomologicalComplex.homologyMap`, `iCycles`, and `homologyπ`.

Edge cases checked before writing:

- The zero complex and the empty abelian category of zero objects yield zero cycle,
  boundary and image objects throughout; no nonzero assumption occurs.
- `r=1` has identical source and target quotient complexes `Fᵖ/Fᵖ⁺¹`; its induced
  map is the identity, so its cohomology image is precisely graded cohomology.
- A complex concentrated in degree zero with `F⁰=F¹=A`, `F²=0` has zero page in
  filtration degree zero and `A` in degree one; the image formula agrees in both cases.
- For the identity complex `A → A`, with the upper filtration step only in degree one,
  `E₁^{0,0}=A` and later terms vanish; the formula is not asserting constant pages
  starting at one.
- Negative `p,q` and arbitrary integer total degree are allowed. The boundary tail
  is `p-r+1`, not `p-r`; the differential uses degree `n-1` to `n`.
- For an unbounded complex with degree-dependent finite bounds, the two tails in
  degrees `n+1` and `n-1` stabilize at a bound depending on `p,n`; the final
  quantifiers permit exactly that. No characteristic or ring assumptions occur.

Searches (all remote Mathlib searches were run with `msearch.py`, and their exact
query/digest records are in the sandbox's `searches.jsonl`):

- LeanSearch: `filtered cochain complex spectral sequence cycles boundaries quotient
  cohomology image`: service unavailable (Internal Server Error).
- LeanFinder: `filtered complex spectral sequence cycles boundaries Z_r B_r`:
  eight ordinary homological-complex cycle lemmas, led by `HomologicalComplex.toCycles_i`;
  no exact filtered-complex theorem.
- Loogle: `CategoryTheory.SpectralSequence`: the spectral-sequence structure and its
  API, not a filtered-complex cycle-boundary theorem.
- Mathlib grep: `filtered|filtration` in `Algebra/Homology`: seven hits, principally
  spectral objects attached to a filtered-complex functor and unrelated filtered
  colimits. No exact theorem or explicit subquotient definitions.
- Searches for the supporting new notion are detailed in the next section.
- `rg` for filtered complexes, filtration and the item id in the source project's
  `WeilConjectures/CategoryTheory` and the project's `lean/Sheaf/CategoryTheory`
  found the existing object-filtration API and the double-complex-specific filtration
  module, but no general quotient-complex or filtered-complex Z/B statement.
- `rg` for `filteredComplex|FilteredComplex|cycleNumerator|boundaryNumerator` and
  the item id in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no declaration to reuse. Separate DAG/source/project searches for
  `complexCycles|complexQuotient|def-sp-filtered-complex-subquotients` found no match.
- `tools/blueprint_refs.py search 'filtered complex'` returned
  `thm-sp-double-complex-spectral-sequences` and `thm-sp-spectral-object-yields`;
  neither carries the missing general quotient/cycle notation as Lean declarations.

Source verification: the local clone contains only literature indexes, not the cited
`homology.tex`. I opened https://stacks.math.columbia.edu/tag/012K and checked the formulas,
Definition 12.24.1, Lemma 12.24.2, and the degreewise finiteness discussion in Lemma
12.24.11. The current online section is 12.24; the node's historical label says 12.19.2.
The formulas and mathematical content agree; no statement correction is needed.
No statement dispute or unusable dependency was found.

Validation: the two modules compiled together on the server with exit code zero and no
warnings, in dependency order. Explicit universes are differently named between the two
modules so the prescribed combined-file compiler can read both in one temporary file.

## New nodes

`def-sp-filtered-complex-subquotients` defines the degreewise filtration steps,
quotient complexes with projections, unquotiented cycle representatives, and cycle and
boundary subobjects of the graded complex. Its module is
`Sheaf.Algebra.Homology.FilteredComplexSubquotients`; all six definitions use existing
Mathlib categorical operations and the dependency's `DecreasingFiltration`.
Its primary declaration is `CategoryTheory.DecreasingFiltration.complexCycles`, with
all six declarations listed in its Lean record. Its source is Stacks Tag 012K,
Definition 12.24.1 and the formulas before Lemma 12.24.2. The item's total-degree
notation substitutes `n = p+q` in these general formulas.

This node packages missing notation, not a second implementation of the object
filtration or spectral-sequence notions. The source's general spectral-object
construction and Mathlib's general kernel/image lemmas do not define these specific
filtered-complex subquotients. The DAG and Lean source searches above found no node
with a usable declaration for them. The dedicated remote queries were:

- LeanSearch: `quotients of subcomplex filtrations and cycle boundary subobjects of the
  graded complex`: unavailable, Internal Server Error, recorded as unavailable.
- LeanFinder, the same query: eight homological-complex cycle or truncation results,
  including `HomologicalComplex.i_cyclesMk`, `toCycles_i`, `truncGE'.X`, `cyclesMk`,
  and `image_to_eq_image`; none defines the filtered-complex subquotients.
- Mathlib grep: `filteredComplex|FilteredComplex|cycleNumerator|boundaryNumerator`:
  zero hits. The same checks in the source project and `lean/Sheaf` had no match;
  the object-filtration API is reused rather than duplicated.

`tools/blueprint_refs.py ancestor` gives `thm-sp-spectral-object-yields`; the new node's
blueprint origin records that ancestor and Step 3, with the item itself prefixed to
`via`. The node is a definition, with empty proof and proof dependencies and no
hollow definition. Its dependencies are precisely `def-sp-abelian` and
`def-sp-filtration`, which its self-contained statement cites.

## Second reading by E1

I independently compared the node statement, Stacks Tag 012K (Definition 12.24.1,
Lemma 12.24.2 and Lemma 12.24.11), and both delivered modules.

- The ambient object is rendered by `{C : Type uZ} [Category.{vZ} C] [Abelian C]`;
  this is exactly an arbitrary abelian category, with both universes explicit. Verdict:
  matches, with no concreteness, countable-sum, characteristic, or ring assumption.
- The complex is `(K : CochainComplex C ℤ)`, so it is an arbitrary integer-indexed
  cochain complex. Verdict: matches the source, including unbounded and zero complexes.
- The filtered complex is `(F : DecreasingFiltration K)`; `step` and
  `antitone_step` are supplied by the dependency declaration, so this is a decreasing
  filtration by subcomplexes. Verdict: matches; no private filtration notion is used.
- Finiteness is rendered by `hfinite : ∀ n : ℤ, ∃ a b : ℤ,
  F.complexStep a n = ⊤ ∧ F.complexStep b n = ⊥`. This is precisely the source's
  assumption that the filtration on each `Kⁿ` is finite (Lemma 12.24.11), and does
  not add a uniform bound. Verdict: matches.
- The first conclusion clause is the pair of equalities, for every `p,n`, identifying
  `complexCycles p n 1` with the graded differential kernel and `complexBoundaries p n 1`
  with its image. Verdict: matches the `r=1` cycle/boundary clause.
- The second clause is `∀ p q, Nonempty ((E.page 1).X (p,q) ≅
  (F.gradedPiece p).homology (p+q))`. Verdict: matches `E₁^{p,q}=H^{p+q}(grᵖK)`.
- The third clause quantifies all integers `p,q,r` with `1 ≤ r`, sets `n=p+q`, and
  defines `Z` and `B` using `complexCycles` and `complexBoundaries`. It asserts
  `∃ hBZ : B ≤ Z`, then identifies page `r` with
  `cokernel (Subobject.ofLE B Z hBZ)`. Verdict: matches `B_r ⊆ Z_r` and
  `E_r^{p,q} ≅ Z_r^{p,q}/B_r^{p,q}` with the same quantifier order.
- The same clause introduces `ha` and `hb`, quotient complexes `S=Fᵖ/Fᵖ⁺ʳ` and
  `T=Fᵖ⁻ʳ⁺¹/Fᵖ⁺¹`, and a morphism `φ` satisfying the projection/inclusion
  commutative equation. Verdict: matches the source's natural quotient-complex map;
  `ha` and `hb` are witnesses of inequalities forced by `r≥1`, not extra hypotheses.
- It defines `R`, `Hφ`, representative maps `z,g`, and the two equations placing
  representatives in `Z` and `S.cycles`; it then gives an isomorphism from the page
  quotient to `image Hφ` with the final representative compatibility equation.
  Verdict: this is a precise categorical rendering of the source's natural image
  description and does not weaken it to an unrelated existence statement.
- The final clause is `∀ p q, ∃ R ≥ 1` such that all `r ≥ R` have equal cycle and
  boundary subobjects and isomorphic page objects. Verdict: matches degreewise finite
  stabilization, with no uniform bound over `(p,q)`.

The supporting definition node was also checked: `complexStep`, `complexQuotient`,
`complexQuotientπ`, `complexCycleRepresentatives`, `complexCycles`, and
`complexBoundaries` use the recorded `DecreasingFiltration` and Mathlib categorical
subobject, image, pullback, cokernel, and homology operations. Their source formulas
have the correct tails `p+r` and `p-r+1`, total-degree shifts `n+1` and `n-1`, and
quotient by `F^{p+1}`. No hollow definition or unbound variable was found.

Edge cases checked: `r=1`; `n=0`; negative `p,q`; zero and degree-zero complexes;
zero subobjects; and degree-dependent finite bounds. All are admitted by the explicit
integer quantifiers and degreewise `hfinite`. No characteristic or universe case is
excluded.

Searches were rechecked with `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`, plus
LeanFinder/Loogle/LeanSearch records in `searches.jsonl`; no existing filtered-complex
Z/B declaration was found. The only related hits were ordinary homological-complex
cycle APIs. No mismatch was found, so no source, node, or Lean statement was changed.

## Reviewer fix (R-fzb1318, stage 2)

The finiteness hypothesis `hfinite` (degreewise finiteness of `complexStep`) was replaced by
`(hF : F.IsFinite)`: the node says "a finite decreasing filtration by subcomplexes
[def-sp-filtration]", i.e. finiteness of `F` as a filtration of `K` in the abelian category of
cochain complexes, which the dependency records as `DecreasingFiltration.IsFinite`. The delivered
degreewise hypothesis was strictly weaker than the node's (a strengthened theorem, Stacks 12.24.11's
setting rather than the node's) and restated a notion that has a recorded declaration. The worker
and second-reading bullets above describing `hfinite` refer to the delivered form.
