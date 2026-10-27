## Worker report

The module `Sheaf.Algebra.Homology.SpectralPageZeroPropagation` states
`CategoryTheory.SpectralSequence.spectral_page_zero_propagation`, with one
`sorry` proof. No definition, new node, dependency repair, or statement correction
is needed. Only the item's `lean` record changes.

Hypothesis and clause correspondence:

- The arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  Object and morphism universes are explicitly independent.
- The sequence is `(E : E₂CohomologicalSpectralSequence C)`. This is Mathlib's
  abbreviation for `SpectralSequence C (fun r ↦ ComplexShape.up' (r, 1-r)) 2`,
  so the index type is `ℤ × ℤ`, the page number is an integer starting at two,
  and the differential has exactly bidegree `(r,1-r)`. `E.page` is a complex,
  and `E.iso` supplies the specified homology-to-next-page isomorphisms.
- The first conjunct quantifies `s : ℤ`, `hs : 2 ≤ s`, `p q r : ℤ`, and
  `hsr : s ≤ r`. Its implication from `IsZero ((E.page s hs).X (p,q))` to
  `IsZero ((E.page r (le_trans hs hsr)).X (p,q))` is the general propagation
  assertion, including arbitrary starting page s, not merely s = 2.
- The antecedents of the second conjunct are exactly the two page-two
  assumptions: `∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ...`, and
  `∀ p q : ℤ, 0 < q → IsZero ...`. They are used only for the consequences;
  they are not hypotheses of the general propagation clause.
- The first consequence quantifies every integer `r ≥ 2` and bidegree, with
  `p < 0 ∨ q ≠ 0 → IsZero ((E.page r hr).X (p,q))`.
- The final consequence quantifies p, positive q, and an object `Z : C`.
  Its premise `∃ (R : ℤ) (hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
  Nonempty ((E.page r (le_trans hR hr)).X (p,q) ≅ Z)` expresses that Z is
  the eventual stationary value. The conclusion is `IsZero Z`. This covers
  every stationary value, with no chosen infinity-page construction or
  convergence/abutment hypothesis. The object is zero already by taking
  r = R in its supplied isomorphisms; no compatibility choice is necessary
  for this vanishing assertion. It does not assert that other rows converge.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its class supplies preadditivity,
  finite products, kernels, cokernels, normal monos, and normal epis.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence`,
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`; concretely its existing
  `CategoryTheory.E₂CohomologicalSpectralSequence` abbreviation is used.
  The full structure, `page`, `iso`, and abbreviation were read.
- Proof dependency `lem-weil-pbc-short-complex-zero-homology` is an existing
  Mathlib leaf, whose relevant clause is
  `CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂` in
  `Mathlib.Algebra.Homology.ShortComplex.Homology`. Its module is imported
  privately as the proof plan. The leaf's other clauses are
  `ShortComplex.isIso_iCycles` in `ShortComplex.LeftHomology` and
  `ShortComplex.isIso_homologyπ` in `ShortComplex.Homology`; their signatures
  were also checked. They are not additional assumptions.

Sources checked directly: `literature/stacks-project/homology.tex`,
`definition-spectral-sequence` (Tag 011N), including its paragraph allowing
specified isomorphisms and arbitrary starting pages; `lemma-relate-boundedness`
(Tag 0BDV), whose proof hint is exactly persistence of zero entries; and the
current `literature/blueprint/latest/blueprint/sec-proper-base-change/`
`sk-lem-pbc-composition-cancellation/lemma-weil-pbc-cancellation.proof.md`,
part (1), at the sentence about collapse to row q = 0. The docstring expands
the node's three proof steps and names the short-complex input.

Edge cases checked before writing: r = s gives the original zero-object
hypothesis; r = s + 1 is page homology of a short complex with zero middle
object; s = 2 is included but s > 2 is not excluded; negative p and negative q
are genuine indices; q = 0 with p ≥ 0 has no vanishing conclusion; p < 0,
q = 0 is covered; q > 0 is covered for every p; the zero category is allowed.
The stationary threshold R may be two or any larger integer. No boundedness,
Noetherian, module-category, nonempty index, or abutment condition is imposed.

Searches for an existing exact statement (all performed 2026-10-23):

- `msearch.py ... leanfinder` with query "A zero entry of a cohomological
  spectral sequence remains zero on every later page starting at any page s":
  eight hits, on bifunctor/total-complex differentials, `dNext_eq_zero`, and
  `CochainComplex.isZero_of_isStrictlyLE`; no page-propagation theorem.
- `msearch.py ... loogle` with query
  `CategoryTheory.SpectralSequence, CategoryTheory.Limits.IsZero`: zero hits.
- `msearch.py ... grep 'isZero|vanish|support'
  Algebra/Homology/SpectralSequence`: zero hits.
- `msearch.py ... leansearch` with query "A zero entry of a spectral sequence
  stays zero on every later page": eight hits, on zero short-complex homology
  maps, augmented-complex differentials, zero-preserving evaluation, and an
  unrelated spectral-radius lemma; no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` with patterns
  `isZero_page|page.*[Zz]ero|spectral.*[Zz]ero|SpectralSequence` and
  `isZero_page_of|isZero.*page|page.*isZero|zero_propagation|zeroPropagation`:
  read `WeilConjectures/CategoryTheory/SpectralSequence/Vanishing.lean`,
  where `isZero_page_of_isZero_page_two` is limited to `ℕ × ℕ` and page two;
  also read `SpectralSequenceNatRowZero.lean` and
  `Algebra/Homology/ExactCouple/EdgeCollapse.lean`, whose propagation result
  concerns an exact couple's iterated derived terms rather than an arbitrary
  supplied spectral sequence. None states this item.
- Searched `dag/lean_names_upstream.json`, Mathlib, upstream, and Sheaf for
  `spectral_page_zero_propagation|page_zero_propagation`: no name collision.
  Searched upstream for the node id: no existing declaration.

Validation: the prescribed `scompile.py` compiled the exact delivered file in
both sandbox mode and its final module name against the live server build,
with no errors or warnings (1.2 s and 1.0 s respectively).

## Second reading by NI

Re-read the node and completed file together after compilation. The abelian
category and independent universes are explicit. Unfolding the Mathlib
abbreviation yields integer bidegrees, start page two, and the required
cohomological differential shape. The first conjunct has all s ≥ 2 and r ≥ s;
the support assumptions occur only in the implication giving the final two
clauses. The support conclusion uses `p < 0 ∨ q ≠ 0`, not just positive rows.
The last clause explicitly includes every eventual stationary positive-row
value via isomorphisms from all sufficiently late entries. All threshold
proofs are explicit, and no `let`, local notation, private notion, or
implicit universe binding appears. No mismatch found; no correction made.
This is the worker's second pass; the maintainer's independent review remains
part of the delivery process, and no additional agent was started.
