## Worker report

The module `lean/Sheaf/CategoryTheory/LerayFiveTerm.lean` defines
`CategoryTheory.BigradedExactCouple.IsFirstQuadrant` and states
`CategoryTheory.BigradedExactCouple.lerayFiveTerm` with a `sorry` proof.
`IsFirstQuadrant` renders the first-quadrant hypothesis clause by clause: for every
page index `r : ℕ`, bidegrees `p q : ℤ`, and disjunction `p < 0 ∨ q < 0`, the page
term `X.page r p q` is zero.  The theorem binds the convergent exact couple `X`,
its limiting subobjects `L`, and diagonal colimits `A`; `hconverges` is exactly
`X.ConvergesTo L A` from the convergence dependency.  It existentially supplies
three edge arrows with domains/codomains
`E₂^{1,0} → A¹`, `A¹ → E₂^{0,1}`, and `E₂^{2,0} → A²`.  The middle arrow is
literally `X.pageDifferential 2 0 1`, hence the `d₂` transgression.  The resulting
`ComposableArrows.mk₄` has the five terms
`E₂^{1,0}, A¹, E₂^{0,1}, E₂^{2,0}, A²`; `.Exact` expresses exactness at all
interior terms and the complex equations.  The edge arrows are the canonical
bottom/left maps induced by the finite filtration and convergence comparison; their
canonical construction is the content proved at stage 3.

Dependencies used:

- `def-sp-abelian`: Mathlib `CategoryTheory.Abelian` supplies `[Abelian C]`.
- `def-sp-convergence`: `Sheaf.CategoryTheory.ExactCoupleConvergence`, declarations
  `CategoryTheory.BigradedExactCouple.LimitSubobjects`, `AlphaColimit`, and
  `ConvergesTo`.
- `def-sp-filtration`: `Sheaf.CategoryTheory.Filtration`, used through the
  convergence declaration and its filtration objects.
- Mathlib `CategoryTheory.ComposableArrows.mk₄` and
  `CategoryTheory.ComposableArrows.Exact` express the displayed five-term exact
  sequence.

Edge cases checked: negative bidegrees are explicitly required to be zero; the
indices in the displayed terms are nonnegative; `pageDifferential 2 0 1` has target
`page 2 2 0`; no nonzero-page or finite-filtration assumptions are omitted because
`hconverges` supplies them.  The use of integer bidegrees avoids excluding any
integer-indexed spectral sequence, while page indices are natural as in the recorded
exact-couple API.

Searches made: `rg` over `lean/Sheaf` and the slopmaster2 `WeilConjectures` source
for `five.?term`, `Leray`, and `ComposableArrows`; no project/source declaration of
this theorem was found.  `msearch.py` LeanFinder query “five term exact sequence
spectral sequence” found only homology-sequence exactness lemmas.  Loogle query
`ComposableArrows, Exact, spectral sequence` found no matching theorem.  Grep of
Mathlib spectral-sequence and CategoryTheory files found page/differential APIs but
no convergence five-term theorem.  Thus a new statement module was required.

## Earlier second reading (a previous round; superseded)

The statement was checked against the source clause by clause.  The first-quadrant
condition is explicit, convergence is the recorded regular/abutting/complete
condition, and the five terms have the required total degrees 1 and 2.  The exact
sequence API records all four arrows and exactness at each internal object; the
middle arrow is exactly the `d₂` differential.  No statement correction or new
node is needed.

## Second reading by C1

I read the node statement clause by clause against
`lean/Sheaf/CategoryTheory/LerayFiveTerm.lean` and the dependency declarations.
The ambient object is rendered by `C : Type u`, `[Category.{v} C]`, and
`[Abelian C]`; the spectral sequence is the type-zero
`X : BigradedExactCouple C 0`; its pages are `X.page r p q`, and the
bidegree differential is `X.pageDifferential`.  The first-quadrant hypothesis is
`hquadrant : X.IsFirstQuadrant`, which quantifies over every natural page and
integer bidegree and requires `IsZero` whenever either index is negative.  The
convergent abutment and filtration data are rendered by
`L : LimitSubobjects X`, `A : ∀ n : ℤ, AlphaColimit X n`, and
`hconverges : X.ConvergesTo L A`.  The five displayed objects are respectively
`X.page 2 1 0`, `(A 1).obj`, `X.page 2 0 1`, `X.page 2 2 0`, and `(A 2).obj`.
The arrows are existentially bound as `edge₁`, `edge₂`, and `edge₄`, with the
middle arrow exactly `X.pageDifferential 2 0 1`; the sequence is expressed by
`ComposableArrows.mk₅ (0 : (0 : C) ⟶ X.page 2 1 0) edge₁ edge₂
(X.pageDifferential 2 0 1) edge₄` and `.Exact`.  This includes the initial zero
arrow, exactness at all four interior objects, and the complex equations; the
final object has no outgoing arrow as in the node.

The first worker used `mk₄`, whose `Exact` omits exactness at the first object,
so it did not express injectivity of `E₂^{1,0} → H¹` required by the leading
`0` in the node.  I changed the conclusion to `mk₅` with the zero-object arrow;
this is the only mismatch found.  The source is Stacks Homology Lemma 0132,
whose first-quadrant and finite-filtration conventions agree with the recorded
convergence API.  Empty/zero categories are covered by the zero-object arrow;
negative bidegrees are handled explicitly by `IsFirstQuadrant`; page indices are
natural, bidegrees and total degrees are integers, and no characteristic or
universe case is excluded.

I searched the project and source with `rg` for `five.?term`, `Leray`, and
`ComposableArrows`; no duplicate declaration exists.  LeanFinder was queried
for “five term exact sequence spectral sequence”, Loogle for
`ComposableArrows, Exact, spectral sequence`, and Mathlib spectral-sequence and
category-theory files were grepped; these found only general homology-sequence
APIs and no convergence five-term theorem.  The dependency declarations used
are `CategoryTheory.BigradedExactCouple.LimitSubobjects`, `AlphaColimit`, and
`ConvergesTo` from `Sheaf.CategoryTheory.ExactCoupleConvergence`, together with
Mathlib `CategoryTheory.Abelian` and `ComposableArrows.mk₅`/`Exact`.

## Reviewer fix (R-lft1152)

The delivered conclusion bound the three edge arrows existentially (`∃ edge₁ edge₂ edge₄`),
which weakens the node: it asserts exactness for *some* maps, not for the canonical
bottom edge, left edge (via the stable-term inclusion) and degree-2 bottom edge the node
names, and downstream users cannot identify the maps. The fixed module constructs them:
`bottomEdge` (E₂^{p,0} → E_∞^{p,0} ≅ grᵖHᵖ = FᵖHᵖ ⊆ Hᵖ) and `leftEdge`
(H^q = F⁰H^q → gr⁰H^q ≅ E_∞^{0,q} ⊆ E₂^{0,q}), through `infinityGradedIso` (the unique
comparison of `weakConvergence_comparison`), with the first-quadrant vanishing facts as
sorry'd lemmas (`limitCycles_bottom_eq_top`, `limitBoundaries_left_comp_eq_zero`,
`imageFiltration_ofLE_eq_zero`, `imageFiltration_zero_eq_top`); `lerayFiveTerm` now states
exactness of `mk₅ 0 (bottomEdge 1) (leftEdge 1) (pageDifferential 2 0 1) (bottomEdge 2)`.
