## Worker report

The module `Sheaf.CategoryTheory.EdgeCollapse` states
`CategoryTheory.BigradedExactCouple.edge_collapse`.  It uses the recorded
`CategoryTheory.BigradedExactCouple` from `Sheaf.CategoryTheory.ExactCouple`,
`BigradedExactCouple.ConvergesTo`, `LimitSubobjects`, `AlphaColimit`,
`imageFiltration`, and `pageInfinity` from
`Sheaf.CategoryTheory.ExactCoupleConvergence`, and `DecreasingFiltration.IsFinite`
from `Sheaf.CategoryTheory.Filtration`.

The exact-couple hypothesis is `X`; convergence to the filtered abutments is
`hconv`; finiteness of each abutment filtration is `hfinite` (exhaustiveness and
separatedness are included by `X.ConvergesTo`).  The page bound is `r₀ ≥ 2`, and
`hvanish` renders the hypothesis that every page-`r₀` term with first index
nonzero is zero.  The first conclusion says every differential on every page
`r ≥ r₀` is zero.  The second gives the stationary-page isomorphisms with page
`r₀`; the third identifies each limiting page with page `r₀`.  The final clause
is the edge map in each total degree, represented by an isomorphism from the
abutment object `(A n).obj` to `X.page r₀ 0 n`.

Edge cases checked: `r₀ = 2` is allowed; the vanishing condition leaves the
zeroth column; arbitrary integer total degree `n` and empty/zero abutment
objects are permitted by the categorical formulation.

Searches made: `msearch.py leanfinder "spectral sequence edge collapse vanishing column isomorphism"`
(found only unrelated HomologicalComplex differential lemmas); `msearch.py loogle
"BigradedExactCouple ConvergesTo"` (0 hits, unknown identifier); `rg` over
`WeilConjectures/` and `lean/Sheaf/` (no existing edge-collapse declaration);
Mathlib spectral-sequence grep (no exact-couple edge-collapse theorem).

## Earlier second reading (a previous round; superseded)

Pending independent reading by the dispatcher’s second worker. This section is reserved for that worker; no independent reading has yet occurred.

The final stationary-page and limiting-page clauses include the canonical cycle-boundary projection compatibility; the edge clause identifies the canonical map through `toPageInfinity` and the page projection.

## Second reading by S1

I independently read the node statement, its three statement dependencies, and
`Sheaf/CategoryTheory/EdgeCollapse.lean`.

- The exact-couple object is rendered by `(X : BigradedExactCouple C 0)` with
  `[Category.{v} C] [Abelian C]`; this is the recorded exact-couple declaration,
  including the page indexing convention `E₂ = X.page 2`, and is the same object.
- The convergent filtered abutment is rendered by `L : X.LimitSubobjects`,
  `A : ∀ n : ℤ, X.AlphaColimit n`, and `hconv : X.ConvergesTo L A`.
  `ConvergesTo` supplies regularity, weak convergence, exhaustiveness and
  separatedness, and completeness of the abutment filtration as in the node.
- The finite-filtration hypothesis is rendered exactly by
  `hfinite : ∀ n : ℤ, (X.imageFiltration n (A n)).IsFinite`.
- The page threshold and its hypothesis are rendered by
  `r₀ : ℕ` and `hr₀ : 2 ≤ r₀`; the surviving-column condition is exactly
  `hvanish : ∀ p q, p ≠ 0 → IsZero (X.page r₀ p q)`.
- The first conclusion quantifies over every `r ≥ r₀`, every `(p,q)`, and states
  `X.pageDifferential r p q = 0`, exactly expressing vanishing of all later
  differentials.
- The second conjunct quantifies over every later page and bidegree and gives an
  isomorphism `X.page r₀ p q ≅ X.page r p q`; its two displayed equations express
  compatibility with the cycle inclusions and cycle-boundary projections, so it
  is the canonical stationary-page identification rather than a weaker existence
  claim.
- The third conjunct supplies one family
  `t : ∀ p q, X.pageInfinity L p q ≅ X.page r₀ p q`; the accompanying equations
  identify the limiting-page projection with the stabilized cycle projection.
  The final clause gives, for every `n : ℤ`, an isomorphism
  `(A n).obj ≅ X.page r₀ 0 n` and identifies its composite with
  `X.toPageInfinity L 0 n`, exactly the edge map in the node (with the canonical
  `eqToHom` accounting for total-degree index normalization).

No hypothesis is added and none is omitted. The universes permit arbitrary
abelian categories, integer total degrees, and all zero or empty objects. The
case `r₀ = 2` is admitted; `hvanish` leaves the zeroth column unrestricted; and
zero abutments and zero pages are covered by `IsZero` and categorical
isomorphisms. The finite assumption is not used to narrow these cases and is
explicitly present in the node.

I searched Mathlib and the source checkout with LeanFinder/Loogle queries for
spectral-sequence edge collapse and with `rg` for `edge_collapse`,
`BigradedExactCouple`, and the relevant phrases. The only hits are the
recorded exact-couple and convergence infrastructure; no existing declaration
states this theorem. The earlier search results in `searches.jsonl` agree.

I found no mismatch in the worker's Lean statement and made no code or node
change. The module compiles cleanly with `scompile.py`; its only proof is the
required `sorry`. The node's `lean.statement` is verbatim the theorem signature.
