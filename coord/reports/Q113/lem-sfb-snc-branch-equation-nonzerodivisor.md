## Worker report

The module `Sheaf.AlgebraicGeometry.SNCBranchEquationNonzerodivisor` states
`AlgebraicGeometry.sncBranchEquation_mul_injective` with `sorry` as its entire proof.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item is unchanged except for its new `lean` record. Its existing Q151 review
is a stage-1 split review, not a Lean statement attachment; the base has no `lean`
record for the item. The previous unchanged-node dry-run failure is addressed by
supplying this missing Lean statement and attachment.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`, with explicit universe `u`.
- Regularity of `X = Spec A`: `hA : IsRegularScheme (Spec (.of A))`, using the
  recorded dependency, which includes both local Noetherianity and regular stalks.
- A finite list of equations, including zero equations: `(r : ℕ) (t : Fin r → A)`.
- The strict normal crossings boundary on that same affine scheme: the ideal
  sheaf data `H` and `hH : IsStrictNormalCrossingsBoundary H`, using the recorded
  predicate without replacing or specializing its definition.
- Reduced closed subscheme structures on `V(t i)`: `hreduced` states
  `_root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A))` for every index. The quotient
  is precisely the coordinate ring of the closed subscheme, so this expresses
  the node's word “reduced”; mere equality of supports would not suffice.
- Pairwise distinct branches: `hdistinct` is injectivity of the map sending the
  index to `PrimeSpectrum.zeroLocus ({t i} : Set A)`. For reduced closed subschemes,
  their supports determine them, so distinct supports mean distinct branches.
- These are precisely the irreducible branches of H: `hbranches` equates the
  range of these zero loci with the ambient images of `irreducibleComponents`
  of the support of H. `Set.image Subtype.val` embeds each component of the
  support subtype in Spec A; the outer `Set.image` collects them. In combination
  with `hreduced`, each specified closed subscheme is exactly the corresponding
  reduced irreducible component. This is the same branch interface used by
  the landed sibling `isRegularRing_snc_finiteRoot`.
- Injectivity of multiplication by every equation: the first conjunct is
  `∀ i : Fin r, Function.Injective (fun a : A ↦ t i * a)`.
- Injectivity of multiplication by their product: the second conjunct is
  `Function.Injective (fun a : A ↦ (∏ i : Fin r, t i) * a)`.
- The zero ring is allowed: there is no `Nontrivial A`, domain, field, or
  characteristic hypothesis. For `r = 0`, `Fin 0` is empty and the finite product
  is 1, precisely as required; its multiplication is the identity.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`:
  exactly `IsLocallyNoetherian X ∧ IsRegular X`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`: invertible radical ideal,
  finitely many distinct integral regular branches, support union, and all
  scheme-theoretic intersection regularity/dimension conditions. These two
  statement dependencies are imported publicly.
- The proof-dependency modules are imported without `public`: upstream
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` provides
  `IsRegularLocalRing.isDomain`; Mathlib's `Localization.AtPrime.Basic`,
  `Localization.Ideal`, `Noetherian.Defs`, `Ideal.KrullsHeightTheorem`,
  `Spectrum.Maximal.Localization`, and `AlgebraicGeometry.StructureSheaf` provide
  `Localization.AtPrime`, the quotient-localization instance,
  `IsNoetherianRing`, `ringKrullDim_le_spanFinrank_maximalIdeal`,
  `PrimeSpectrum.toPiLocalization_injective`, and
  `StructureSheaf.IsLocalization.to_stalk`, respectively. These are the recorded
  `lean` declarations or `mathlib_match` of the proof dependencies; none is
  restated. The source modules/signatures of both statement dependencies were
  read in full. The main docstring carries all five steps of the DAG proof,
  including the finite-dimensional contradiction and joint-localization descent.

Source check: read `literature/stacks-project/etale.tex`,
`definition-strict-normal-crossings` and `lemma-strict-normal-crossings` (Tags
0BI9, 0BIA). The latter explicitly identifies reduced irreducible components,
regular intersections of the expected codimension, and cancellation by a branch
parameter. The DAG's assertion is explicitly a derived combination, not a
verbatim quotation; its proof uses the existing boundary definition's singleton
local-dimension equality, regular-local domains (00NP), and joint injectivity
of prime localizations (00HN).

Edge cases checked before writing:

- `r = 0`: first conjunct vacuous; product is 1. On a nonempty regular affine
  scheme the empty boundary has no irreducible components, so this is admissible.
- A zero ring: Spec is empty and has no integral branches. `hbranches` therefore
  forces the equation family to be empty. Multiplication on A is injective
  regardless, since A is a singleton; no case is excluded by the statement.
- A disconnected regular ring, e.g. `k[x] × k`: equation `(x,1)` gives the single
  reduced codimension-one branch and is a nonzerodivisor. Equation `(x,0)` would
  contain a whole connected component and does not satisfy the SNC branch
  hypothesis. No incorrect global-domain assumption was introduced.
- A unit equation has empty zero locus, which cannot be an irreducible component;
  repeated branch supports violate `hdistinct`. A nonreduced equation such as
  `x²` in `k[x]` violates `hreduced`; the scheme structure has not been discarded.
- No characteristic, positivity of r, choice of field, or extra Noetherian
  assumption on A was imposed. One arbitrary universe suffices for Spec A.

Searches for an existing statement (all through prescribed msearch or read-only rg):

- LeanFinder: “An equation of an irreducible branch of a strict normal crossings
  boundary on a regular affine scheme acts injectively on its coordinate ring”:
  eight hits, including `PrimeSpectrum.toPiLocalization_injective` and unrelated
  scheme/Weierstrass injectivity results; none states the SNC assertion.
- Loogle: `IsStrictNormalCrossingsBoundary, Function.Injective`: no hits; the
  service does not index the project's boundary predicate.
- LeanSearch: “A branch equation of a strict normal crossings divisor is a non
  zero divisor”: eight hits on `nonZeroDivisors`, meromorphic divisors, and
  `AlgebraicGeometry.germ_eq_zero_of_pow_mul_eq_zero`; none is this statement.
- Mathlib grep through msearch: `IsRegularRing|IsSMulRegular.*minimalPrimes|nonZeroDivisors.*height`
  in RingTheory finds regular-ring definitions and related ring results, not an
  SNC branch theorem. `StrictNormalCross|normal.crossings|branch.*nonZeroDivisors`
  in AlgebraicGeometry gives zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `strictNormalCross|StrictNormalCross|snc.*[Nn]onzero|branch.*[Ii]njective|branch.*[Rr]egular`
  found the existing boundary predicate, parameter criterion, root-ring siblings,
  and downstream root-chart statements; no declaration says this node's claim.
  The finite-root regular-ring sibling confirms the reduced/distinct/complete
  branch hypotheses used here. `grep -rn` of the item id in `lean/WeilConjectures`
  gave no hits. A further name search in both source roots and
  `dag/lean_names_upstream.json` found no conflicting declaration name.

Validation: the prescribed `scompile.py Q113` invocation compiled the delivered
file in both sandbox and library modes on the server (6.3 s and 6.1 s), with
no errors or unexpected warnings. No direct local compiler or global build was run.
No statement dispute or unresolved node fault remains.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
