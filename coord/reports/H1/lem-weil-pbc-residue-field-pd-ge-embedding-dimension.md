## Worker report

The module `lean/Sheaf/RingTheory/ResidueFieldProjectiveDimensionLowerBound.lean` states
`IsLocalRing.finrank_cotangentSpace_le_of_hasProjectiveResolutionLE`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The docstring carries
all nine proof steps of the node, including the induced maps on mG/m²G and the coefficient
argument establishing injectivity of the reduced Koszul differential.

Hypothesis and clause correspondence:

- The commutative ring R is `(R : Type u) [CommRing R]`, with its universe explicitly bound.
- The local ring (R,m) is `[IsLocalRing R]`; m is its unique `IsLocalRing.maximalIdeal R`.
  Nontriviality is included in Mathlib's local-ring notion, as required for the residue field.
- Noetherian is `[IsNoetherianRing R]`, exactly the dependency's recorded definition.
- κ = R/m is `IsLocalRing.ResidueField R`, whose actual definition is that quotient.
  `ModuleCat.of R (ResidueField R)` uses its canonical R-module structure.
- m/m² is `IsLocalRing.CotangentSpace R`, an abbreviation for the maximal ideal's
  `Ideal.Cotangent`. The latter is the quotient of m by `m • ⊤` inside m, i.e. m².
- n = dim_κ(m/m²) is written directly as
  `Module.finrank (ResidueField R) (CotangentSpace R)`; no separate n or let binder is needed.
  Mathlib supplies finite dimensionality from the Noetherian hypothesis, so finrank is the
  genuine finite vector-space dimension, not the infinite-dimensional default zero.
- The nonnegative integer d is `(d : ℕ)`, including d = 0.
- Existence of a projective resolution of κ of length at most d is the hypothesis
  `h : ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ResidueField R)) d`.
  The landed definition is an existential `ProjectiveResolution` with zero terms above d;
  projectivity and exactness are provided by that structure. There is no finite-free
  restriction or global-dimension hypothesis.
- The conclusion d ≥ n is
  `Module.finrank (ResidueField R) (CotangentSpace R) ≤ d`.
  This is the node's primary bounded-resolution formulation; the final equivalent pd
  formulation is explanatory, not a separate stronger conclusion. In particular, applying
  it to the minimal length gives the stated projective-dimension lower bound.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`;
  read its definition and `isNoetherianRing_iff_ideal_fg`. It is imported transitively by the
  cotangent module, so no redundant direct import was added.
- `def-weil-pbc-finite-global-dimension`: imported `Sheaf.RingTheory.GlobalDimension`;
  read the entire module, including the used `ModuleCat.HasProjectiveResolutionLE`.
  This is the resolution-length definition, rather than Mathlib's Ext-vanishing predicate.
- Mathlib's `IsLocalRing.ResidueField`, `IsLocalRing.CotangentSpace`, `Ideal.Cotangent`,
  and the Noetherian finite-dimensional instance were read in full from their source files.
  `Mathlib.RingTheory.Ideal.Cotangent` is the direct import for the conclusion.

Source check: the local literature checkout does not contain `literature/stacks-project/algebra.tex`.
Read the statement and full proof at [Stacks Tag 00OA](https://stacks.math.columbia.edu/tag/00OA)
instead. It agrees with the node. No statement correction or disputed statement is needed.

Edge cases checked before writing:

- n = 0 (in particular a field): the inequality is 0 ≤ d, including d = 0.
- d = 0: the hypothesis means a projective residue field and the conclusion forces m/m² = 0;
  this matches the Noetherian local field case.
- Singular Artinian examples such as k[ε]/(ε²) have no finite residue-field resolution;
  the theorem does not assert one exists and its hypothesis is not hollow.
- The zero ring is excluded by the source's local-ring-with-residue-field setting and
  Mathlib's nontrivial `IsLocalRing`, with no added nonzero-ideal condition.
- All characteristics are allowed; the signed coefficient argument also works in
  characteristic two. No domain, regularity, finite residue-field or characteristic binder.
- R has arbitrary universe u. Its residue field and the resolution live in the corresponding
  module universe, with no quantification over smaller test categories.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "projective dimension of residue field of Noetherian local ring
  at least dimension of cotangent space"`: eight results, including
  `IsLocalRing.finrank_cotangentSpace_eq_zero_iff`, the finite-dimensional cotangent instance,
  and Krull-dimension bounds; none is the required resolution-length bound.
- `msearch.py ... loogle "IsLocalRing.CotangentSpace, CategoryTheory.HasProjectiveDimensionLE"`:
  no hits.
- `msearch.py ... grep "(ResidueField|CotangentSpace|cotangentSpace|embedding).*(projective|
  Projective)|(projective|Projective).*(ResidueField|CotangentSpace|cotangentSpace|embedding)"`:
  one irrelevant KProjective/embeddingDownNat hit, no match.
- `msearch.py ... leansearch "projective dimension residue field Noetherian local ring at
  least cotangent space dimension"`: service unavailable (Internal Server Error); no verdict.
- `rg` on `WeilConjectures` and `lean/Sheaf` for residue-field projective dimension,
  cotangent space and embedding dimension found no exact declaration. Read
  `WeilConjectures/Mathlib/RingTheory/Regular/ProjectiveDimension.lean`: its residue-field
  pd equality assumes regularity, and Serre's theorem concludes regularity using the
  Ext-vanishing predicate. Neither signature is this statement.
- Search for the exact node id in `WeilConjectures` returned no hits. Search of
  `dag/lean_names_upstream.json` for related residue-field/cotangent-projective names found
  no recorded match. The chosen full declaration name was searched in Mathlib,
  `WeilConjectures`, and `lean/Sheaf`: no collision.

Validation: `scompile.py H1 lem-weil-pbc-residue-field-pd-ge-embedding-dimension` on the module
returned exit code 0, compiled in 1.4 seconds, without errors or warnings. Every variable and
universe is explicitly bound. The delivery dry run is the final worker check; the independent
second reading is left to the second reader as instructed.

## Second reading by H1

I independently read the node statement, its dependency records, and
`Sheaf.RingTheory.ResidueFieldProjectiveDimensionLowerBound`.

- The commutative ring is rendered by `(R : Type u) [CommRing R]`; verdict: matches.
- The local-ring hypothesis is rendered by `[IsLocalRing R]`, whose `ResidueField R` is
  `R ⧸ IsLocalRing.maximalIdeal R`; verdict: matches the pair `(R, m)` and κ.
- Noetherianity is rendered by `[IsNoetherianRing R]`; verdict: exactly the Mathlib leaf
  recorded for `def-weil-pbc-noetherian-ring`, with no stronger finiteness assumption.
- The integer bound is `(d : ℕ)` and the resolution hypothesis is
  `ModuleCat.HasProjectiveResolutionLE (ModuleCat.of R (ResidueField R)) d`; verdict:
  this is the dependency's recorded projective-resolution-of-length-at-most-d notion,
  including `d = 0`, with no finite-free or global-dimension hypothesis added.
- The dimension `n` is rendered directly as
  `Module.finrank (ResidueField R) (CotangentSpace R)`; verdict: `CotangentSpace R` is
  Mathlib's maximal-ideal cotangent space `m/m²`, and Noetherianity supplies its finite
  dimensionality.
- The conclusion is
  `Module.finrank (ResidueField R) (CotangentSpace R) ≤ d`; verdict: same inequality and
  quantifier order as the node. The explanatory projective-dimension equivalence in the
  prose is not asserted as an extra conclusion.

Edge cases checked again: `n = 0` and `d = 0` give the expected `0 ≤ d` or force vanishing;
the zero ring is excluded by `IsLocalRing`; arbitrary characteristic and arbitrary ring
universe are admitted; no index type, finite-residue-field, domain, or regularity assumption
is introduced. The empty scheme and empty index-set cases are irrelevant to this purely
ring-theoretic statement.

Searches were checked in Mathlib, `WeilConjectures`, and `lean/Sheaf` using LeanSearch,
LeanFinder/Loogle, and grep. They found only general projective-dimension APIs and the
cotangent-space finite-dimensionality instance, not this residue-field lower bound; the
source's regular-ring projective-dimension theorem has different hypotheses.

No mismatch was found. I changed no statement, dependency, declaration, or definition;
the node's `lean.statement` remains verbatim the theorem signature in the module.
