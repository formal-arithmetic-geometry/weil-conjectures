## Worker report

The module `Sheaf.RingTheory.PolynomialClosedFibreComponents` states
`MvPolynomial.isCatenaryRing_equidimensional_localizationAtMaximal` with proof
`sorry`. No definitions are introduced and nothing is proved. The module and
its docstring follow the eight proof steps of the node. I read the final two
paragraphs of Stacks Project, more-algebra.tex, lemma-formally-catenary (Tag
0AW5), including its dimension display. No statement correction or dependency
repair is needed; the node changes only in `lean`.

Hypotheses and clauses, individually:

- The commutative ring C is `(C : Type u) [CommRing C]`, with arbitrary explicit
  universe `u`; `[IsNoetherianRing C]` is Noetherianity and `[IsLocalRing C]`
  is locality. The named maximal ideal n is `IsLocalRing.maximalIdeal C`.
- Equidimensionality of Spec C is `heq`: for every two subsets Z and W of
  `Spec (.of C)` belonging to `irreducibleComponents`, their
  `topologicalKrullDim` values agree. This is equality of component dimensions,
  without assuming irreducibility, reducedness, or a common dimension in advance.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, exactly
  completeness for the maximal-ideal-adic topology, including separatedness.
- The nonnegative number r of variables is `(r : ℕ)`. The polynomial ring is
  `MvPolynomial (Fin r) C`, using the dependency's existing polynomial construction.
- The maximal ideal n' is `(M : Ideal (MvPolynomial (Fin r) C)) [M.IsMaximal]`.
  Its lying over n is `hclosed`, the equality of its comap along the coefficient
  homomorphism `MvPolynomial.C` with `IsLocalRing.maximalIdeal C`.
- The localization in the conclusion is the recorded `Localization.AtPrime M`.
  Its prime-ideal instance is inferred from the maximal-ideal hypothesis.
- Catenarity is the first conjunct, `IsCatenaryRing (Localization.AtPrime M)`.
- Equidimensionality of its spectrum is the second conjunct, again equality of
  `topologicalKrullDim` for any two members of `irreducibleComponents` of the
  scheme `Spec (.of (Localization.AtPrime M))`.
- The last conjunct quantifies over every component Z of that same spectrum and
  states `topologicalKrullDim Z = ringKrullDim C + (r : WithBot ℕ∞)`. The subtype
  topology on Z gives precisely its component dimension. No finite-dimension
  truncation is used.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg`, for def-weil-pbc-noetherian-ring.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` and
  `IsAdicComplete`, for def-weil-pbc-adic-completion. The statement needs only
  the companion completeness notion recorded on that node.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and its underlying
  spectrum, for def-weil-affine-spectrum.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, maximal nonempty
  irreducible subsets, for def-weil-irreducible-components.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, with values in
  `WithBot ℕ∞`, for def-kun-topological-krull-dimension.
- `Sheaf.RingTheory.ExcellentRing`: `IsCatenaryRing`, with its finite chain bound
  and equality of saturated lengths, for def-exc-excellent-ring. Its
  `IsUniversallyCatenary` and `IsExcellent` are the proof interfaces.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and `MvPolynomial.C`,
  for def-weil-pbc-mv-polynomial-ring.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  for def-weil-pbc-localization-at-prime.

All additional recorded proof dependencies are imported non-publicly:
`Mathlib.RingTheory.RingHom.Flat` (`RingHom.Flat`),
`Sheaf.RingTheory.CompleteLocalExcellent`
(`isExcellent_of_isNoetherianRing_of_isAdicComplete`),
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
`Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
(`MvPolynomial.ringKrullDim_localizationAtMaximal`),
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`
(`Ideal.exists_minimalPrimes_le`), and
`Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.zeroLocus_minimalPrimes` and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`). The declarations and
source signatures were read, not inferred from their names.

Edge cases checked mathematically before writing:

- r = 0: the polynomial ring is C; localizing at its maximal ideal returns C.
  The conclusion is catenarity of complete local C and its original component
  dimensions, with zero added.
- C a field: completeness is for the zero ideal, and closed-point polynomial
  localizations have dimension r. No characteristic restriction is imposed.
- C = k[[u,v]]/(uv): two components of dimension one are allowed; localizing
  at (u,v,x_1,...,x_r) gives components of dimension 1+r. There is no domain
  assumption or selection of a single component.
- Nilpotents, for example k[epsilon]/(epsilon^2), are allowed; its underlying
  spectrum has dimension zero and the polynomial component dimension is r.
- Nonrational closed points are included, for example C = real[[t]], r = 1,
  M = (t,x^2+1). Its residue field need not equal the residue field of C.
- The closed-fibre hypothesis is substantive: localization at the prime (x)
  of k[[t]][x] contracts to (0), and its dimension is one rather than two.
  The Lean retains contraction equality, not merely containment.
- A zero ring has no maximal ideal, so cannot supply M. This introduces no
  excluded valid instance and avoids treating empty components as irreducible.
- All ring sizes are covered by explicit `universe u`; finite variable indices
  and the canonical localization introduce no additional size restriction.

Searches for an existing exact statement (all through authorized wrappers or
read-only source searches):

- msearch.py, LeanSearch: “A polynomial ring over a complete equidimensional
  Noetherian local ring localized at a closed fibre maximal ideal is catenary
  with equidimensional spectrum”. Eight hits concern Noetherian spectra,
  Jacobson polynomial rings, local closed points, finite local dimension, and
  local Noetherian criteria; none states this theorem.
- msearch.py, LeanFinder: “A complete Noetherian equidimensional local ring
  localized polynomial ring at maximal ideal over closed point is catenary
  equidimensional dimension base plus variables”. Eight results include
  polynomial maximal-ideal heights and regular-element dimension formulas;
  none gives catenarity and the component assertion.
- msearch.py, Loogle: `"ringKrullDim", "MvPolynomial"`. Six results are global
  polynomial dimension formulas and bounds, including
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`. They do not describe
  equidimensional components of the specified localization.
- msearch.py, grep: `equidimensional|IsCatenaryRing|catenary`, under Mathlib
  RingTheory. No hits.
- Read-only rg on upstream WeilConjectures for `equidimensional|IsCatenaryRing`
  and catenarity, and grep for this exact blueprint id: no exact statement.
- Read-only rg on lean/Sheaf for equidimensionality and catenarity found
  ExcellentRing, CompleteLocalExcellent, FlatEquidimensionalCatenaryDescent,
  RatliffFormalCatenarity and unrelated dimension results. The first two are
  used as dependencies; the descent theorem has a different statement and
  RatliffFormalCatenarity cites this item in its proof rather than stating it.
- The proposed full declaration name was searched in Mathlib, upstream
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json; no collision.

Validation: scompile.py NW lem-per-polynomial-closed-fibre-components compiled
this file successfully, in both sandbox and library naming contexts (1.6 seconds
per context), with no diagnostics. All variables and the universe are explicitly
bound and `autoImplicit` is disabled. Exactly one named theorem has `sorry`.
No STATEMENT-DISPUTED issue was found.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
