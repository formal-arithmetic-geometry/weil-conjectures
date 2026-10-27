## Worker report

The module `Sheaf.RingTheory.LaurentSubalgebraDimensionBound` states
`LaurentPolynomial.ringKrullDim_subalgebra_le`, with a single `sorry` proof.
It adds no definitions and changes only the item's `lean` record.
The theorem docstring carries all six proof steps, including the coefficientwise
minimal-prime reduction, fraction-field embeddings, generic transcendence bound,
and application of the scheme dimension inequality.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- A commutative ring is `(R : Type u) [CommRing R]`; `universe u` is explicit.
- Nonzero is `[Nontrivial R]`.
- Noetherian is `[IsNoetherianRing R]`.
- Finite Krull dimension `d >= 0` is `(d : ℕ)` and
  `(hd : ringKrullDim R = (d : WithBot ℕ∞))`. Equality to a natural number
  excludes both infinite dimension and the bottom dimension of the zero ring.
- The ambient ring is Mathlib's `LaurentPolynomial R`, definitionally
  `AddMonoidAlgebra R ℤ`, hence finitely supported integer-indexed coefficients,
  with coefficientwise addition and convolution multiplication. This is the
  exact ring described inline in the node, not a Laurent series ring.
- An R-subalgebra containing the constant copy is
  `(B : Subalgebra R (LaurentPolynomial R))`. `Subalgebra.algebraMap_mem`
  includes every constant automatically; `LaurentPolynomial.C_eq_algebraMap`
  identifies the inherited coefficient algebra map with the constant embedding.
- Finite type over R is `(hB : (algebraMap R B).FiniteType)`, using the exact
  dependency declaration `RingHom.FiniteType` on the induced coefficient map.
  Its equivalence with `Algebra.FiniteType R B` is
  `RingHom.finiteType_algebraMap`.
- The conclusion is `ringKrullDim B ≤ ((d + 1 : ℕ) : WithBot ℕ∞)`.
- No reducedness, domain, locality, or catenarity assumptions are present.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, lines 193–205. Its definition is
  Noetherianity as an R-module, equivalent to finite generation of all ideals.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`, lines 27–31. It is the dimension
  of the ordered prime spectrum in `WithBot ℕ∞`, with precisely the node's
  bottom and infinite values.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`, lines 211–222, together with the underlying
  `Algebra.FiniteType` at lines 37–40. It states finite generation of the
  algebra attached to the ring map. The recorded interface is usable unchanged.

The module publicly imports these three modules and the Laurent polynomial
module. Every currently stated proof dependency is imported ordinarily:

- `minimalPrimes.finite_of_isNoetherianRing` from
  `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`;
- `Ideal.sInf_minimalPrimes` from
  `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`;
- the `Ideal.ResidueField` interfaces from
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`;
- `RatFunc` from `Mathlib.FieldTheory.RatFunc.Basic` (including its Defs module);
- `Algebra.IsAlgebraic.trdeg_le_cardinalMk` from
  `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`;
- `Algebra.trdeg` from `Mathlib.RingTheory.AlgebraicIndependent.Basic`;
- `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme`;
- `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE` from
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`;
- `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`;
- `PrimeSpectrum.zeroLocus_minimalPrimes`, `PrimeSpectrum.closure_singleton`,
  and `PrimeSpectrum.pointsEquivIrreducibleCloseds` from
  `Mathlib.RingTheory.Spectrum.Prime.Topology`;
- `AlgebraicGeometry.spec_field_point_residue_field` and its generic specialization
  from `WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField`;
- `AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom` from
  `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`.

`lem-sfb-generic-residue-transcendence-dimension-bound` currently has no Lean
record or Mathlib match; it is a proof dependency only, so there is no module to
import yet. The docstring retains its final application. No missing notion is
needed to type this item's statement.

Source and edge cases:

Read `literature/stacks-project/morphisms.tex`, labels
`lemma-alteration-dimension-general` (0BAG) and
`lemma-dimension-formula-general` (0BAE). The former assumes a locally
Noetherian base and a locally finite type morphism, and bounds source dimension
by base dimension plus the supremum of generic residue transcendence degrees.
The node's six-step reduction supplies that supremum bound by one.
The current blueprint ancestor `lem-per-artin-gabber-affine-curve` was read
under `literature/blueprint/latest/`.

Checked before writing: `d = 0` gives the bound one, including Artinian bases
with nilpotents. The constant subalgebra (`B = ⊥`) gives dimension d and satisfies
the bound; the full Laurent algebra (`B = ⊤`) gives the expected one-variable
bound. Products of nonzero Noetherian rings and nonreduced rings are included;
no field or domain typeclass is inferred as a hypothesis. The zero ring is
excluded explicitly as required. For the proof plan, zero Laurent polynomials
use exponent one, and the minimal-prime family cannot be empty over a nonzero
ring. There are no test-object quantifiers or additional universe constraints.

Searches actually run through `msearch.py`, group Q29, this item:

- LeanFinder: "A finite type subalgebra of a Laurent polynomial ring over a
  Noetherian ring R of Krull dimension d has dimension at most d plus one".
  Eight hits, including `Polynomial.ringKrullDim_of_isNoetherianRing`,
  `Polynomial.ringKrullDim_le`, and multivariable polynomial bounds; none states
  the Laurent subalgebra result.
- Loogle: `"ringKrullDim", "Subalgebra"`; zero hits.
- Grep in Mathlib/RingTheory:
  `ringKrullDim.*(Subalgebra|Laurent)|Laurent.*ringKrullDim|Subalgebra.*ringKrullDim`;
  zero hits.
- LeanSearch: "Krull dimension of a finite type subalgebra of a Laurent
  polynomial ring over a Noetherian ring"; eight hits, including polynomial
  dimension theorems and quotient bounds, none the subalgebra statement.
- Direct `rg` with the dimension/Laurent/subalgebra pattern and the item id in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found
  no existing theorem. The prescribed item-id source search likewise found none.
- Direct `rg` for `ringKrullDim_subalgebra_le` and
  `ringKrullDim_le_of_finiteType_subalgebra` in Mathlib, both project roots,
  and the upstream names index found no name collision.

Validation: `scompile.py Q29 lem-per-laurent-subalgebra-dimension-bound` compiled
both the sandbox form and `Sheaf.RingTheory.LaurentSubalgebraDimensionBound` on
the server, each in 1.4 seconds, with no diagnostics. All binders and universes
are explicit. No statement correction or dispute is needed.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
