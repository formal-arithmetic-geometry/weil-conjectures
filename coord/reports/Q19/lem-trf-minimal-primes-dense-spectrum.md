## Worker report

The module `Sheaf.TraceFormula.MinimalPrimesDenseSpectrum` states
`minimalPrimes_dense_spectrum` with proof `sorry`. It renders the node's field `k`,
commutative ring `A`, `k`-algebra structure, and finite-type hypothesis as
`{k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
[Algebra.FiniteType k A]`. The conclusion is
`Dense {p : PrimeSpectrum A | p.asIdeal ∈ minimalPrimes A}`: the displayed set is
exactly the points corresponding to minimal prime ideals, and `Dense` means that every
nonempty open subset of the Zariski spectrum meets it. The affine spectrum dependency
is rendered by Mathlib's `PrimeSpectrum A` underlying the scheme `AlgebraicGeometry.Spec
(CommRingCat.of A)`.

The proof docstring records the source argument clause by clause. A nonempty open has a
point; `PrimeSpectrum.isTopologicalBasis_basic_opens` supplies a principal basic open
`D(f)` inside it; `Ideal.exists_minimalPrimes_le` supplies a minimal prime below the
chosen prime; containment preserves `f ∉ p`; hence the minimal-prime point lies in the
original open. The zero ring has empty spectrum, so the density assertion is vacuous;
for a field the unique point is minimal; nilpotents do not affect the argument.

Dependencies used are Mathlib `Algebra.FiniteType`/`RingHom.FiniteType` from
`Mathlib.RingTheory.FiniteType` and Mathlib's affine spectrum `AlgebraicGeometry.Spec`
from `Mathlib.AlgebraicGeometry.Scheme`. The topology and minimal-prime ingredients are
`PrimeSpectrum.isTopologicalBasis_basic_opens` and
`Ideal.exists_minimalPrimes_le` from `Mathlib.RingTheory.Spectrum.Prime.Topology`
and its imported minimal-prime theory.

Searches made: `msearch.py Q19 lem-trf-minimal-primes-dense-spectrum leanfinder
"finite type algebra over field"` returned only generic finite-generation and field
extension results; `loogle "Algebra.FiniteType, PrimeSpectrum, Spec"` returned no
usable direct match; `grep "PrimeSpectrum|Algebra.FiniteType" Mathlib/RingTheory/Spectrum`
found the basis, minimal-prime, and dense-range ingredients but no exact theorem. Direct
`rg` over `WeilConjectures/` and project `lean/Sheaf/` found no existing declaration for
this item or an exact minimal-prime density theorem. The DAG records the same searches
and has no Mathlib declaration matching the complete statement.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
