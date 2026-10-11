## Worker report

The module states `PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors`; its proof is `sorry`.
`(A : Type u) [CommRing A]` renders an arbitrary commutative ring, including the zero ring.
`(a : A) (ha : a ∈ nonZeroDivisors A)` renders the non-zero-divisor hypothesis.
`basicOpen a` is the principal open `D(a)` of `PrimeSpectrum A`, and
`Dense (↑(basicOpen a) : Set (PrimeSpectrum A))` states topological density.
The explicit universe `u` imposes no size restriction on `A`.

The statement dependency `def-pc-scheme` is Mathlib's
`AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` in
`Mathlib.AlgebraicGeometry.Scheme`. Its affine spectrum is represented by
Mathlib's `PrimeSpectrum A`; `PrimeSpectrum.basicOpen` in
`Mathlib.RingTheory.Spectrum.Prime.Topology` has carrier `{p | a ∉ p.asIdeal}`.
The proof outline cites the nodes
`lem-weil-pbc-spec-localization-away-basic-open`,
`lem-pc-dense-range-comap-minimal-primes`, and
`lem-pc-minimal-prime-avoids-nonzerodivisor` (proof dependencies only).

Edge cases: for the zero ring the spectrum is empty and the empty open is dense
in it; for `a = 1`, `D(a)` is all of the spectrum. In a reduced domain such as
`k[t]`, `D(t)` is dense. In `k[x,y]/(xy)`, `x` is a zero divisor and the
hypothesis correctly excludes the non-dense `D(x)`.

Searches: `msearch.py leanfinder` for "principal open of non zero divisor is
dense in prime spectrum" returned `PrimeSpectrum.basicOpen` and minimal-prime
facts, but no exact theorem. `msearch.py loogle` for
`PrimeSpectrum.basicOpen, Dense` returned no hits. `msearch.py grep` for
`dense.*basicOpen|basicOpen.*dense|Dense.*basicOpen` in
`RingTheory/Spectrum` returned no hits. `rg` of the Mathlib prime-spectrum
topology and project `WeilConjectures` found no exact statement; `grep -rn`
for the node id in `WeilConjectures` found none. `rg` in `lean/Sheaf` found
`PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor`, whose
conclusion concerns injectivity of a sheaf restriction and density of a scheme
morphism, rather than density of the underlying basic open as a subset of
`PrimeSpectrum A`.

The local Stacks source file `literature/stacks-project/divisors.tex` is absent
on this machine; the node records Tag 07ZU and its affine-local calculation.

## Second reading by J1

The node introduces the following objects and clauses, checked against
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenDenseOfNonZeroDivisor.lean`:

- `A` is an arbitrary commutative ring: Lean `(A : Type u) [CommRing A]`.
  The explicit universe leaves the ring unrestricted in size.
- `a` is an element of that ring: Lean `(a : A)`.
- `a` is a non-zero-divisor: Lean `(ha : a ∈ nonZeroDivisors A)`.
- `D(a)` is the principal open in `Spec(A)`: Lean `basicOpen a`, coerced to
  `Set (PrimeSpectrum A)`.
- The conclusion is that this subset is topologically dense: Lean
  `Dense (↑(basicOpen a) : Set (PrimeSpectrum A))`.

The quantifier order and all hypotheses agree with the node. Mathlib's
`PrimeSpectrum` is the affine prime spectrum and `basicOpen` is its Zariski
principal open, so these definitions agree with `Spec(A)` and `D(a)`. No
scheme, Noetherian, reducedness, finiteness, characteristic, or extra ring
hypothesis is added.

Edge cases checked: the zero ring is allowed and has empty spectrum, where the
empty principal open is dense; `a = 1` gives the whole spectrum; empty schemes
are not excluded by the affine ring formulation; no index set or natural
number occurs; and the universe parameter imposes no restriction. A domain
such as `k[t]` with `a = t` satisfies the hypothesis and gives the expected
dense open. A zero divisor such as `x` in `k[x,y]/(xy)` is correctly excluded,
since its principal open need not be dense.

I searched Mathlib and the source/project with LeanFinder for
"principal open of non zero divisor is dense in prime spectrum", Loogle for
`PrimeSpectrum.basicOpen, Dense`, grep for
`dense.*basicOpen|basicOpen.*dense|Dense.*basicOpen` in the spectrum topology,
and `rg` through `WeilConjectures` and `lean/Sheaf`. These found the
basic-open and minimal-prime infrastructure and the unrelated sheaf theorem
`PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor`, but no
existing declaration of this statement. The Stacks source file is not present
locally; the node's recorded source is Tag 07ZU.

No mismatch was found, so no statement or dependency was changed. The module
was compiled with `scompile.py`; it compiled cleanly with only the intentional
`sorry` proof warning.
