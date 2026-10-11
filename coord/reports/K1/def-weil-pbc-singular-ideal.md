## Worker report

The module defines smoothness at a prime, the set of smooth principal-localization
elements, and the singular ideal. It states the radical, smooth-locus, zero-locus,
and uniqueness clauses with `sorry` proofs.

Statement correspondence:

- A commutative ring map `R → A` is represented by `[CommRing R] [CommRing A]
  [Algebra R A]`, with no finiteness or characteristic assumption.
- `A_g` with its induced `R`-algebra structure is `Localization.Away g`.
- Smoothness at `q` is `Algebra.IsSmoothAtPrime R q`, whose body is
  `∃ g : A, g ∉ q.asIdeal ∧ Smooth R (Localization.Away g)`.
- `G` is `Algebra.smoothElements R A = {g | Smooth R (Localization.Away g)}`.
- `H_{A/R} = √(G)` is `Algebra.singularIdeal R A =
  (Ideal.span (smoothElements R A)).radical`.
- Its radical property is `Algebra.singularIdeal_isRadical`.
- The equality of the smooth locus with the union of the `D(g)` is
  `Algebra.smoothAtPrime_locus_eq`; openness is
  `Algebra.isOpen_smoothAtPrime_locus`.
- The equality of `V(H)` with the nonsmooth locus and the intersection of all
  `V(g)` is `Algebra.singularIdeal_zeroLocus`.
- The uniqueness among radical ideals with this zero locus is
  `Algebra.singularIdeal_unique`.

Dependency: `Algebra.Smooth` from `Mathlib.RingTheory.Smooth.Basic`, the recorded
`mathlib_match` of `def-weil-pbc-smooth-ring-map`. Its source declaration says a
smooth algebra is formally smooth and finitely presented. The localization uses
Mathlib's `Localization.Away`. The radical, span, basic opens, and zero locus use
Mathlib's `Ideal` and `PrimeSpectrum` declarations.

Edge cases: no nonzero-ring, finite-presentation, Noetherian, or characteristic
condition was introduced. In a zero ring, there are no primes; the set and ideal
definitions still type. If no principal localization is smooth, `G` is empty and
the ideal is the radical of the zero ideal. If `g = 0`, `Localization.Away 0` is
still a valid localization and the definitions still type.

Searches:

- `msearch.py leanfinder` query `singular ideal of algebra radical of elements
  whose localization is smooth over base ring`: returned `Algebra.smoothLocus`
  and `Algebra.IsSmoothAt`, but no singular ideal. `IsSmoothAt` means formal
  smoothness at a prime and is not the arbitrary-map 00TB predicate here.
- `msearch.py loogle` query `Algebra.smoothLocus, Algebra.Smooth,
  Ideal.radical`: no hit.
- `msearch.py grep` query `singularIdeal|singular ideal|smoothLocus|IsSmoothAt`
  in `RingTheory/Smooth`: smooth-locus references only, no singular ideal.
- `rg` in `WeilConjectures` for `SingularIdeal|singularIdeal|IsSmoothAt|smoothLocus`:
  smooth-locus uses only, no definition of this ideal.
- `grep -rn def-weil-pbc-singular-ideal` in `WeilConjectures`: no hit.
- `rg` in the project's `lean/Sheaf`: no matching definition.

The local `literature/stacks-project/smoothing.tex` was absent from this checkout.
Stacks Project Tag 07C5 was read at https://stacks.math.columbia.edu/tag/07C5;
it defines the unique radical ideal with the nonsmooth locus as zero locus.

Compilation: `scompile.py K1 def-weil-pbc-singular-ideal` completed without errors
or warnings after the final docstring expansion.

## Second reading by K1

I opened `dag/nodes/sec-proper-base-change/def-weil-pbc-singular-ideal.json` and
`lean/Sheaf/RingTheory/SingularIdeal.lean` independently. The correspondence is:

- The node's commutative rings and ring map `R → A` are the binders
  `[CommRing R] [CommRing A] [Algebra R A]` in every declaration; the two
  universes `u v` allow arbitrary universe levels. No finite-presentation,
  Noetherian, characteristic, nonzero, or field hypothesis is added.
- The node's `A_g` with its induced `R`-algebra structure is
  `Localization.Away g` in `IsSmoothAtPrime` and `smoothElements`, with the
  canonical induced algebra instance. The condition `g ∉ q` is rendered as
  `g ∉ q.asIdeal` for `q : PrimeSpectrum A`.
- The node's `G = {g | A_g is smooth over R}` is exactly
  `smoothElements R A`; `singularIdeal` is exactly
  `(Ideal.span (smoothElements R A)).radical`.
- The radical clause is `singularIdeal_isRadical`. The smooth-locus clause is
  `smoothAtPrime_locus_eq`, and its openness clause is
  `isOpen_smoothAtPrime_locus`.
- The two zero-locus clauses in the node are the conjunction in
  `singularIdeal_zeroLocus`: `V(H)` is the set of primes where
  `¬ IsSmoothAtPrime R q`, and it is the intersection of the `V(g)` for
  `g ∈ smoothElements R A`.
- The node's uniqueness clause is `singularIdeal_unique`, whose hypotheses are
  exactly that `J` is radical and has the stated nonsmooth zero locus, and
  whose conclusion is `J = singularIdeal R A`.

No mismatch was found and no Lean source change was needed. In particular,
the empty smooth-elements set, `g = 0`, zero rings, empty prime spectra, and
`n = 0` presentations are not excluded by the declarations. The dependency
`Algebra.Smooth` was checked in `Mathlib.RingTheory.Smooth.Basic`; it is the
recorded smooth-algebra notion used by the node's dependency. The existing
definition searches listed above found no singular-ideal declaration in
Mathlib, `WeilConjectures`, or the project `lean/Sheaf`.
