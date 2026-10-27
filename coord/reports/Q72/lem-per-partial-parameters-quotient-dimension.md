## Worker report

The module `Sheaf.RingTheory.PartialParametersQuotientDimension` states
`IsLocalRing.ringKrullDim_quotient_initial_parameters`, with its sole proof `sorry`.
It states the node unchanged. The source was read in `literature/stacks-project/algebra.tex`:
Tag 02IE (`lemma-elements-generate-ideal-definition`, statement and proof), Tag 07DU
(`definition-ideal-definition`), and Tag 00KW (`lemma-one-equation`). No missing notion,
unusable dependency, statement correction, or disputed mathematical assertion was found.

The hypothesis and conclusion correspondence is:

- The commutative ring is `(A : Type u) [CommRing A]`, with arbitrary explicit universe `u`.
- Noetherianity is `[IsNoetherianRing A]`, the recorded declaration of
  `def-weil-pbc-noetherian-ring`.
- Locality with a unique maximal ideal is `[IsLocalRing A]`; its unique maximal ideal
  is `IsLocalRing.maximalIdeal A`. Mathlib's `IsLocalRing` extends `Nontrivial A`, so
  nonzeroness is included and needs no additional hypothesis. The uniqueness equivalence
  is `IsLocalRing.isMaximal_iff` in the imported maximal-ideal module.
- The nonnegative integer dimension is `(d : ℕ)` and
  `hd : ringKrullDim A = (d : WithBot ℕ∞)`. This uses the recorded definition of
  `def-weil-pbc-krull-dimension-ring`, rather than a finite-dimension proxy.
- The ordered list of exactly `d` parameters is `(a : Fin d → A)`. The index `j`
  represents the paper's index `j.val + 1`; no distinctness condition is imposed.
- Membership of every parameter in the maximal ideal is
  `ha : ∀ j : Fin d, a j ∈ maximalIdeal A`.
- The ideal `J = (a₁, ..., a_d)` is `Ideal.span (Set.range a)`.
  The ideal-of-definition condition is exactly
  `hrad : (Ideal.span (Set.range a)).radical = maximalIdeal A`.
  Mathlib's radical allows an exponent zero, but for a proper ideal a witness with
  exponent zero would say `1 ∈ J`, which is impossible. Here `ha` implies `J ≤ m`
  and `m` is proper. Thus this is exactly the node's positive-exponent radical.
- Every integer in the asserted range is quantified by
  `∀ (i : ℕ), 1 ≤ i → i ≤ d → ...`. These are exactly the possible integer values
  in the node; no negative integer can satisfy its lower bound.
- The initial segment ideal is `Ideal.span (a '' {j : Fin d | j.val < i})`.
  Its generators are precisely `a₁, ..., aᵢ`, with repetitions harmless.
- The quotient is Mathlib's `A ⧸ Ideal.span (...)`, using the quotient ring construction
  of `def-weil-pbc-algebra-hom-quotient`. The conclusion is exactly
  `ringKrullDim (A ⧸ Ideal.span (a '' {j : Fin d | j.val < i})) =
  ((d - i : ℕ) : WithBot ℕ∞)`. Since `i ≤ d`, natural subtraction agrees with
  integer subtraction. Both sides use the full Krull dimension, not its truncation.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg` confirming every ideal is finitely generated.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, whose full definition
  is `Order.krullDim (PrimeSpectrum A)` in `WithBot ℕ∞`.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: the quotient ring and its
  `Ideal.Quotient.algebra` / `Ideal.Quotient.mkₐ` interface recorded in the quotient
  dependency's `mathlib_match`. The item needs only the quotient ring carrier;
  no algebra homomorphism is an extra object in this statement. The recorded
  `AlgHom` signature in `Mathlib.Algebra.Algebra.Hom` was also read.
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`: `IsLocalRing.maximalIdeal`,
  and the underlying `IsLocalRing` class in `LocalRing.Defs`.
- Plain proof import `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`:
  `Ideal.height_le_height_add_encard_of_subset`, the recorded Mathlib match of
  `lem-weil-pbc-noetherian-height-quotient-bound`. Its signature and surrounding
  Noetherian commutative-ring binders were read. The docstring includes all five
  accepted proof steps: quotient correspondence and heights, the first height bound,
  the unique-prime full quotient, the second height bound, and the resulting equality.

Edge cases checked before writing:

- `d = 0`: `Fin d` is empty and no `i` satisfies `1 ≤ i ≤ d`; the conclusion is vacuous,
  exactly as in the node. Zero-dimensional local rings, including fields, are retained.
- `d = 1, i = 1`: the initial segment is the full parameter set and the quotient has
  dimension zero by the radical hypothesis.
- `i = d` for any positive `d`: every `Fin d` index is selected, and the right side
  is zero; the proof's remaining generator list is empty.
- `i = 1`: exactly the parameter with index zero is selected.
- The zero ring is excluded by the local-ring instance, as required by the node.
- Repetitions, zero parameters, zero divisors, and non-Cohen–Macaulay local rings
  have no additional restriction. The theorem does not replace parameters by a
  regular sequence. Infinite dimension is excluded precisely by the stated finite `d`.

Searches for an existing declaration, all on 2026-10-24:

- `msearch.py leanfinder`: "Noetherian local ring quotient by first i elements of a
  system of d parameters has Krull dimension d minus i". Eight hits, including
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`, dimension lower bounds,
  and singleton quotient equalities requiring regular elements. Read
  `Mathlib/RingTheory/KrullDimension/Regular.lean`, including the full regular-sequence
  equality signature. None states this arbitrary system-of-parameters equality.
- `msearch.py loogle`: `ringKrullDim, Ideal.radical`. One hit:
  `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain`, a dimension-one domain criterion,
  not the requested theorem.
- `msearch.py leansearch`: "In a Noetherian local ring a quotient by the first i elements
  of a system of d parameters has Krull dimension d minus i". Eight hits: quotient
  dimension monotonicity, height bounds, and regular-sequence/regular-element dimension
  formulas. None is an exact match.
- `msearch.py grep` in Mathlib `RingTheory`:
  `(systemOfParameters|SystemOfParameters|[Pp]artial.*[Pp]arameter|ringKrullDim.*radical)`.
  Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `(02IE|[Pp]artial.*[Pp]arameter|[Pp]arameter.*[Qq]uotient.*[Dd]im|[Dd]im.*[Pp]artial.*[Pp]arameter)`.
  Hits concern regular parameter quotients, power-series presentations, and Kummer
  constructions. Read `WeilConjectures/RingTheory/PowerSeriesParameterQuotient.lean`:
  its scope is the power-series/regular-parameter setting, not arbitrary local rings.
- `grep -rn` of the exact item id in `lean/WeilConjectures`: zero hits.
- Exact proposed declaration name searched with `rg` in Mathlib, both project source
  roots, and `dag/lean_names_upstream.json`: no collision.

Validation: the prescribed `scompile.py` compiled both its sandbox view and the library
module successfully, without warnings or errors. Every universe and variable is bound
explicitly. Only the item's `lean` record is changed; no new nodes or dependency repairs
are needed. Delivery preflight is run through `deliver2.py`.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
