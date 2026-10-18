## What changed

Proved `Ideal.reduced_ideals_zero_intersection` in
`Sheaf.RingTheory.ReducedIdealsZeroIntersection`, with its signature and imports unchanged.
The proof applies `PrimeSpectrum.zeroLocus_inf` to the covering hypothesis, then
`PrimeSpectrum.zeroLocus_eq_univ_iff` and `nilradical_eq_zero` to obtain `I ⊓ J = ⊥`.
It constructs the quotient map restricted to `I` as an `A`-linear map into
`Ideal.map (Ideal.Quotient.mk J) I`. Injectivity follows because the difference of
any two lifts lies in `I ⊓ J`; surjectivity follows from
`Ideal.mem_map_iff_of_surjective` and `Ideal.Quotient.mk_surjective`.
`LinearEquiv.ofBijective` supplies the equivalence, whose value is definitionally
the required quotient image.

Read the source Stacks Project Varieties Remark 09NW (`remark-conductor`), both
Mathlib-leaf dependency nodes and their recorded signatures, and the unit's
`realized` field. The existing three-step route is unchanged, so no DAG edit is
needed. Searches used LeanFinder, Loogle, the launcher's grep search, and local
ripgrep of Mathlib and the library. The assigned file compiled cleanly through
`lcompile.py` in 2.5 seconds.

## Proved and sorry left

Closed 1 of 1 holes: `Ideal.reduced_ideals_zero_intersection`
(node `lem-sc-reduced-ideals-zero-intersection`). Added 0 holes; split off 0
statements. No `sorry` remains in the delivered module, and no other module is
changed.

## No longer needed

None. Both existing public imports are needed by the statement. Both declared
proof dependencies remain the conceptual steps of the proof:
`lem-weil-pbc-zero-locus-ideal-intersection` is used via
`PrimeSpectrum.zeroLocus_inf`, and
`lem-weil-pbc-zero-locus-eq-iff-radical-eq` is used through its Mathlib zero-locus /
nilradical criterion `PrimeSpectrum.zeroLocus_eq_univ_iff`. No module or node is
made unnecessary by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Mathlib already packages the radical
argument as `PrimeSpectrum.zeroLocus_eq_univ_iff`, so it needs no additional
intermediate statement. The zero ring and zero-ideal cases require no extra
hypotheses: the proof uses neither nontriviality nor a choice of a prime ideal.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
