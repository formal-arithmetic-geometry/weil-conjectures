# OrderedSpectralRawLattices: exact Kernel site

**Declaration:** `AlgebraicGeometry.ProEtale.small_spectral_raw_lattices`,
from historical fix commit `f4946fdb6b6` (2026-11-02),
`fix(sfb-2): match instance search in OrderedSpectralLattices to avoid a kernel timeout`.

## Phase gate

The historical parent and fixed source were ported to the current master
checkout with the one current API rename
`U.counitIso_functor_comp` -> `U.counitInv_functor_comp`. With Lean/Mathlib
4.35.0, single-threaded synchronous elaboration, the ported Before source
took 45.73 s and 3,283,804 KB RSS and reported
`(kernel) deterministic timeout` at `small_spectral_raw_lattices`. The same
command with Kernel checking disabled took 13.11 s and 2,486,256 KB RSS; the
command on After took 13.91 s and 2,494,432 KB RSS and exited successfully.

## Exact site and comparison

The target is the direct application
`CondensedRing.exists_stratified_lisse_integral_lattice ℓ K p k hpℓ S`.
The Before declaration reaches the target and times out in the Kernel before
the later source error at `ordered_lattices_of_coefficient_square`; the After
declaration completes and has no later error. The source files and their
ported forms are retained in this directory, so the measurement is directly
reproducible. The `Before` and `After` files under `probes/` are identical
copies used for the reported commands.

The change is an instance-search alignment in the surrounding ordered
lattice construction. Its direct effect is to make the target application
elaborate through the current coefficient and equivalence instances without
the parent proof's expensive conversion. The phase gate confirms a real
Kernel-on versus passing fixed-form difference; the exact internal reduction
chain was not isolated further because the fixed form completes in 13.91 s.

## Classification

Primary mechanism: **E (representation/instance mismatch)**. Contributing
mechanism: **A (reduction/definitional equality)**. Evidence: **confirmed**
for the declaration-level timeout and fixed-form improvement; **strongly
supported** for E/A by the historical commit message and the direct target
location.

