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

## Top-down bisect and exact conversion

All controls use this command from the master build tree, replacing
`<probe>` and `<skip>` with each row's values:

```text
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1200 nice -n 10 lake env lean \
  -DElab.async=false -Ddebug.skipKernelTC=<skip> \
  /path/to/dataset/KernelTimeouts/OrderedSpectralRawLattices/probes/<probe>.lean
```

| Probe | Kernel on | Kernel skipped | Result |
|---|---:|---:|---|
| `Before` | 45.73 s | 13.11 s | timeout at target on; skipped completes |
| `After` | 13.91 s | 12.51 s | passes |
| `TypeOnly` (`by sorry`) | 13.91 s | 12.41 s | declared type is cheap |
| `ApplicationOnly` (name helper, final `sorry`) | 13.91 s | 12.51 s | helper result is cheap to bind |
| `FinalExact` (name helper, `exact h`) | 48.73 s with diagnostics | not rerun | timeout at target |
| `PrintConversion` (name helper, trace, `sorry`) | 13.91 s | not rerun | prints the two types |

The exact expensive operation is the final conversion at `exact h`: the
inferred type of `CondensedRing.exists_stratified_lisse_integral_lattice
ℓ K p k hpℓ S` is checked against the declared `RawStratifiedLattices`
goal. The compact printed excerpt is:

```text
h : let A := Profinite.continuousMapRingObj ...;
    let B := Profinite.continuousMapRingObj K;
    let a := (sheafCompose ...).map ...;
    ∀ L, CondensedRing.LocallyFree (condensedRingObj B S) L →
      ∃ P, ∀ i, ∃ M, CondensedRing.LocallyFree (condensedRingObj A ...) M ∧ ...
⊢ let A₀ := Profinite.continuousMapRingObj ...;
  let B₀ := Profinite.continuousMapRingObj K;
  let a₀ := (sheafCompose ...).map ...;
  RawStratifiedLattices A₀ B₀ a₀ S
```

The proof's type expands the lattice predicate while the goal retains its
private wrapper. The source fix scopes `[-instance]` for
`IsRegularLocalRing.toIsLocalRing`, `HenselianLocalRing.toIsLocalRing`, and
`IsDomain.of_isSimpleRing`; the original comment says these proofs must
match `StratifiedLattice` to avoid unfolding coefficient topology.
Diagnostics at threshold 10000 on `FinalExact` report 23,580 reducible
`Functor.obj` reductions at the target and a Kernel deterministic timeout.
The exact smallest unequal instance argument inside the expanded predicate
was not structurally diffed.

## Classification

Primary mechanism: **E (representation/instance mismatch)**. Contributing
mechanism: **A (reduction/definitional equality)**. Evidence: **confirmed**
for the final conversion site and fixed-form improvement; **strongly
supported** for E/A by the scoped instance change, printed types, and
`Functor.obj` diagnostic. The exact inner instance difference remains
unresolved.

