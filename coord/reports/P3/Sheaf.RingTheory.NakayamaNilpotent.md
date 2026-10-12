## What changed

Proved `RingTheory.surjective_of_surjective_mod_nilpotent` in
`Sheaf.RingTheory.NakayamaNilpotent`, preserving its signature and visibility.
Surjectivity of `mapQ` gives `I • ⊤ ⊔ u.range = ⊤` via Mathlib's range and quotient
identities. Induction proves `I ^ n • ⊤ ⊔ u.range = ⊤`: distribute scalar
multiplication over the sum and absorb `I ^ n • u.range` into `u.range`.
Substitution of the nilpotent power yields `u.range = ⊤` and surjectivity.
Updated the existing node's proof and proof origin to record this direct
submodule version of the source's nilpotent-power argument.

Mathlib search used the launcher's LeanFinder, Loogle, and grep services, plus
local searches in Mathlib, WeilConjectures, and Sheaf. The nearby adic completion
result requires completeness and separatedness instances; finite-generation
Nakayama results do not apply. The proof instead uses only elementary submodule
identities from the two existing Mathlib imports.

The module compiles without warnings using `lcompile.py`. The argument covers
arbitrary modules, the zero ideal, zero modules, and the trivial ring, without
any finiteness or nontriviality assumptions. The node is below the unit's
realized statement and steps, and the unit route is preserved.

## Proved and sorry left

Closed one hole: `RingTheory.surjective_of_surjective_mod_nilpotent`
(node `lem-weil-pbc-nakayama-nilpotent`). No holes remain in the module.
No holes were added; no statements were split off.

## No longer needed

None. Both existing imports are required by the unchanged statement:
`Mathlib.LinearAlgebra.Quotient.Basic` and `Mathlib.RingTheory.Ideal.Operations`.
There were no project proof-dependency imports or nodes to prune.
The quotient-by-range construction in the original proof plan is unnecessary;
the same nilpotent-power argument is performed directly on submodule sums.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The original quotient argument is
valid; direct induction on `I ^ n • ⊤ ⊔ u.range` is a shorter formalization.
The source file named by the node is absent from this clone; the node contains
its quoted nilpotent-power proof and the full source reference.

## Second reading by P3

1. Compared the delivered module with the repository version. The theorem
   signature, declaration name, visibility, imports, and surrounding definitions
   are unchanged; only the proof body replaces `sorry`.
2. Compiled the module with `lcompile.py` and checked the theorem's axioms. It
   compiles without warnings, has no remaining `sorry`, and depends only on
   `propext`, `Classical.choice`, and `Quot.sound`; no forbidden declarations occur.
3. Checked the existing node and the proof against Stacks Algebra Lemma 00DV
   (9)--(11). The nilpotent hypothesis is used with a positive exponent, the
   quotient-map hypothesis is converted to the range equality, and the induction
   proves exactly the stated surjectivity. No new statement was split off.
4. Checked the proof route and pruning. The direct submodule induction is a
   shorter valid route than introducing a quotient module; both public imports
   are needed for the unchanged interface, and the node's empty `proof_deps`
   correctly records that only Mathlib declarations are used.
5. Checked the unit record: this lemma remains below and is used by the unit's
   realized steps, so the unit route is preserved. No target statement or
   definition changed.

Changed only this second-reading report section; no Lean code, node statement,
or imports required repair.
