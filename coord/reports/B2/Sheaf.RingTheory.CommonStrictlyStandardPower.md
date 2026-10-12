## What changed

Completed the proof of `Algebra.exists_common_strictlyStandard_power` in
`Sheaf.RingTheory.CommonStrictlyStandardPower`. For each index, the chosen finite
free basis of the localized Kähler differentials is reindexed to a `Fin` basis.
`LinearEquiv.prodUnique` supplies the rank-zero summand required by
`smooth_free_differentials_strictly_standard_power`; the resulting threshold is
combined using one plus the finite sum of thresholds. The module's proof-only
import of `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower` is used.

## Proved and sorry left

Closed `Algebra.exists_common_strictlyStandard_power` (node
`lem-weil-pbc-common-strictly-standard-power`). No `sorry` remains in the
item and no new holes or nodes were added. Holes closed: 1; holes added: 0.
The axiom check still includes `sorryAx` inherited from the existing
`Algebra.smooth_free_differentials_strictly_standard_power` dependency; this
delivery closes the local hole, not the remaining upstream obligations.

## No longer needed

None. The stated single-element dependency remains necessary, and no planned
unit step or dependency was bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt incorrectly supplied an equivalence from the zero module to
the differential module. The required equivalence is obtained from the chosen
finite free basis of the differential module, after adding the unique rank-zero
factor. The compiled dependency exposes the repaired product-parenthesized
signature, so no dependency adaptation is needed.


## Second reading by B2

1. **Unchanged interface — pass.** Compared every delivered Lean file (one)
   against the repository using `diff -u`. The theorem signature, docstring,
   namespace, universes, visibility and all imports are byte-for-byte unchanged;
   only the theorem proof changes. No definitions or change records are added.
2. **Proof and axioms — pass.** Compiled the module with `lcompile.py`, without
   errors or warnings. A scratch copy with `#print axioms` reports only
   `propext`, `Classical.choice`, `Quot.sound` and inherited `sorryAx` for both
   this theorem and its single-element dependency. No delivered declaration
   contains `sorry`, and there are no forbidden declarations or attributes.
   All choices in the proof supply proof witnesses; no public definition chooses
   data from an unproved mere-existence theorem.
3. **Split statements — pass, none.** No new statements, nodes or holes are
   split off. Checked the rank-zero stable-free specialization: `prodUnique`
   removes the unique `Fin 0` summand, and the basis representation is then
   reindexed to `Fin t`. Mathlib's `ChooseBasisIndex.fintype` explicitly handles
   subsingleton rings, so zero localizations need no nontriviality assumption.
   For an empty index type the sum is zero and the chosen exponent is one;
   for a singleton the exponent is one plus its threshold.
4. **Route and pruning — pass.** Independently searched Mathlib through
   `msearch.py grep` for standard powers, basis indices and `prodUnique`, and
   searched the library for strictly-standard powers and common exponents.
   No existing theorem replaces the common-exponent reduction. The proof uses
   its sole planned dependency, the single-element threshold theorem, with
   elementary finite-sum bounds. The three public imports supply signature
   notions; the single-element dependency is a plain proof-only import.
   `No longer needed: None` is complete. Read `dag/units/sk-thm-p1.json`:
   no realized unit statement or step is bypassed or changed.
5. **DAG agreement — pass.** The node retains its statement and sole
   `proof_deps` entry. Its revised `proof` describes exactly the finite basis,
   rank-zero summand and threshold-sum argument; `proof_origin` records the
   same source route. Only the permitted proof metadata differs from the
   repository node. Read the landed stable-product change record and verified
   the current dependency's parenthesized product matches this application.

Second reading changed only this report: recorded the independent checks,
explicit hole counts and the inherited upstream `sorryAx`. The Lean proof and
node metadata needed no repair.
