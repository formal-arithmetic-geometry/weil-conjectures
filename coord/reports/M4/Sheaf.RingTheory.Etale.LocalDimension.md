## What changed

Proved `RingHom.Etale.ringKrullDim_localization_eq` in
`Sheaf.RingTheory.Etale.LocalDimension` with its exact original signature, including
independent universes. The lower inequality uses the canonical localization hom,
Mathlib flatness and local faithful flatness, and the existing faithfully flat
local dimension inequality. The upper inequality uses the existing quasi-finite
local dimension inequality. Mathlib supplies finite type and discrete fibre spectra
from the etale instance; unfolding the isolated-point definition proves the required
quasi-finiteness directly. Antisymmetry completes the proof.

Replaced the proof-only import `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime` with
`Mathlib.RingTheory.Unramified.LocalStructure`. Updated the node's second proof
step and dependencies to record the local three-line quasi-finiteness verification.
The unit `sk-thm-br` has no realized steps in this node; its Brauer-group argument
is unchanged. No public imports or statements changed.

## Proved and sorry left

Closed one original hole:
`RingHom.Etale.ringKrullDim_localization_eq`
(node `lem-sc-etale-local-dimension`). No holes remain in this module and no holes
or declarations were added. The two dimension-inequality modules remain imported;
their existing proof dependencies remain the responsibility of their own items.

## No longer needed

Removed proof-only import `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime` and proof
dependency `lem-weil-pbc-etale-ring-map-quasi-finite`: the finite-type and
isolated-fibre-point facts follow directly from Mathlib instances and
`isOpen_discrete`. Thus none of that module's scheme-theoretic equivalence,
etale-base-change, finite-product-fields, tensor-swap, or fibre-prime-bijection
proof route is needed through this import. Other targets may still use that module.
All remaining imports support the original statement or the proof.

## Where the brief, the DAG or earlier work was wrong

The planned quasi-finiteness theorem
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_etale` binds both rings in one
universe. The present statement permits independent universes, so a direct
application would restrict its scope. Mathlib's universe-polymorphic
quasi-finite instance avoids that mismatch without changing either statement.
The lower-bound plan and the upper dimension inequality fit as stated.

Searches actually run: LeanFinder for etale localization dimension invariance
returned only etale/localization facts; Loogle `ringKrullDim, Localization` returned
zero hits; the logged grep for etale dimension equality returned zero hits. Direct
source searches found the localRingHom flatness lemma, local faithful-flatness
lemma, and Mathlib's unramified quasi-finite instance. Single-file compilation
checks the arbitrary-universe theorem, with no Noetherian or finite-dimensional
assumptions. No new statements required edge-case testing.

## Second reading by M4

1. **Diff and statements — pass.** Compared the delivered module and node with the repository versions. The theorem signature is byte-for-byte unchanged; only the proof-only import, proof, and DAG proof metadata changed.
2. **Compilation and axioms — pass.** Compiled the module with `lcompile.py`; it has no `sorry`, forbidden declarations, or warnings. `#print axioms RingHom.Etale.ringKrullDim_localization_eq` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statement and split review — pass.** The unchanged theorem is the Stacks 07QP local-dimension equality for arbitrary universes. No new statements or split-off holes were added; the direct Mathlib quasi-finite construction is true and sufficient.
4. **Pruning and route — pass.** The lower bound uses the existing faithfully-flat local-dimension route, and the upper bound uses the existing quasi-finite inequality. The obsolete `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime` import and its proof dependency were removed; the unit route remains represented by this node.
5. **DAG agreement — pass.** The node’s proof text and dependencies match the Lean proof, including the Mathlib quasi-finiteness step and removal of `lem-weil-pbc-etale-ring-map-quasi-finite`.

I changed only the proof, its proof-only import, the corresponding node proof metadata, and this review record.
