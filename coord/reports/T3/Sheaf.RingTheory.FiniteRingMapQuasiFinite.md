## What changed

Proved `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite` in
`lean/Sheaf/RingTheory/FiniteRingMapQuasiFinite.lean`, preserving its signature,
visibility and existing docstrings. Added the proof-only import
`Mathlib.RingTheory.QuasiFinite.Basic`.

The existing four-step DAG plan is realized by Mathlib instances and the definition:
`Module.Finite.finiteType` supplies finite type; the finite-algebra instance of
`Algebra.QuasiFinite` and `Algebra.QuasiFinite.finite_fiber` supply finite residue-field
fibres. The fibre-Artinian instance in `Mathlib.RingTheory.QuasiFinite.Basic` supplies
Artinian fibres, and the
instance in `Mathlib.RingTheory.Spectrum.Prime.Noetherian` supplies their discrete
spectra. Unfolding `Algebra.IsQuasiFiniteAtPrime` exposes the singleton of the canonical
point given by `PrimeSpectrum.preimageHomeomorphFiber`; `isOpen_discrete` proves it open.
This realizes the planned finite-discrete-spectrum and fibre-prime-bijection leaves
without adding project dependencies or changing the mathematical route. No node edit
is needed. No unit statement or realized step is bypassed.

Validation: local compilation succeeded; `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary axiom-print command was removed.
The proof needs no nontriviality assumption on either ring: if the target is zero,
there is no prime to introduce; if a fibre is zero, discreteness still holds. The
original independent universe parameters are preserved.

## Proved and sorry left

Closed the sole original hole:
`Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite`
(node `lem-weil-pbc-finite-ring-map-quasi-finite`).

Proved 1 of 1 original sorries. No sorries remain in the item, and none were added.
The axiom check confirms this is a complete proof, not a decomposition through
unproved project statements.

## No longer needed

None. No original imports were removed. All five original proof-dependency nodes
remain relevant: module finiteness, finite type, the project's isolated-fibre-point
definition, finite discrete fibre spectra, and the canonical fibre-prime correspondence.
The last two are already Mathlib leaves. No new project module is imported.

## Where the brief, the DAG or earlier work was wrong

The node's earlier Mathlib-candidate discussion overestimates the need for a comparison
between `Algebra.QuasiFiniteAt` and the project's predicate. One can prove openness
directly in the fibre spectrum using its inferred discrete topology. This implements
the original plan rather than comparing the two quasi-finiteness definitions.

Searches used the launcher: LeanFinder for finite algebras being quasi-finite at every
prime; Loogle for `PrimeSpectrum, DiscreteTopology`; grep for discrete-spectrum and
finite-type instances. The matching Mathlib sources were read. No exact source-library
replacement was found. The cited Stacks algebra source is not materialized in this
clone; the existing node's source and proof were retained, with no new sourced claims
or unproved statements added.


## Second reading by T3

1. **Interface preserved — PASS.** Compared the complete delivered module with the
   repository version using `diff -u`. The sole changes are the plain proof-only import
   `Mathlib.RingTheory.QuasiFinite.Basic` and replacement of the original `sorry`.
   The existing declaration signature, independent universes, visibility, and docstrings
   are byte for byte unchanged. No definitions or target statements changed, and no
   change records or adaptations are needed.
2. **Kernel proof — PASS.** Independently compiled the delivered file through
   `lcompile.py`: exit code 0, no warnings. Compiled a scratch copy with
   `#print axioms Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read the whole module: no remaining `sorry`, axiom, unsafe declaration, opaque
   declaration, external implementation, or data selected from an unproved theorem.
3. **Split statements — PASS (none).** There are no added declarations, split-off
   statements, new nodes, or new holes. Checked the mathematical edge cases: a zero
   target has no prime, a zero fibre has empty spectrum, and neither requires an added
   nontriviality hypothesis. Read the actual isolated-fibre-point definition, which
   uses the canonical `PrimeSpectrum.preimageHomeomorphFiber` rather than arbitrary
   witness data.
4. **Shortest route and pruning — PASS.** Independently searched the project for
   isolated-fibre and quasi-finiteness results and used a launcher grep search with
   different wording. Read Mathlib's `Module.Finite.finiteType`, finite-algebra
   `Algebra.QuasiFinite` instance, `Algebra.QuasiFinite.finite_fiber`, fibre-Artinian
   instance, and Artinian discrete-spectrum instance. Direct singleton openness avoids
   an unnecessary comparison with localized quasi-finiteness. Both imports are needed:
   the public one supplies the predicate in the signature; the plain one supplies the
   proof instances. `No longer needed` is complete: none of the five old dependency
   nodes is obsolete. Read `dag/units/sk-thm-p1.json`: the item is below the realized
   unit steps, and no unit statement, realized node, or route is removed or bypassed.
5. **DAG agreement — PASS.** Read the item's node and both Mathlib leaf records.
   Its four proof steps remain the route implemented by the inferred instances:
   finite module to finite type, finite residue-field fibre, discrete fibre spectrum,
   and openness of the canonical corresponding point. All five `proof_deps` remain
   relevant, including the correspondence used in the unfolded definition.
   The existing document `proof_origin` remains accurate. No node edit is required.

Second reading changed only this report by adding the independent review and validation
record. The first worker's Lean proof is retained unchanged. Closed one original hole,
added zero holes, split off zero statements, and pruned no modules.
