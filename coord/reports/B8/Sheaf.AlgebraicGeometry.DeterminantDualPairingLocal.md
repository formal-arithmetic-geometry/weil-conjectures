## What changed

Completed the retirement assigned by coord/retire-items.tsv, row 487. Withdraw
Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal via deleted.txt and attach
lem-sc-exterior-dual-pairing-local-bijective to the already proved official
WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal theorem.

Adapt all three direct consumers: DeterminantExteriorDualIso,
KoszulSelfExtDualExteriorConormal, and KoszulSelfExtYonedaSurjection. They import
the official pairing theorem and the existing ExteriorSheafPowerComparison.
Conjugate each legacy pairing by the exterior comparison and its dual. The two
inverse-wedge formulas prove the official determinant hypothesis. Cancel the
bijective section comparisons to recover the original local bijectivity.
Consumer statements, public imports, attributes, and docstrings are unchanged.
Update their existing DAG proofs to record the comparison tool dependency.
The unit and chapter route is preserved. The generic construction-comparison
node is used only to identify two implementations, not to replace a unit step.

All three consumer files compile in import order against the sandbox overlay:
3.1 s, 8.9 s, and 8.6 s, without warnings or holes. The change record is
coord/changes/retire-determinant-dual-pairing-local.md.

## Proved and sorry left

This is a zero-hole retirement: 0 of 0 original sorries closed; 0 added; 0 split
off; no sorries remain in any delivered Lean module. The retired theorem
AlgebraicGeometry.exterior_dual_pairing_app_bijective was already proved; its
fully proved official counterpart supplies all local bijectivity uses.

The following consumer theorems retain complete proofs:

- AlgebraicGeometry.exteriorSheaf_dual_iso.
- AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal.
- AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal. All three
private imports of this module are replaced by its official twin. Its private
rec_eq_cast helper and the entire duplicate determinant-basis proof disappear.
No module in lean/ or quarantine/ still imports this copy after the delivery.

The official local pairing proof does not require
lem-sc-exterior-sheaf-presheaf-upstream-comparison, so remove that proof dependency
from its node. The withdrawn module's imports of
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPresheafComparison and
Mathlib.Tactic.DepRewrite are unnecessary for this proof. The canonical iso API
supplies the consumer compatibility instead. The presheaf-comparison module is
still needed elsewhere and is not withdrawn. The local-frame and exterior-basis
nodes remain required by the official proof. No further modules or nodes are
claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but the current queue and
retire-items.tsv assign retirement of a proved duplicate (zero holes).
The old node attachment points to the copy, and its proof describes cast-based
transport of official frames. The official theorem instead obtains official
frames directly. The node now records that existing proof, while the three
consumer nodes record transport of the determinant morphism through the already
proved exteriorSheafPowerIso and inverse-wedge formula.

The assignment is fully repaired without changing upstream declarations,
definitions, targets, or mathematical hypotheses. No new nodes were needed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
