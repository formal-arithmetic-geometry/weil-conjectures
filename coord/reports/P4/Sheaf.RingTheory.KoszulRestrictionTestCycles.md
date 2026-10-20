## What changed

Withdrew the unimported duplicate
`lean/Sheaf/RingTheory/KoszulRestrictionTestCycles.lean` via `deleted.txt`.
Reattached node `new-t2-koszul-restriction-test-cycles` to the existing
`AlgebraicGeometry.exists_koszul_restriction_test_cycles` in
`WeilConjectures.RingTheory.KoszulRestrictionTestCycles`.
The upstream and Sheaf public signatures are byte-for-byte identical.
No consumer requires adaptation: the upstream
`WeilConjectures.RingTheory.SelfTorRestrictionConormalWedge` already imports
that upstream module, and zero modules import the Sheaf duplicate.

Change record: `coord/changes/P4-retire-koszul-restriction-test-cycles.md`.
The proof plan, proof dependencies, source theorem, and unit route are preserved.

## Proved and sorry left

The assigned module started with zero sorries. Holes closed: 0. Holes added: 0.
Sorries left: none. Split off: none. This is duplicate retirement, not a new proof.
The surviving theorem is
`AlgebraicGeometry.exists_koszul_restriction_test_cycles`.

A scratch theorem with the original full signature, proved by applying the
upstream declaration, compiled in 2.0 seconds. `#print axioms` on both the
upstream theorem and the signature-check theorem lists exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Pruned module: `Sheaf.RingTheory.KoszulRestrictionTestCycles`, its duplicate
public theorem body, and its private construction helpers. No modules still
import it. The following imports disappear with the withdrawn copy:

- `public import WeilConjectures.AlgebraicGeometry.KoszulComplex`
- `public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution`
- `public import Mathlib.LinearAlgebra.ExteriorPower.Basic`
- `public import Mathlib.Algebra.Category.ModuleCat.Projective`
- `public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`
- `public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `import WeilConjectures.RingTheory.KoszulAugmentationLiftExists`
- `import WeilConjectures.RingTheory.KoszulGeneratorChainMap`
- `import Mathlib.LinearAlgebra.ExteriorPower.Basis`
- `import Mathlib.LinearAlgebra.TensorProduct.Basis`
- `import Mathlib.CategoryTheory.Adjunction.Additive`
- `import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`

These are removals from the duplicate only. The upstream proof retains its
existing imports; no dependency node or upstream module is claimed pruned.
Node `new-t2-koszul-restriction-test-cycles` remains attached to its upstream
realization. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but this queue entry has kind
`retire` and zero holes. A previous retirement wave left this twin because
its consumer was in a pending landing. Consumers now use the upstream version,
and the Sheaf module has no importers. The remaining stale DAG attachment
still pointed at the duplicate; this delivery repairs it.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
