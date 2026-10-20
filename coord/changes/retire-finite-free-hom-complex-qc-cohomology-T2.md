# AlgebraicGeometry.finiteFree_homComplex_qc_cohomology

## Reason

Complete the listed retirement in coord/retire-items.tsv. The adopted source twin has
exactly the same public theorem signature and the same finite-support induction proof.
The current Sheaf module has zero holes. Both modules compile independently.
The old inventory's obstacles (Sheaf HomComplexProjections, StupidTailHomShortExact,
and DerivedCategory dependencies) have already been migrated: every current import
of the item is a WeilConjectures or Mathlib import.

## Old

The duplicate Sheaf module declares:

```lean
theorem finiteFree_homComplex_qc_cohomology
    (X : Scheme.{u}) (U : X.Opens)
    (E I : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hEbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i))
    (hEfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hI : ∀ i : ℤ, (I.homology i).IsQuasicoherent) (n : ℤ) :
    ((homComplex (R := X.toRingedSpace.sheaf.over U) E I).homology n).IsQuasicoherent
```

## New

The identical declaration and signature above remain in
WeilConjectures.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology, unchanged.
Withdraw the Sheaf copy through deleted.txt and repoint only the node's Lean attachment
(module and file, with an explanatory note) to the source twin. The DAG statement,
proof, proof dependencies, and unit route remain unchanged. No source file is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology | T2 | Duplicate module withdrawn. |
| WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartQCCohomology | unmodified | Already imports the source twin and applies the identical theorem. |

There are no current Lean imports of the Sheaf path, including in quarantine.
The sole DAG parent is new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology;
its step 3 and proof_deps retain this node and its declaration. Its Lean module is the
source consumer above, so no parent dependency change or consumer adaptation is needed.
The unit sk-thm-picard-duality has empty realized lists and is unchanged.

## Status

landed 20261020T154053-L-3041857 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology)
