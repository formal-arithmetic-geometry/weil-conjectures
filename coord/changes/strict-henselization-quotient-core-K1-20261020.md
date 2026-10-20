# Algebra.strictHenselization_surjective_quotient_core

## Reason

Restore the quarantined stage-3 repair listed in coord/rework.tsv. Its original proof
calls the retired quotientBaseChange_obj_iso, whereas the adopted upstream API is
quotientBaseChangeObjIso and requires an explicitly compatible B-action.

## Old

The theorem signature below is taken verbatim from the quarantined module:

```lean
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (_hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

The old proof obtains the B-action and isomorphism from quotientBaseChange_obj_iso.

## New

The signature is identical:

```lean
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (_hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

The proof constructs the B-action on C/IC by RingHom.liftOfSurjective. The kernel
inclusion follows from Ideal.le_comap_map, and liftOfSurjective_comp_apply proves its
composition with pi is A -> C/IC. Apply the proved upstream quotientBaseChangeObjIso
with this equation and compose with the existing colimit vertex isomorphism.
No definition, public import, declaration visibility, or mathematical statement changes.

## Users

The read-only downstream.py query reports unknown module because the item is quarantined.
Scanning both lean/ and quarantine/ finds the one direct importer and theorem consumer
below. The rework table also records the transitive quarantine dependents. The direct
consumer was copied unchanged temporarily into the sandbox, compiled against the repaired
core, and removed from the delivery. It needs no adaptation. No target definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore | K1 | Restored, proof repaired. |
| Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient | unclaimed in shared snapshot | Archived original compiles unchanged against the repair. |

## Status

landed 20261020T145521-L-2406039 2026-10-20 (merge of deliver/K1/Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore)
