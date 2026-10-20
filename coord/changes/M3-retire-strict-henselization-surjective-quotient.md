# Algebra.IsStrictHenselization.surjective_quotient

## Reason

Complete the human-authorized retirement in coord/retire-items.tsv and
coord/changes/retire-sheaf-twins-20261020.md. The assigned Sheaf module contains zero
holes and duplicates the upstream theorem name with an older existential interface.
The upstream theorem requires a chosen separable closure and the induced quotient action,
so a plain import replacement does not suffice for its localized-divisor caller.

## Old

The retiring Sheaf declaration:

```lean
theorem IsStrictHenselization.surjective_quotient
    (A K C B : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField B) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField B) L)
      (_ : Algebra B L) (_ : IsScalarTower B (IsLocalRing.ResidueField B) L)
      (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

## New

Withdraw lean/Sheaf/RingTheory/StrictHenselizationSurjectiveQuotient.lean using deleted.txt.
Use the existing upstream declaration, unchanged:

```lean
theorem IsStrictHenselization.surjective_quotient
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) (I : Ideal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))]
    (hcomp : (algebraMap B (C ⧸ I.map (algebraMap A C))).comp π =
      (Ideal.Quotient.mk _).comp (algebraMap A C)) :
    IsStrictHenselization B L (C ⧸ I.map (algebraMap A C))
```

The original node statement remains existential. Choose the canonical SeparableClosure
of ResidueField B, with the B-action composed with the residue map. For Q = C/IC,
Ideal.le_comap_map shows that A -> Q kills ker(pi) = I. RingHom.liftOfSurjective
constructs beta : B -> Q; liftOfSurjective_comp_apply proves exactly hcomp. Apply the
upstream theorem and package these structures. The complete original signature was
compiled with this derivation, and #print axioms reports only propext, Classical.choice,
and Quot.sound. Its complete proof is recorded in the report.

The localized-divisor consumer keeps its public signature and explicitly performs the
same construction for B = (R/(f))_p. Its existing ideal-extension equality transports the
constructed action and proof from C/IC to C/(b(f)). The coordinate-stratum consumer only
changes its proof import. No upstream source, target statement, or definition changes.

## Users

The read-only tools/downstream.py query lists exactly the two direct consumers below;
a scan of lean/ and quarantine/ finds the same two, with archival copies in quarantine/.
Both live consumers are adapted and server-compiled in this delivery. The archival copies
are preserved. Neither consumer is claimed in the preparation snapshot. The complete
project import closures were checked: no new duplicate Sheaf/upstream pair is introduced.
The coordinate consumer already has the unrelated StrictHenselizationStructuralMap pair,
whose claimed repair is outside this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient | M3 assignment | Withdraw duplicate; attach its node to the upstream theorem. |
| Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient | unclaimed | Migrate import and explicitly construct the structures required by upstream; signature identical. |
| Sheaf.TraceFormula.CoordinateMaximalBranchStratum | unclaimed | Replace the proof import; theorem and existing hole unchanged. |

The DAG attachment for lem-sbc-strict-henselization-surjective-quotient points to the
upstream theorem, with its verbatim signature and a note explaining the existential
construction. Its proof dependencies now reflect the upstream final-cocone proof.
The localized-divisor node's final step records the explicit compatible-action adaptation.
Other DAG parents, including unfinished and quarantined parents, keep using the same
mathematical quotient theorem through its corrected upstream attachment. No unit route
is bypassed; sk-prop-input-spreading has no realized entry for this auxiliary node.
No target definition changes meaning.

## Status

landed 20261020T162546-L-3622366 2026-10-20 (merge of deliver/M3/Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient)
