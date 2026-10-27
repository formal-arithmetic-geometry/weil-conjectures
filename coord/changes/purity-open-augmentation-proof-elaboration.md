# AlgebraicGeometry.ProEtale.supportComparisonSource

## Reason

The shifted single-functor wrapper `CochainComplex.singleFunctor` makes repeated
bounded-complex and comparison conversions expensive. The original common-injectives
module exceeded 60 seconds in the unchanged baseline check. Replacing that wrapper
by its underlying `HomologicalComplex.single` compiled the common module in 37.3 seconds
and the complete open-restriction proof in 25.3 seconds. Mathlib explicitly documents
these functors as definitionally equal in `HomotopyCategory/SingleFunctors.lean`.
The new construction has exactly the same terms, differentials and bound proof.
Final server validation compiled the two delivered modules in 3.1 and 31.6 seconds;
the unchanged dependent section-model module also compiled in 43.9 seconds.

The adapted module is unclaimed. Its existing theorem proofs, signatures, attributes
and public imports are unchanged. This definition is in `Sheaf/`, not in the adopted
`WeilConjectures/` tree. No source-library file changes.

The item also gains the complete proof and the proved private helper
`supportComparisonOpenUnitForward`. Its existing theorem statement and the two open
source/resolution constructions are unchanged. Proof imports use the existing adopted
localization-restriction injective instance directly. The unused Grothendieck-module
and enough-injectives proof imports are removed. Local irreducibility attributes
keep the canonical comparison constructions closed during elaboration. A scoped
heartbeat setting handles the dependent normalization clauses without raising the
60-second compile limit.

## Old

```lean
noncomputable def supportComparisonSource
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj F, ⟨0, inferInstance⟩⟩
```

## New

```lean
noncomputable def supportComparisonSource
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    CochainComplex.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ⟨(HomologicalComplex.single _ (.up ℤ) 0).obj F, ⟨0, inferInstance⟩⟩
```

## Users

The complete output of `tools/downstream.py Sheaf.Paper.PuritySupportCommonInjectives
--uses supportComparisonSource` consists of the following three modules. The item
itself has no Lean importers. The consumer is checked from its unchanged source in
a scratch packet against the repaired dependency. The definitionally equal body
changes neither any target statement nor its mathematical meaning. If the definition's
indirect use by a target triggers statement review, the equality here is the entire
scope of that review; no hypothesis or conclusion changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PuritySupportCommonInjectives | unclaimed | Definitionally equal single-complex construction; proofs unchanged. |
| Sheaf.Paper.PurityOpenRestrictionAugmentation | S2 | Complete proof; original public statements preserved. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | No changes required; original consumer checked against the repair. |

## Status

landed 20261024T020158-L-2565845 2026-10-24 (merge of deliver/S2/Sheaf.Paper.PurityOpenRestrictionAugmentation)
