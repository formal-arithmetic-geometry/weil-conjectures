# AlgebraicGeometry.ProEtale.exists_finiteCoefficient_localization_triangle

## Reason

Restore the proved module preserved by its current coord/rework.tsv entry. The live
source path is absent after the reverted cluster restore, but its Lean attachment and
its mathematical consumers remain. Preserve the archived theorem and dependencies.
The restored proof separates the dependent recollement instance witness before unpacking
its remaining conjunctions. No statement, definition, or target meaning changes.

## Old

The live file lean/Sheaf/Paper/CondensedFiniteCoefficientLocalization.lean is absent.
Its authoritative source is quarantine/Sheaf/Paper/CondensedFiniteCoefficientLocalization.lean.
The archived public signature is:

```lean
theorem exists_finiteCoefficient_localization_triangle
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Z : Scheme.{u}} (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (padicSubfieldRingObj U ℓ EU))
    (EZ : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicSubfieldRingObj Z ℓ EZ))
    (eU : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) j).obj N))
    (eZ : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ EZ)).obj PZ ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) k).obj N)) :
    ∃ D : Pretriangulated.Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))),
      D ∈ distTriang _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ EU)).obj
          ((CondensedRing.openImmersionLowerShriek
            (Profinite.continuousMapRingObj.{u} EU) j).obj PU)) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ EZ)).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} EZ) k).obj PZ)) ≅
          D.obj₃) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj D.obj₂ ≅ N)
```

## New

Restore the archived module at its original Lean path, with the identical public signature
above and the same localization and scalar-comparison proof. The dependent witness is now
unpacked from a named hypothesis, rather than generalizing the complete recollement term.
No new public declaration, axiom, proof hole, or definition is introduced.
The quarantine file and DAG attachment are preserved.

Validation compiled the unchanged recollement dependency followed by this item, each
within the single-file limit (42.8 and 9.9 seconds). This avoided a kernel argument
mismatch in the published recollement artifact involving Mod.monoidalClosed. The
dependency source is not modified or included in the delivery. All public signatures
and imports are identical to the archive, including the import-all access to its existing
private support helpers. The only source changes relative to the archive are the two
witness-elimination proof fragments.

## Users

The source-only tools/downstream.py scan with --allow-missing finds no active importers.
A scan of both library roots and both quarantine roots finds the archived direct consumer
below; its theorem application uses exactly the unchanged public signature. It requires
no adaptation. The parent DAG still cites this item, so withdrawal would be incorrect.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | E3 | Restore source and repair witness elimination. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unqueried; unchanged | Archived consumer; same theorem application and interface. |

## Status

landed 20261021T021914-L-2791593 2026-10-21 (merge of deliver/E3/Sheaf.Paper.CondensedFiniteCoefficientLocalization)
