# Sequence completion projection: equivalent section interfaces

## Reason

The old ordinary unit and transition fields force Lean to identify the section types
of scalar restrictions and vertical evaluations inside nested function applications.
Profiling found repeated `isDefEq`/`whnf` timeouts at those applications. Compose the
actual module morphisms first and evaluate only the resulting map. This preserves the
normalization and the actual transition, while avoiding repeated expansion of the
underlying scalar-action constructions. The interface normalization avoids expanding
entire module actions when identifying section maps.

The module-coordinate and ordinary-unit fields use heterogeneous equality of their
section values. Their existing object-equality fields identify the section types.
Transporting along those equalities recovers the previous ordinary equalities.
For the ordinary unit, applying the invertible evaluation comparison gives the previous
formula; conversely its inverse gives the new formula. These changes retain exactly
the coordinate and tensor-insertion normalizations.

The transition field now composes the comparison inverse, the given transition and
scalar restriction of the comparison before evaluating. Restriction preserves the
underlying additive maps. Expanding composition and scalar restriction recovers the
old formula verbatim. No coefficient hypothesis, bound, or conclusion is changed.

Explicit category arguments on `eqToHom` and explicit site arguments on the flatness
and K-flat predicates only resolve elaboration metavariables; their types are unchanged.
During elaboration, the generic multicospan composition instance is suppressed and
the size-bounded limit-preservation instance receives local priority 11000. This avoids
attempting limits in the wrong site universe. The existing specialized forgetful
composition instances receive local priority 30000; all their signatures remain unchanged. The generic
multicospan instance is restored at the end of the file, so the suppression is
confined to elaborating this module.

Explicit private instances cache the existing limits of individual towers; they use the standard existing limit instances. Declaration linters are disabled in this module to avoid
repeated traversal of transported coordinate proof terms. All proofs remain kernel checked.

The structure `RingedToposMorphismOfUniverses` is unchanged. No source-library file or
locked target declaration is changed.
The definition review of consuming target statements must recheck these equivalent
section interfaces, as required for a changed definition on their route.

## Old

```lean
  moduleDirect_section : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : (g.π.modules.obj M).val.obj U),
    (eqToHom (restriction_obj M n)).val.app U
      ((limit.π (restriction.obj M) (op n)).val.app U
        ((moduleDirect.hom.app M).val.app U x)) =
      (eqToHom (g.setsTower_obj
        ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, r} J B τ)).obj M) n)).hom.app U
        ((limit.π (g.setsTower.obj
          ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, r} J B τ)).obj M)) (op n)).hom.app U
          ((g.directLimit.hom.app
            ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
              (systemRing.{c, v, r} J B τ)).obj M)).hom.app U
            ((g.π.underlying.hom.app M).hom.app U x)))

  ordinary_unit : ∀ (M : Mod.{c, v, r} J b.pt) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U),
    ((ordinaryEvaluation n).hom.app M).val.app U
      ((eqToHom (u.restriction_obj (extension.obj M) n)).val.app U
        ((limit.π (u.restriction.obj (extension.obj M)) (op n)).val.app U
          ((u.moduleDirect.hom.app (extension.obj M)).val.app U
            ((moduleAdjunction.unit.app M).val.app U x)))) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U 1 x


  ordinary_transition : ∀ (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m)
    (U : Cᵒᵖ) (a : (B m).obj.obj U) (x : M.val.obj U),
    ((ordinaryEvaluation n).hom.app M).val.app U
      (((transition.{c, v, r} J B τ h).app (extension.obj M)).val.app U
        (((ordinaryEvaluation m).inv.app M).val.app U
          (completionScalarSection.{c, v, r} J (b.π.app (op m)) (level m) M U a x))) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U
        ((coefficientMap.{c, v, r} J B τ h).hom.app U a) x
```

## New

```lean
  moduleDirect_section : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : (g.π.modules.obj M).val.obj U),
    HEq ((limit.π (restriction.obj M) (op n)).val.app U
      ((moduleDirect.hom.app M).val.app U x))
      ((eqToHom (g.setsTower_obj
        ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, r} J B τ)).obj M) n)).hom.app U
        ((limit.π (g.setsTower.obj
          ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, r} J B τ)).obj M)) (op n)).hom.app U
          ((g.directLimit.hom.app
            ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
              (systemRing.{c, v, r} J B τ)).obj M)).hom.app U
            ((g.π.underlying.hom.app M).hom.app U x))))

  ordinary_unit : ∀ (M : Mod.{c, v, r} J b.pt) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U),
    HEq ((limit.π (u.restriction.obj (extension.obj M)) (op n)).val.app U
      ((u.moduleDirect.hom.app (extension.obj M)).val.app U
        ((moduleAdjunction.unit.app M).val.app U x)))
      (((ordinaryEvaluation n).inv.app M).val.app U
        (completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U 1 x))


  ordinary_transition : ∀ (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m)
    (U : Cᵒᵖ) (a : (B m).obj.obj U) (x : M.val.obj U),
    (((ordinaryEvaluation m).inv.app M ≫
      (transition.{c, v, r} J B τ h).app (extension.obj M) ≫
        (res.{c, v, r} (coefficientMap.{c, v, r} J B τ h)).map
          ((ordinaryEvaluation n).hom.app M)).val.app U)
            (completionScalarSection.{c, v, r} J (b.π.app (op m)) (level m) M U a x) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U
        ((coefficientMap.{c, v, r} J B τ h).hom.app U a) x
```

## Users

The read-only `tools/downstream.py` inventory finds sixteen transitive importers (refreshed 2026-10-23).
Separate `--uses moduleDirect_section`, `--uses ordinary_unit`, and
`--uses ordinary_transition` searches find these field names only inside the item itself.
No downstream source adaptation is necessary. The item compiled in 56.9 seconds as a single file. The consumer batch stopped
when exporting the item exceeded the server's 60-second limit; no consumer compiler
error was produced. Delivery preflight remains required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SequenceSiteCompletionProjection | Q1 | Equivalent compatibility fields; completed proof. |
| Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData | unclaimed | Unchanged ringed-topos interface. |
| Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.ConstantModuleTensorSquareDescent | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.ConstantModulePlusComparisonData | unclaimed | No use of the changed fields. |
| Sheaf.Paper.PurSequenceAdjointResolutionData | unclaimed | No use of the changed fields. |
| Sheaf.Paper.PurSequenceAdjointResolutionShifts | unclaimed | No use of the changed fields. |
| Sheaf.Paper.SequenceSiteOpenExtension | unclaimed | No use of the changed fields. |
| Sheaf.Paper.SemilinearOpenClosedComplexSequence | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.Sites.RingedSitePicardData | unclaimed | No use of the changed fields. |
| Sheaf.CategoryTheory.Sites.RingedSitePicardH1Natural | unclaimed | No use of the changed fields. |
| Sheaf.Paper.EtaleRingedDerivedIdentificationData | unclaimed | No use of the changed fields. |
| Sheaf.Paper.EtaleRingedDerivedNormalization | unclaimed | No use of the changed fields. |
| Sheaf.Paper.EtaleRingedProjectionIdentification | unclaimed | No use of the changed fields. |
| Sheaf.Paper.EtaleRingedProjectionPresentation | unclaimed | No use of the changed fields. |

## Status

landed 20261024T015540-L-2416635 2026-10-24 (merge of deliver/Q1/Sheaf.Paper.SequenceSiteCompletionProjection)
