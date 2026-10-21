# proEtaleUnitLerayDirectImageIso

## Reason

The equality-elimination implementation forces Lean to unfold the ring-sheaf coefficient
comparison when proving its action on sections. The worker repeatedly obtained 60-second
file timeouts and 200000-heartbeat `whnf` timeouts in the assigned identity/composition proof.
Use Mathlib's `SheafOfModules.pushforwardCongr` for the same equality of scalar maps. Its
hom and inverse have proved, definitional identity formulas on sections. The declaration's
signature and every other existing definition remain unchanged. This is an implementation
repair, not a change of the coefficient map or the selected adjunction.

For equal scalar maps, equality induction identifies the old transported reflexive
isomorphism with `pushforwardCongr`: after substituting the equality, both have identity
components, and natural-transformation extensionality proves equality. Thus the comparison
and all target meanings are preserved. The repair is in the project's Sheaf tree.

## Old

```lean
noncomputable def proEtaleUnitLerayDirectImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ≅ proEtaleConstantModuleDirectImage h A := by
  have he : proEtaleRingDirectImageMap h (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison h A) =
        proEtaleCoefficientDirectImageMap h A := by
    change (proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap h A)) = _
    exact Equiv.apply_symm_apply _ _
  unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
  rw [he]
  exact Iso.refl _
```

## New

```lean
noncomputable def proEtaleUnitLerayDirectImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ≅ proEtaleConstantModuleDirectImage h A := by
  have he : proEtaleRingDirectImageMap h (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison h A) =
        proEtaleCoefficientDirectImageMap h A := by
    change (proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap h A)) = _
    exact Equiv.apply_symm_apply _ _
  exact SheafOfModules.pushforwardCongr
    (congrArg (fun (a : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) ↦
      (show ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A)) ⟶
        ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing X A)) from
        ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩)) he)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula --uses
proEtaleUnitLerayDirectImageIso` lists the following modules. The source claim directory has
no claim for the first module; V5 holds the assigned second module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula | unclaimed | Implement the same comparison with `pushforwardCongr`; all declarations and proof helpers retain their signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation | V5 | Use Mathlib's proved hom/inverse section formulas in the composition and identity proofs. |

Both modules are compiled together in dependency order. No consumer signature changes.
The repaired helper is definitionally normalized on sections, including the zero ring and
the empty scheme; the equality of scalar maps and the pushforward construction require
no nonzero or nonempty hypothesis.

## Status

landed 20261021T152407-L-1927624 2026-10-21 (merge of deliver/V5/Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation)
