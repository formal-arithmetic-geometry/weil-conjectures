# AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_derived_scalar_basis

## Reason

The original full theorem statement checks without output in 27.2 seconds, but exporting
it repeatedly exceeds the unchanged 60-second limit. The same effect occurred on the lower
unit theorem: naming its scalar-unit leg reduced exporting compilation from timeout to
19.2 seconds. A previous project repair (`E4-compact-derived-comparison-signatures.md`)
identifies the premise-index extension's repeated inspection of partially applied derived
functors. Name the original scalar-basis proposition as an exposed ordinary `Prop` definition;
its body is exactly the former conclusion. This avoids repeating that inspection when
indexing the theorem. No binder, universe, hypothesis or conclusion changes mathematically.
The same theorem name and arguments remain usable by its one direct caller. No Challenge
target is changed. There is no proof or data placeholder in the proposition definition.

## Old

In the original variable context `(ℓ : ℕ) [Fact ℓ.Prime]
(E : PadicAlgCl.FiniteIntermediateField ℓ)` and universe `u`:

```lean
theorem condensedQbar_derived_scalar_basis :
    ∃ (I : Type (u + 1))
      (τ : ∀ Z : Scheme.{u}, I → CatCenter (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)))),
      (∀ (Z : Scheme.{u}) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
        [HasCoproduct (fun _ : I ↦ M)],
        IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app M ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).mapDerivedCategory.map
              ((τ Z i).app ((Mod.extendScalars (coefficientMap
                (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).leftDerivedFunctor.obj M)))) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I)
        (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))),
        R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map ((τ X i).app M) =
          (τ Y i).app (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M))
```

## New

In exactly the same variable context:

```lean
def CondensedQbarDerivedScalarBasis : Prop :=
    ∃ (I : Type (u + 1))
      (τ : ∀ Z : Scheme.{u}, I → CatCenter (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)))),
      (∀ (Z : Scheme.{u}) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
        [HasCoproduct (fun _ : I ↦ M)],
        IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app M ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).mapDerivedCategory.map
              ((τ Z i).app ((Mod.extendScalars (coefficientMap
                (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).leftDerivedFunctor.obj M)))) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I)
        (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))),
        R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map ((τ X i).app M) =
          (τ Y i).app (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M))

theorem condensedQbar_derived_scalar_basis :
    CondensedQbarDerivedScalarBasis ℓ E
```

Unfolding `CondensedQbarDerivedScalarBasis` gives the old conclusion literally. A scratch
consumer states the old full signature and applies the new theorem directly; it compiled
in 22.2 seconds, verifying this definitional identity in Lean. The existing source consumer uses `obtain` on the exposed
proposition without changing its proof or public statement.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | A3 | Name the identical proposition to make exporting compilation tractable. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Only external theorem caller; its existing elimination works unchanged. Its separate shared-helper edits are documented in A3-qbar-shared-scalar-helpers.md. |

All transitive downstream modules of the source consumer are listed in the shared-helper
change record. They retain the same public mathematical statements and need no edits.

## Status

landed 20261016T173551-L-1931163 2026-10-16 (merge of deliver/A3/Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis)
