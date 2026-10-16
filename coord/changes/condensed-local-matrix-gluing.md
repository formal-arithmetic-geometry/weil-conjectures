# Local matrix descent and gluing decomposition

## Reason

Make the finite presentation argument concrete in Lean while isolating the
remaining overlap descent and gluing problem. Avoid an unnecessary comparison
of the inverse-image coefficients with the standard coefficients on the stratum.
The original public theorem signature and every definition are unchanged. The second
reading reuses the existing `Mod.regularExtensionIso` and its naturality in the matrix
proof, and records the existing `sectionModuleEquivalence` in the gluing plan. The repair
exposes three already-proved private transport lemmas in the unclaimed module
`Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`; see the companion
change record `condensed-fp-shared-api.md`.

## Old

The existing theorem had this signature and one unproved body:

```lean
theorem exists_lfp_finiteCoefficient_model_on_immersion
    (T X : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (f : X ⟶ T) [IsImmersion f] (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      IsLocallyFinitelyPresented
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅ M)
```

## New

The existing theorem has exactly the same signature and a complete proof from
the following two new declarations. The first is proved; the second is the only
new named theorem left with `sorry`.

```lean
theorem exists_finiteCoefficient_gluing_of_local_models
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))),
      (∀ i, Nonempty (
        ((upperStar Ab.{u + 1} (U.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj P ≅
        (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i))) ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj P ≅ M)
```

```lean
theorem exists_common_finiteCoefficient_presentation_matrices
    (T X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X),
      Finite U.I₀ ∧ (∀ i, IsAffine (U.X i)) ∧
      ∃ (n m : U.I₀ → ℕ)
        (d : ∀ i, Mod.finiteFree
          ((upperStar Ab.{u + 1} (U.f i)).obj
            ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (m i) ⟶
          Mod.finiteFree
          ((upperStar Ab.{u + 1} (U.f i)).obj
            ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (n i)),
        ∀ i, Nonempty ((Mod.extendScalars
          ((upperStar Ab.{u + 1} (U.f i)).map
            ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
              (cokernel (d i)) ≅
          ((upperStar Ab.{u + 1} (U.f i)).mapMod
            ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)
```

## Users

| Module | Holder | Adaptation |
| --- | --- | --- |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | Proof and proof-only imports; signature unchanged. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | A4 (new) | New proved local-matrix theorem. |
| Sheaf.Paper.CondensedLocalModelGluing | A4 (new) | New local-model gluing statement. |

Existing importers see the same original signature and public imports. The unclaimed shared scalar-extension module additionally exposes its existing
transport helpers. There are no adaptations of modules held by other groups.

## Status

landed 20261016T073458-L-1079815 2026-10-16 (merge of deliver/A4/Sheaf.Paper.CondensedLfpCoefficientModel)
