# AlgebraicGeometry.Scheme.finiteModel_derivedRepresentative_transport

## Reason

The transport lemma and two lower ordinary-model comparisons omitted K-flatness. For the map ℤ → ℤ/2 and P = (ℤ/2)[0], derived scalar extension has a nonzero Tor_1 term that ordinary scalar extension omits. The corrected statements compute ordinary scalar extension only on K-flat inputs, as required in Stacks 06YY and 0D6D. The general parent theorem keeps its exact signature: its proof chooses a K-flat representative, applies both corrected comparisons there, then transports along exact constant realization and exact coefficient restriction. All three related modules were unclaimed on the current server when inspected.

No definition, target signature, source-library declaration or public import is removed. Two proved helpers are made available in the item module: exact constant realization of derived isomorphisms and existence of same-universe K-flat representatives. The free-forgetful counit proves the required functorial flat-resolution instance locally; the representative helper applies the existing source theorem CochainComplex.exists_quasiIso_flat_kFlat. The public K-flat import is required by the three corrected signatures.

## Old

FiniteModelCoefficientTransport

```lean
theorem finiteModel_derivedRepresentative_transport
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D
            (((ModuleCat.extendScalars (ρ.toRingHom.comp q)).mapHomologicalComplex
              (.up ℤ)).obj P)) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D K))
```

FiniteModelConstantScalarExtensionCore

```lean
theorem finiteModel_constantScalarExtension_core
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

FiniteModelConstantScalarExtensionLiftComparison

```lean
theorem finiteModel_constantScalarExtension_liftComparison
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P))) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

finiteModel_constantComplex_mapIso was private; finiteModel_exists_kFlat_representative did not exist.

## New

FiniteModelCoefficientTransport

```lean
theorem finiteModel_derivedRepresentative_transport
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat P)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D
            (((ModuleCat.extendScalars (ρ.toRingHom.comp q)).mapHomologicalComplex
              (.up ℤ)).obj P)) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D K))
```

FiniteModelConstantScalarExtensionCore

```lean
theorem finiteModel_constantScalarExtension_core
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat P) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

FiniteModelConstantScalarExtensionLiftComparison

```lean
theorem finiteModel_constantScalarExtension_liftComparison
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat P) :
    Nonempty
      ((ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P))) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

```lean
theorem finiteModel_constantComplex_mapIso
    (X : Scheme.{t}) {D : Type t} [CommRing D]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    {A B : CochainComplex (ModuleCat.{t} D) ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) :
    Nonempty
      ((@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D A) ≅
        (@DerivedCategory.Q (SheafOfModules.{t + 1} (adicModuleRing X D)) _ _).obj
          (finiteModelConstantComplex X D B))
```

```lean
theorem finiteModel_exists_kFlat_representative (B : Type t) [CommRing B]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    ∃ R : CochainComplex (ModuleCat.{t} B) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat R ∧
        Nonempty (DerivedCategory.Q.obj R ≅ DerivedCategory.Q.obj P)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteModelDerivedScalarComparison | unclaimed | Its exact statement is preserved. Choose a K-flat resolution R of P, apply the corrected core and transport to R, then map the original resolution isomorphism through L, exact restriction and exact constant realization. |
| Sheaf.Paper.FiniteModelConstantScalarExtensionCore | unclaimed | Add hP to the signature and pass it to the corrected lift comparison. |
| Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison | unclaimed | Correct its existing holed theorem by adding K-flatness, and give the complete resolution-based proof plan in its docstring. |
| Sheaf.Paper.FiniteModelCoefficientTransport | K1 | Prove corrected transport and the two general helpers; no sorry remains. |

These are all textual callers of the changed declarations and all direct importers of the changed interfaces. The parent is the sole direct importer of transport and core; core is the sole direct importer of the lift comparison. Indirect users continue to use the identical arbitrary-complex parent signature. The helper newly exposed from a private theorem has no pre-existing caller. All four files compile one at a time in dependency order. No module held by another group is edited.

## Status

landed 20261028T034822-L-3552048 2026-10-28 (merge of deliver/K1/Sheaf.Paper.FiniteModelCoefficientTransport)
