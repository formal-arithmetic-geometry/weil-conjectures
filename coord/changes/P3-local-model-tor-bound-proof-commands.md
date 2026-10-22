# AlgebraicGeometry.ProEtale.localModel_torBound_descent

## Reason

Preflight classifies the added local attribute command as an interface change and requires
this record. The command keeps pullback and monoidal constructions folded during proof
elaboration. Three proved private theorem helpers and one explicit canonical isomorphism construction
keep the local tensor calculation and cover descent
abstract in the same module. All public signatures and public imports are unchanged; no public
instance, definition, notation or attribute is changed. All additional imports are ordinary private proof imports; descent uses the public
`condensed_cover_restriction_conservative` theorem. No source-library module is modified.

## Old

```lean
theorem localModel_torBound_descent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X]
    (S : Scheme.{u})
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (n : ℕ) (V : Fin n → S.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈
      Scheme.proetalePrecoverage S)
    (r s : ℤ) (hrs : r ≤ s)
    (L : ∀ i : Fin n, CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
        (condensedRingObj Γ.X (V i).left)) ℤ)
    (hbound : ∀ (i : Fin n) (q : ℤ), q < r ∨ s < q → IsZero ((L i).X q))
    (hflat : ∀ (i : Fin n) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (V i).left)
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left))
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left)).functor.obj
          ((L i).X q)))
    (model : ∀ i : Fin n,
      (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj Q ≅
        DerivedCategory.Q.obj (L i)) :
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n), Nonempty
        ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
          ((CochainComplex.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _)))) ∧
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (q : ℤ), q < r ∨ s < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)) r s Q
```

The theorem body was `by sorry`, with no local reducibility command in this namespace.

## New

```lean
theorem localModel_torBound_descent
    (Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X]
    (S : Scheme.{u})
    (Q : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)))
    (n : ℕ) (V : Fin n → S.ProEt)
    (hcover : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈
      Scheme.proetalePrecoverage S)
    (r s : ℤ) (hrs : r ≤ s)
    (L : ∀ i : Fin n, CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology (V i).left) Ab.{u + 1})
        (condensedRingObj Γ.X (V i).left)) ℤ)
    (hbound : ∀ (i : Fin n) (q : ℤ), q < r ∨ s < q → IsZero ((L i).X q))
    (hflat : ∀ (i : Fin n) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (V i).left)
      (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left))
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology (V i).left) (condensedRingObj Γ.X (V i).left)).functor.obj
          ((L i).X q)))
    (model : ∀ i : Fin n,
      (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj Q ≅
        DerivedCategory.Q.obj (L i)) :
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (i : Fin n), Nonempty
        ((CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i)
          ((CochainComplex.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _)))) ∧
    (∀ (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))
      (q : ℤ), q < r ∨ s < q → IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S)) r s Q
```

The theorem has a complete proof and the following local elaboration command:

```lean
attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.instMonoidalCategory_weilConjectures
  CategoryTheory.Mod.monoidalClosed DerivedCategory.monoidalClosed
```

The private theorem helpers are `flatTensorCalculation`, `moduleZeroDescent`, and
`coverHomologyZero`. They are proved, add no holes, and are absent from public signatures.
The private definition `transportTensorIso` explicitly composes the supplied isomorphisms;
it has no postponed proof or chosen existence witness.
The supplied interval-order hypothesis remains in the statement; the proof works without
needing to strengthen it. A theorem-scoped `set_option linter.unusedVariables false in`
preserves that original unused binder without adding a redundant reference to the proof. The theorem's meaning is unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.LocalModelTorBoundDescent` reports zero current Lean
importers. Its unfinished DAG parent still needs this theorem, so the module is retained.
No consumer requires adaptation and no target definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocalModelTorBoundDescent | P3 | Complete proof; identical public interface. |

## Status

landed 20261022T011912-L-3230758 2026-10-22 (merge of deliver/P3/Sheaf.Paper.LocalModelTorBoundDescent)
