# derivedPullback_tensor_unit_kFlat

## Reason

Restore the assigned zero-hole module from quarantine after the upstream sync.
The original compile fails at its import of `Sheaf.AlgebraicGeometry.DerivedPullback`:
`AlgebraicGeometry.derivedPullback` is already present from the adopted source module.
The adopted `WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` already
contains the complete unit-law proof and the same public declaration name. Re-export
it through the former Sheaf path instead of introducing another implementation.

The only difference in its theorem signature is the spelling of K-flatness:
`CochainComplex.IsKFlatTensor` replaces `CochainComplex.IsAcyclicTensorKFlat`.
Both are defined by the same acyclic-total-tensor condition using the same sheaf
monoidal category. No hypothesis, conclusion, universe, or unit comparison changes.
No adopted source file or target statement is edited.

## Old

The quarantined module public-imported
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitCounit`, privately
imported `Sheaf.AlgebraicGeometry.DerivedPullback`,
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`,
`WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`, and
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization`,
and contained a complete proof with this signature:

```lean
theorem derivedPullback_tensor_unit_kFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P →
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))]
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    : (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (λ_ ((derivedPullback g).obj A)).hom =
           η.hom ▷ (derivedPullback g).obj A ≫
             ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
             (derivedPullback g).map (λ_ A).hom) ∧
      (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (ρ_ ((derivedPullback g).obj A)).hom =
           (derivedPullback g).obj A ◁ η.hom ≫
             ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
             (derivedPullback g).map (ρ_ A).hom)
```

## New

The restored module has the public import

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat
```

with a module docstring and `@[expose] public section`. The source theorem it
provides is:

```lean
theorem derivedPullback_tensor_unit_kFlat {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    [IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))))]
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    : (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (λ_ ((derivedPullback g).obj A)).hom =
           η.hom ▷ (derivedPullback g).obj A ≫
             ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
             (derivedPullback g).map (λ_ A).hom) ∧
      (let η := derivedPullback_tensorUnitIso g F mF ε
       let A := DerivedCategory.Q.obj P
       (ρ_ ((derivedPullback g).obj A)).hom =
           (derivedPullback g).obj A ◁ η.hom ≫
             ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
             (derivedPullback g).map (ρ_ A).hom)
```

The node's Lean attachment retains the same declaration and now names its
adopted upstream module and exact signature. Its statement, statement dependencies,
proof steps, proof dependencies, unit, and route are retained verbatim.
The quarantine archive is preserved; this is restoration, not withdrawal.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat | Q1 | Restored as a public compatibility import; no local theorem duplication. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit | unclaimed | Quarantined direct importer; its two applications use the same theorem name and argument order. Both components of the same conjunction remain available. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit | unclaimed | Already imports and uses the canonical source theorem; unchanged. |

A full source scan of `lean/` and `quarantine/` found no further direct importers
or theorem users. `tools/downstream.py` cannot inspect this missing live module
and reports `unknown module(s)`; the source scan includes the preserved archive.
The sole DAG parent is `lem-pc-derived-pullback-tensor-unit`; its dependency remains.
The complete old theorem type was also kernel-checked in a separate consumer
probe using its explicit original acyclic-tensor condition, and the canonical
theorem applies directly. `Iff.rfl` checks equality of the two predicate bodies
on schemes. The probe compiles in 10.3 seconds; the compatibility import compiles
in 1.5 seconds. The source theorem's axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. No forced consumer adaptation is required. The quarantined parent has its own
outstanding sync repair, and this packet does not claim to repair it.

## Status

landed 20261020T211815-L-3504234 2026-10-20 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat)
