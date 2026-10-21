# AlgebraicGeometry.derivedPullback_tensor_unit

## Reason

Restore the assigned zero-hole module from quarantine after the upstream sync.
The archived module no longer compiles: its public import
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` is withdrawn, so
`Scheme` and `HasDerivedCategory` are not publicly available at the theorem's
signature. The adopted source module already contains the complete theorem with
the same name, hypotheses, conclusion, universes, private transport helpers, and
proof route. Restore the Sheaf path as a public compatibility import of that
module, preserving the archive and its dependency graph.

The only textual difference in the theorem signature is the rename from
`CochainComplex.IsAcyclicTensorKFlat` to `CochainComplex.IsKFlatTensor`. Both
predicates have identical bodies: for every acyclic N, Tot(N tensor P) is acyclic,
using the same sheaf monoidal structure. There is no mathematical statement change.
No adopted source file, target, definition, or unit route is edited.

## Old

The quarantined module's header and imports were:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat
import Sheaf.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

```

It contained two proved private transport lemmas and a complete proof of:

```lean
theorem derivedPullback_tensor_unit {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    : ∃ η : 𝟙_ (schemeDerivedCategory T) ≅
        (derivedPullback g).obj (𝟙_ (schemeDerivedCategory X)),
        (∀ A : schemeDerivedCategory X,
          (λ_ ((derivedPullback g).obj A)).hom =
            η.hom ▷ (derivedPullback g).obj A ≫
              ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
              (derivedPullback g).map (λ_ A).hom) ∧
        (∀ A : schemeDerivedCategory X,
          (ρ_ ((derivedPullback g).obj A)).hom =
            (derivedPullback g).obj A ◁ η.hom ≫
              ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
              (derivedPullback g).map (ρ_ A).hom)
```

## New

The restored module is:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit

/-! # Unit laws for derived pullback tensor comparisons

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.derivedPullback_tensor_unit`. The source theorem supplies the
unit isomorphism and both unit laws, without assuming associativity. Its
`CochainComplex.IsKFlatTensor` is the acyclic-tensor predicate formerly named
`CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit).
-/

@[expose] public section
```

The node's Lean attachment now names the canonical adopted declaration with
`existing: true` and its exact signature:

```lean
theorem derivedPullback_tensor_unit {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    : ∃ η : 𝟙_ (schemeDerivedCategory T) ≅
        (derivedPullback g).obj (𝟙_ (schemeDerivedCategory X)),
        (∀ A : schemeDerivedCategory X,
          (λ_ ((derivedPullback g).obj A)).hom =
            η.hom ▷ (derivedPullback g).obj A ≫
              ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
              (derivedPullback g).map (λ_ A).hom) ∧
        (∀ A : schemeDerivedCategory X,
          (ρ_ ((derivedPullback g).obj A)).hom =
            (derivedPullback g).obj A ◁ η.hom ≫
              ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
              (derivedPullback g).map (ρ_ A).hom)
```

All statement dependencies, proof dependencies, proof steps and unit records are
preserved. The canonical proof still constructs the explicit unit isomorphism,
applies both K-flat unit laws, and transports along a K-flat resolution of each
object. This is restoration through an existing complete proof, not withdrawal.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit | T7 | Restore by re-export of the canonical theorem. |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent | unclaimed | Quarantined direct importer; same theorem name and argument order, same pair of unit laws. No adaptation needed to this call. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent | unclaimed | Already uses the canonical adopted theorem; unchanged. |

`tools/downstream.py` reports `unknown module(s)` because the assigned module is
absent from the live tree. A source scan of both `lean/` and `quarantine/` finds
only the consumers listed above. The sole DAG parent is
`lem-pc-derived-pullback-monoidal-descent`, whose dependency remains in place.
The remaining occurrences in the counit and K-flat nodes are provenance links,
not parents that need adaptation. The quarantined parent has separate outstanding
sync repairs; this packet repairs the assigned module only.

A consumer probe compiles the full old statement against the re-exported theorem,
using the explicit former acyclic-tensor predicate. `Iff.rfl` verifies the
predicate equality. Both that consumer and the source theorem depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The restored import compiles
in 2.3 seconds and the consumer in 17.7 seconds.

## Status

landed 20261021T170806-L-2761164 2026-10-21 (merge of deliver/T7/Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit)
