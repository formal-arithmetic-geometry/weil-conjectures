# AlgebraicGeometry.derivedPullback_monoidal_descent

## Reason

Repair return C-3b01e for delivery 3b01ec8345f. The independent reader passed the
mathematical packet, but landing rejected a reviewer correction named only
B2-derived-pullback-monoidal-descent-restoration.md. This record is delivered at
its repository-relative path:
coord/changes/B2-derived-pullback-monoidal-descent-restoration.md.
Any reviewer correction of this record must preserve that directory path.
The record is absent from current sheaf-dag and is included in the repaired packet.
The delivery tool rebases the retained work onto freshly fetched sheaf-dag.
The current compatibility consumer matches the retained consumer exactly; the
only node differences are the two Lean attachments. Preserve the approved
retirement, replacement theorem, proof plans, dependencies and unit route.
Fresh server compilation is recorded in the accompanying report. The consumer
compiled in 4.7 seconds. A separate 1.8-second axiom probe printed only propext,
Classical.choice and Quot.sound for the descent theorem, model predicate and
model existence theorem.

Repair the stale-base return from reviewer C-51828 (delivery 51828489665).
Read the current server modules before changing the retained packet. Both are now
compatibility imports of their adopted source counterparts. The retained consumer
still reintroduced the old declarations; replace it with the current compatibility
module, so downstream imports cannot create duplicate declarations.

The explicit coord/retire-items.tsv row assigns retirement of the descent twin.
Carry out that retirement and preserve its actual argument in the adopted source.
This is not a withdrawal inferred from an absent quarantined path: the current
retirement assignment names the source replacement, and the current consumer uses
that replacement through its adopted model. Quarantine archives remain untouched.

## Old


Archived root theorem signature, verbatim:

```lean
theorem derivedPullback_monoidal_descent {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    (hnatural : ∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ))
    (hiso : ∀ P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P → CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ m : (derivedPullback g).CoreMonoidal,
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P →
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
```

The archived consumer imports:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent
```

The archived consumer definition, verbatim:

```lean
def IsDerivedPullbackMonoidalModel {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal) : Prop := by
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := moduleSymmetric X
  letI := moduleSymmetric T
  haveI := modulePreadditive X
  haveI := modulePreadditive T
  letI := moduleClosed X
  letI := moduleClosed T
  haveI := moduleGrothendieck X
  haveI := moduleGrothendieck T
  haveI := moduleResolutions X
  haveI := moduleResolutions T
  haveI := moduleDerivedMonoidal X
  haveI := moduleDerivedMonoidal T
  letI := m.toMonoidal
  exact ∃ (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (_ : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    (_ : F.Additive) (mF : F.CoreMonoidal),
    (∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm)) ∧
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h) ∧
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P →
          CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
```

## New

The descent path is withdrawn, as recorded in deleted.txt. Its node now points to
WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent and the existing
AlgebraicGeometry.derivedPullback_monoidal_descent declaration, with its verbatim
source signature. All three mathematical proof dependencies remain.

The consumer is restored using exactly the compatibility module currently on the
server, rather than restoring duplicate public declarations:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel

/-! # Monoidal models of the derived pullback

Compatibility import for the complete adopted source proof of
`AlgebraicGeometry.IsDerivedPullbackMonoidalModel` and
`AlgebraicGeometry.exists_derivedPullbackMonoidalModel`.
The source module `WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel` is now
in the import closure of the downstream Sheaf modules, so the former copy at this
path would clash with it. Its `CochainComplex.IsKFlatTensor` is the acyclic-tensor
predicate formerly named `CochainComplex.IsAcyclicTensorKFlat` at this path.

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: def-pc-derived-pullback-monoidal-model).
-/

@[expose] public section
```

The model node now records the existing declarations at
WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel. Its predicate and
existence theorem, and every proof dependency, remain. IsKFlatTensor is the adopted
name of the same acyclic-tensor predicate formerly named IsAcyclicTensorKFlat.
No source-library declaration, signature, import or proof is changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel | unclaimed | Preserve the current server compatibility module; its source model imports the adopted descent. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel | unclaimed | Already uses the adopted descent; unchanged. |

The current Sheaf model compatibility consumer imports the adopted source model,
whose predicate and complete existence proof are preserved. It is byte-identical
to the consumer in this packet. The old quarantined model records the former
import of the retired descent path; its archive is preserved. Parent
DAG edges and both node proof plans are unchanged. No mathematical node or unit
step is bypassed. The retired descent and restored compatibility model have zero
holes; the existing source proofs are checked with axiom probes.

## Status

landed 20261021T203408-L-3717831 2026-10-21 (merge of deliver/B2/Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent)
