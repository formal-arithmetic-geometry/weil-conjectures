/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-! # Tensor comparison on K-flat representatives

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-kflat-tensor-model).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance kFlatTensorModelPullbackDescentModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

noncomputable local instance kFlatTensorModelModuleSymmetric (S : Scheme.{uModel}) :
    SymmetricCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.symmetricCategory S.sheaf

noncomputable local instance kFlatTensorModelModulePreadditive (S : Scheme.{uModel}) :
    MonoidalPreadditive (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).1

noncomputable local instance kFlatTensorModelModuleClosed (S : Scheme.{uModel}) :
    MonoidalClosed (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1

local instance kFlatTensorModelModuleGrothendieck (S : Scheme.{uModel}) :
    IsGrothendieckAbelian.{uModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings S.toRingedSpace)

local instance kFlatTensorModelModuleResolutions (S : Scheme.{uModel}) :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution S

local instance kFlatTensorModelModuleDerivedMonoidal (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

noncomputable local instance kFlatTensorModelPullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance

/-- The comparison on K-flat cochain representatives, before localization in either
variable. Source: Stacks Project, Cohomology, Tags 079U, 06YC and 06YH; steps 1 and 2
and the representative naturality calculation of the parent proof.
(blueprint: lem-pc-derived-pullback-kflat-tensor-model).

Proof: identify F with tensorPullback by functor extensionality. Uniqueness of the
left-derived functor compares epsilon with the recorded K-flat counit; hence epsilon
is invertible on K-flat complexes. Pullback preserves K-flatness (06YC). The derived
localization tensorator is invertible when its first argument is K-flat (06YH), both
on X and on T after F. For a K-flat pair let A=L(mu_Q), B=epsilon_tensor followed by
Q(phi), and C=(epsilon_P tensor epsilon_N) followed by mu_Q(FP,FN). A and C are
invertible by those computations and B by hiso. Set e=C followed by B inverse and
A inverse. Cancellation gives e;A;B=C. Naturality of the lax tensorator, epsilon
and phi gives u;A'B'=AB;z and v;C'=C;z for the induced source, target and model maps.
Postcompose v;e' and e;u with the invertible A'B' and use these two equalities;
cancellation proves simultaneous naturality. No localization of the K-flat full
subcategory, or extension to arbitrary derived objects, occurs in this lemma.
The construction includes the identity and empty scheme without a flatness hypothesis. -/
theorem derivedPullback_kFlat_tensor_model {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
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
          CochainComplex.IsKFlat (R := X.sheaf) P → CochainComplex.IsKFlat (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ e : ∀ (P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := X.sheaf) P →
        CochainComplex.IsKFlat (R := X.sheaf) N →
          (((derivedPullback g).obj (DerivedCategory.Q.obj P) ⊗
            (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≅
          (derivedPullback g).obj (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N)),
      (∀ (P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
        (hN : CochainComplex.IsKFlat (R := X.sheaf) N),
        (e P N hP hN).hom ≫
            (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
            DerivedCategory.Q.map (φ P N).hom =
          (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              ((F.mapHomologicalComplex (.up ℤ)).obj P)
              ((F.mapHomologicalComplex (.up ℤ)).obj N)) ∧
      (∀ (P P' N N' : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
        (hP' : CochainComplex.IsKFlat (R := X.sheaf) P')
        (hN : CochainComplex.IsKFlat (R := X.sheaf) N)
        (hN' : CochainComplex.IsKFlat (R := X.sheaf) N') (a : P ⟶ P') (b : N ⟶ N'),
        ((curriedTensorPre (derivedPullback g)).map (DerivedCategory.Q.map a)).app
            (DerivedCategory.Q.obj N) ≫
            ((curriedTensorPre (derivedPullback g)).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map b) ≫ (e P' N' hP' hN').hom =
          (e P N hP hN).hom ≫
            ((curriedTensorPost (derivedPullback g)).map (DerivedCategory.Q.map a)).app
              (DerivedCategory.Q.obj N) ≫
            ((curriedTensorPost (derivedPullback g)).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map b)) := by sorry

end AlgebraicGeometry
