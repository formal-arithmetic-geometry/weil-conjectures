/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.Algebra.Homology.KFlatTensorProduct
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-!
# Derived pullback and derived tensor product

There is no derived tensor bifunctor on `D(𝒪_X)`, so `K ⊗^L L` is stated through K-flat
representatives `K ≅ Q(P)`, `L ≅ Q(N)`, for which `K ⊗^L L ≅ Q(Tot(P ⊗_{𝒪_X} N))`.

## References

* Stacks Project, Tag 079U
-/

@[expose] public section

universe uPull wPull

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The tensor product of sheaves of `𝒪_X`-modules, `SheafOfModules.monoidalCategory X.sheaf`,
made a local instance for the total tensor complexes below. -/
noncomputable local instance instMonoidalCategoryModulesOfDerivedPullbackTensorProduct
    (X : Scheme.{uPull}) :
    MonoidalCategory (SheafOfModules.{uPull} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in
-- Elaborating the transported tensor comparison and its totalization needs extra heartbeats.
set_option synthInstance.maxSize 256 in
/-- For a morphism of schemes `g : T ⟶ S`, derived pullback commutes with derived tensor product:
`Lg^*(K ⊗^L L) ≅ Lg^*K ⊗^L Lg^*L`, canonically and naturally in `K` and `L`, stated on K-flat
representatives. (Stacks, Tag 079U) -/
theorem derivedPullback_tensorProduct
    {T S : Scheme.{uPull}} (g : T ⟶ S)
    [HasDerivedCategory.{wPull}
      (SheafOfModules.{uPull} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wPull}
      (SheafOfModules.{uPull} (moduleRings T.toRingedSpace))] :
    ∃ (F : SheafOfModules.{uPull} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{uPull} (moduleRings T.toRingedSpace))
      (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
      (_ : ∀ {M N} (a : M ⟶ N),
        F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
          eqToHom (hF N).symm)
      (_ : F.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      (derivedPullback g).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ,
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
            CochainComplex.mapBifunctor ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ (P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ)
            (p q n : ℤ) (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (ComplexShape.up ℤ)
              p q n h) ≫ (φ P N).hom.f n =
            eqToHom (hF _) ≫
              ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p)
                (N.X q)).hom ≫
              (eqToHom (hF (P.X p)).symm ⊗ₘ eqToHom (hF (N.X q)).symm) ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _)
                (ComplexShape.up ℤ) p q n h) ∧
        (∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ)) ∧
        ∀ P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := S.sheaf) P →
            CochainComplex.IsKFlatTensor (R := S.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)) := by
  classical
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hmap, hadd, ε, hder, htri, hε⟩ :=
      (derivedPullback_spec g)
  -- The recorded object and map formulas determine the termwise functor strictly.
  have hEq : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  let : (Scheme.Modules.tensorPullback g).Additive := hadd
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  let : (Scheme.Modules.tensorPullback g).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  let G := Scheme.Modules.tensorPullback g
  let e := Classical.choose (Scheme.Modules.module_pullback_tensor g)
  have hn := (Classical.choose_spec (Scheme.Modules.module_pullback_tensor g)).1
  -- Package the two-variable module comparison for the existing totalization API.
  let τ : (Functor.postcompose₂.obj G).obj
      (curriedTensor (SheafOfModules.{uPull} (moduleRings S.toRingedSpace))) ⟶
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj
        (curriedTensor (SheafOfModules.{uPull} (moduleRings T.toRingedSpace))) :=
    { app := fun M ↦
        { app := fun N ↦ (e M N).hom
          naturality := by
            intro N N' b
            simpa using hn M N M N' (𝟙 M) b }
      naturality := by
        intro M M' a
        apply NatTrans.ext
        funext N
        simpa using hn M N M' N a (𝟙 N) }
  let : ∀ M N, IsIso ((τ.app M).app N) := fun M N ↦ (e M N).isIso_hom
  let : (curriedTensor (SheafOfModules.{uPull}
      (moduleRings S.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor S.sheaf
  let : (curriedTensor (SheafOfModules.{uPull}
      (moduleRings T.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  let : ∀ M : SheafOfModules.{uPull} (moduleRings S.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj S.sheaf M
  let : ∀ M : SheafOfModules.{uPull} (moduleRings T.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf M
  let φ := fun (P N : CochainComplex
      (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ) ↦
    asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P N)
  refine ⟨G, hF, hmap, hadd, ε, hder, φ, ?_, ?_, ?_⟩
  · intro P N p q n h
    simpa only [φ, asIso_hom, HomologicalComplex.mapBifunctorComparison_f,
      HomologicalComplex.mapBifunctorComparisonApp, τ, e, G, eqToHom_refl,
      tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id] using
      HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) P N p q n h
  · intro P P' N N' a b
    exact HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) a b
  · intro P N hP hN
    have hflat := CochainComplex.IsKFlatTensor.mapBifunctor
      (X := S.toRingedSpace) P N hP hN
    let := hε (CochainComplex.mapBifunctor P N (curriedTensor _)) hflat
    infer_instance

end AlgebraicGeometry
