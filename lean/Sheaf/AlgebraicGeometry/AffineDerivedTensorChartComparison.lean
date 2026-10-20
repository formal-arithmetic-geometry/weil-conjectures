/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import all WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import Sheaf.AlgebraicGeometry.AffineChartTotalTensor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Derived tensor through the canonical affine spectrum chart

Source: Stacks Project, Tags 08DX(2) and 08DV.
(blueprint: lem-pc-affine-derived-tensor-chart-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Compute affine derived tensor through the canonical spectrum chart, on given
module complexes and a given K-flat resolution of the first complex.
Source: Stacks Project, Tag 08DX(2), using Tag 08DV.
Proof: X.toSpecΓ is an isomorphism because X is affine. Exact restriction along it
preserves quasi-isomorphisms, tensor products, coproducts, and K-flat complexes.
Termwise tilde sends the given quasi-isomorphism s to a quasi-isomorphism, and tilde P
is K-flat by Tag 08DV. Thus restriction of tilde P is a K-flat representative of
restriction of tilde M. Compute the left derived tensor using that representative.
The affine tilde total-tensor comparison, restricted degree by degree, identifies
its total tensor with restriction of tilde Tot(P tensor N). Restriction preserves
arbitrary coproducts, including those in the unbounded total complex. This proves
the comparison for the specified resolution, without choosing an arbitrary derived
model. No quasi-coherence or boundedness assumption is used, and zero rings and
zero complexes are included.
(blueprint: lem-pc-affine-derived-tensor-chart-comparison). -/
theorem affine_derivedTensor_chart_comparison (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ)
    (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(X, ⊤)) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ⊗
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N)) ≅
      DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings X.toRingedSpace))
            (Scheme.Modules.restrictFunctor X.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
                (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                  (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} Γ(X, ⊤))))))) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S : ModuleCat.{u} Γ(X, ⊤) ⥤
      SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) :=
    tilde.functor Γ(X, ⊤)
  let R : SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤ C :=
    Scheme.Modules.restrictFunctor X.toSpecΓ
  let : S.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : R.PreservesZeroMorphisms := by
    change (Scheme.Modules.restrictFunctor X.toSpecΓ).PreservesZeroMorphisms
    infer_instance
  let T := S.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let F := RC.obj (T.obj P)
  let G := RC.obj (T.obj N)
  let K := RC.obj (T.obj (CochainComplex.mapBifunctor P N
    (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))))
  let : MonoidalCategory C := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalCategory (SheafOfModules.{u}
      (moduleRings (Spec Γ(X, ⊤)).toRingedSpace)) :=
    SheafOfModules.monoidalCategory (Spec Γ(X, ⊤)).sheaf
  let : (curriedTensor C).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : ∀ Z : C, ((curriedTensor C).obj Z).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  have hacyc : ∀ F₀ : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ,
      F₀.Acyclic → (CochainComplex.mapBifunctor F₀ P
        (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))).Acyclic := by
    intro F₀ hF₀
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F₀).mpr hF₀)).2
  have hT : CochainComplex.IsAcyclicTensorKFlat (R :=
      (Spec Γ(X, ⊤)).sheaf) (T.obj P) := isKFlat_tilde Γ(X, ⊤) P hacyc
  have hR : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) (RC.obj (T.obj P)) :=
    isKFlat_restrict X.toSpecΓ (T.obj P) hT
  let : ∀ {M₁ M₂ : ModuleCat.{u} Γ(X, ⊤)} (f : M₁ ⟶ M₂),
      PreservesLimit (parallelPair f 0) S := fun {_ _} f ↦
        tilde_preservesKernel (Γ(X, ⊤) : Type u) f
  let : PreservesFiniteLimits S :=
    Functor.preservesFiniteLimits_of_preservesKernels S
  let : S.IsLeftAdjoint := (tilde.adjunction (R := Γ(X, ⊤))).isLeftAdjoint
  let : PreservesFiniteColimits S := by
    dsimp [S]
    infer_instance
  let : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteLimits R := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let : S.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts S
    exact Functor.additive_of_preservesBinaryBiproducts S
  let : R.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts R
    exact Functor.additive_of_preservesBinaryBiproducts R
  let : QuasiIso s := hs
  have hsT : QuasiIso (T.map s) := by
    dsimp [T]
    infer_instance
  let : QuasiIso (T.map s) := hsT
  have hsR : QuasiIso (RC.map (T.map s)) := by
    dsimp [RC]
    infer_instance
  let FI := (Functor.const (Discrete PUnit.{1})).obj (RC.obj (T.obj P))
  let GI := (Functor.const (Discrete PUnit.{1})).obj (RC.obj (T.obj N))
  obtain ⟨cmp⟩ := kFlat_derivedTensor_comparison_natIso X FI GI (fun _ ↦ hR)
  let c := (cmp.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  obtain ⟨chart⟩ := affineChart_totalTensor_iso X P N
  let eS : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj (RC.obj (T.obj M)) :=
    asIso (DerivedCategory.Q.map (RC.map (T.map s)))
  let eC : DerivedCategory.Q.obj (CochainComplex.mapBifunctor F G
      (curriedTensor C)) ≅ DerivedCategory.Q.obj K := by
    simpa [F, G, K, RC, T, C, R] using (DerivedCategory.Q.mapIso chart)
  simpa [F, G, K, RC, T, C, R, S, FI, GI] using
    (⟨tensorIso eS.symm (Iso.refl _) ≪≫ c ≪≫ eC⟩ : Nonempty _)

end AlgebraicGeometry
