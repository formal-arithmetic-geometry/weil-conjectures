/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom
import WeilConjectures.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension
import WeilConjectures.AlgebraicGeometry.TensorHomRestrictionScalar
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction

/-! # Tensor extension of a coherent local morphism

Stacks Project, Tag 01YB.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- A local morphism extends from an ideal-power tensor product. (Stacks, Tag 01YB). -/
theorem coherent_open_map_tensor_extension
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (H F : X.Modules)
    (hH : RingedSpace.IsCoherent X.toRingedSpace H) [F.IsQuasicoherent]
    (U : X.Opens) (hI : (I.support : Set X) = (U : Set X)ᶜ)
    (φ : (restrictFunctor U.ι).obj H ⟶ (restrictFunctor U.ι).obj F) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∃ (n : ℕ) (β : (I ^ n).toModules ⊗ H ⟶ F),
      (restrictFunctor U.ι).map β =
        (restrictFunctor U.ι).map ((I ^ n).toModulesι ▷ H ≫ (λ_ H).hom) ≫ φ := by
  classical
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : H.IsFinitePresentation :=
    AlgebraicGeometry.isFinitePresentation_of_coherent X H hH
  let E : X.Modules := SheafOfModules.homObj (R := X.sheaf) H F
  have : E.IsQuasicoherent := isQuasicoherent_homObj_of_isFinitePresentation X H F
  let ψ := (overFunctorEquiv U).hom.app H ≫ φ ≫ (overFunctorEquiv U).inv.app F
  let σ : H.over U ⟶ F.over U := (overEquiv U).functor.preimage ψ
  let s : E.val.obj (.op U) := σ.val
  obtain ⟨n, α, hα⟩ := quasicoherent_open_section_ideal_extension I E U hI s
  obtain ⟨e, he, _⟩ := SheafOfModules.exists_tensorHom_linearEquiv X X.sheaf H F
  refine ⟨n, e _ α, ?_⟩
  have ht := tensorHom_restriction_of_local_scalar (I ^ n).toModules H F
    (I ^ n).toModulesι U s α hα (e _ α) (he _ α).1
  have hσ : (overEquiv U).functor.map σ = ψ := Functor.map_preimage _ _
  change (restrictFunctor U.ι).map (e _ α) = _
  rw [ht]
  rw [show (⟨s⟩ : H.over U ⟶ F.over U) = σ from rfl, hσ]
  simp [ψ, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
