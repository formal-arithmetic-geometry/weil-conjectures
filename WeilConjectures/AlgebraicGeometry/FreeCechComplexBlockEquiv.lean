/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible

public import Mathlib.LinearAlgebra.DFinsupp
import WeilConjectures.AlgebraicGeometry.FreeCechTupleDifferential

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Evaluation of the free Čech complex has a degreewise tuple-block basis, and the
basis identifications intertwine its differentials. No exactness assertion is involved
(Stacks, Tags 03AT and 03F5). -/
theorem freeCechComplex_block_equiv (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) :
    let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O))))
    let S := fun φ : W ⟶ U₀ => Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
    ∃ e : ∀ n : ℕ, K.X n ≃ₗ[O.obj (op W)]
        (Π₀ φ : W ⟶ U₀, Algebra.powerSetComplexObject (O.obj (op W)) (S φ) n),
      ∀ n : ℕ,
        (DFinsupp.mapRange.linearMap
          (fun φ => Algebra.powerSetComplexDifferential (O.obj (op W)) (S φ) n)).comp
            (e (n + 1)).toLinearMap = (e n).toLinearMap.comp (K.d (n + 1) n).hom := by
  classical
  dsimp
  let b := freeCechTupleMap X ι U₀ U f O W
  let e := fun n ↦ LinearEquiv.ofBijective (b n)
    (freeCechTupleMap_bijective X ι U₀ U f O W n)
  refine ⟨fun n ↦ (e n).symm, ?_⟩
  intro n
  have h := freeCechDifferential_compatibility X ι U₀ U f O W n
  dsimp [e, b] at h ⊢
  apply LinearMap.ext
  intro v
  apply (e n).injective
  have hv := LinearMap.congr_fun h ((e (n + 1)).symm v)
  let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (freeCechModule X ι U₀ U f O)))
  change (e n) ((DFinsupp.mapRange.linearMap _)
      ((e (n + 1)).symm v)) = (e n) ((e n).symm ((K.d (n + 1) n).hom v))
  rw [LinearEquiv.apply_symm_apply]
  have hv' : (K.d (n + 1) n).hom ((e (n + 1)) ((e (n + 1)).symm v)) =
      (e n) ((DFinsupp.mapRange.linearMap _ ) ((e (n + 1)).symm v)) := hv
  simpa only [LinearEquiv.apply_symm_apply] using hv'.symm

end AlgebraicGeometry
