/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCohomologyCoproduct

/-! # Derived direct image preserves direct sums

## References

* Stacks Project, Perfect Complexes, quasi-coherence of pushforward and direct sums
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem exists_ambient_coproduct (Y : Scheme.{u₁})
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedCategory Y) :
    ∃ (S : schemeDerivedCategory Y) (ι : ∀ i, E i ⟶ S),
      Nonempty (IsColimit (Cofan.mk S ι)) ∧
      ∀ q : ℤ, IsIso (Sigma.desc (fun i ↦
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) q).map (ι i))) := by
  classical
  let Q := DerivedCategory.Q (C := SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
  let K := fun i ↦ Q.objPreimage (E i)
  let e := fun i ↦ Q.objObjPreimageIso (E i)
  exact ⟨Q.obj (∐ K), (fun i ↦ (e i).inv ≫ Q.map (Sigma.ι K i)),
    derivedAmbientDirectSums Y I E K e⟩

/-- For a quasi-compact and quasi-separated morphism of schemes, derived direct image
preserves every set-indexed coproduct of objects with quasi-coherent cohomology
(Stacks Project, Perfect Complexes). -/
theorem derivedDirectImagePreservesDirectSums {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))] :
    ∀ (I : Type u₁) (E : I → schemeDerivedQCohCategory X),
      PreservesColimit (Discrete.functor (fun i => (E i).obj))
        (schemeDerivedDirectImage f) := by
  classical
  intro I E
  refine ⟨?_⟩
  intro c hc
  let F := schemeDerivedDirectImage f
  let c' := Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.ι.app ⟨i⟩))
  obtain ⟨S, ι, ⟨hs⟩, hH⟩ := exists_ambient_coproduct Y I (fun i ↦ F.obj (E i).obj)
  let comparison := hs.desc c'
  have hcomparison : IsIso comparison := by
    apply (DerivedCategory.isIso_iff _ comparison).2
    intro q
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) q
    have hsource : IsIso (Sigma.desc (fun i ↦ H.map (ι i))) := hH q
    have htarget : IsIso (Sigma.desc (fun i ↦ H.map (F.map (c.ι.app ⟨i⟩)))) := by
      apply derivedDirectImage_cohomology_coproduct f I E c.pt
      exact hc
    have heq : Sigma.desc (fun i ↦ H.map (ι i)) ≫ H.map comparison =
        Sigma.desc (fun i ↦ H.map (F.map (c.ι.app ⟨i⟩))) := by
      apply Sigma.hom_ext
      intro i
      simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
      rw [← H.map_comp]
      congr 1
      exact hs.fac c' ⟨i⟩
    have : IsIso (Sigma.desc (fun i ↦ H.map (ι i)) ≫ H.map comparison) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_left (Sigma.desc (fun i ↦ H.map (ι i))) (H.map comparison)
  have hc' : IsColimit c' := hs.ofPointIso
  refine ⟨IsColimit.mk (fun s ↦ hc'.desc
    (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩))) ?_ ?_⟩
  · intro s j
    exact hc'.fac (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩)) j
  · intro s m hm
    apply hc'.uniq (Cofan.mk s.pt (fun i ↦ s.ι.app ⟨i⟩)) m
    exact hm

end AlgebraicGeometry
