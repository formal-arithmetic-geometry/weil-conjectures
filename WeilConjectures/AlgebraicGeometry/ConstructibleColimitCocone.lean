/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleSheafGeneration
import WeilConjectures.AlgebraicGeometry.ConstructibleColimitFactorization
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.ConstructibleSheaf.FinitePushforward

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Constructible-source factorization and refinement of relations recognize a
filtered colimit cocone. No constructibility assumption on the diagram is needed
(Stacks, Tags 09Z4, 03EW, 03S8 and 03SA). -/
theorem exists_constructible_colimit_cocone
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A : Type (u + 1)) [SmallCategory A] [IsFiltered A]
    (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ι : D ⟶ (Functor.const A).obj F)
    (hfactor : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf G → ∀ p : G ⟶ F,
        ∃ (a : A) (q : G ⟶ D.obj a), q ≫ ι.app a = p)
    (hrelations : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf G → ∀ (a b : A)
        (p : G ⟶ D.obj a) (q : G ⟶ D.obj b),
        p ≫ ι.app a = q ≫ ι.app b →
        ∃ (c : A) (f : a ⟶ c) (g : b ⟶ c), p ≫ D.map f = q ≫ D.map g) :
    Nonempty (IsColimit (Cocone.mk F ι)) := by
  classical
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsConstructibleEtaleModuleSheaf
  have hP : P.IsSeparating := ObjectProperty.IsSeparating.mk_of_exists_epi fun H ↦ by
    obtain ⟨I, C, hC, hcoprod, π, hπ⟩ := exists_epi_coproduct_constructible H
    let := hcoprod
    exact ⟨I, C, hC, colimit.cocone (Discrete.functor C), colimit.isColimit _, π, hπ⟩
  let : HasColimit D := inferInstance
  let t : colimit D ⟶ F := colimit.desc D (Cocone.mk F ι)
  have ht (a : A) : colimit.ι D a ≫ t = ι.app a := colimit.ι_desc _ _
  have hinj (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hG : P G) (p q : G ⟶ colimit D) (hpq : p ≫ t = q ≫ t) : p = q := by
    obtain ⟨a, p', rfl⟩ := exists_constructible_hom_of_isColimit G hG (colimit.isColimit D) p
    obtain ⟨b, q', rfl⟩ := exists_constructible_hom_of_isColimit G hG (colimit.isColimit D) q
    obtain ⟨c, f, g, h⟩ := hrelations G hG a b p' q' (by simpa [Category.assoc, ht] using hpq)
    calc
      p' ≫ colimit.ι D a = (p' ≫ D.map f) ≫ colimit.ι D c := by simp
      _ = (q' ≫ D.map g) ≫ colimit.ι D c := by rw [h]
      _ = q' ≫ colimit.ι D b := by simp
  have : IsIso t := hP.isDetecting t fun G hG p ↦ by
    obtain ⟨a, q, hq⟩ := hfactor G hG p
    refine ⟨q ≫ colimit.ι D a, ?_, ?_⟩
    · simpa [Category.assoc, ht] using hq
    · intro q' hq'
      apply hinj G hG
      simpa [Category.assoc, ht, hq] using hq'
  exact ⟨(colimit.isColimit D).ofIsoColimit
    (Cocone.ext (asIso t) (fun a ↦ ht a))⟩

end AlgebraicGeometry.Scheme
