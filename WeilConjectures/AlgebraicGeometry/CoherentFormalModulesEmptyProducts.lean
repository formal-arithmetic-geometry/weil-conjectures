/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Empty products of coherent formal modules

Stacks Project, Tag 0EHN.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The empty limit satisfies the coherent formal module property (Stacks, Tag 0EHN). -/
theorem coherentFormalModules_closedUnderEmptyProducts (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  rintro F ⟨p⟩
  have hz : IsZero F := p.isLimit.isZero_pt (by
    rw [Functor.isZero_iff]
    rintro ⟨⟨⟩⟩)
  have hterm (n : ℕ) : IsZero (F.obj (op n)) :=
    hz.obj (op n)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    let A := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} PUnit)
    have hc : IsColimit (CokernelCofork.ofπ (0 : A ⟶ F.obj (op n))
        (show (𝟙 A) ≫ 0 = 0 by simp)) := by
      refine Cofork.IsColimit.mk _ (fun _ ↦ 0) ?_ ?_
      · intro s
        have hs := s.condition
        change (𝟙 A) ≫ s.π = 0 ≫ s.π at hs
        simpa only [Category.id_comp, zero_comp, comp_zero] using hs.symm
      · intro s m hm
        exact (hterm n).eq_of_src _ _
    let P := SheafOfModules.presentationOfIsCokernelFree (𝟙 A)
      (0 : A ⟶ F.obj (op n)) (by simp) hc
    have : P.generators.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} PUnit))⟩
    have : P.generators.localGeneratorsData.IsFiniteType := by
      refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk
        (p := P.generators.localGeneratorsData) (fun i ↦ ?_)
      change (P.generators.map _ _).IsFiniteType
      infer_instance
    have : (F.obj (op n)).IsFiniteType := by
      apply SheafOfModules.IsFiniteType.mk (M := F.obj (op n))
      exact ⟨P.generators.localGeneratorsData, inferInstance⟩
    have := P.isQuasicoherent
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
      ⟨inferInstance, inferInstance⟩
  · intro n
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    change IsZero (image _)
    exact IsZero.of_mono (image.ι _) (hterm n)
  · intro n
    have hq : IsZero (formalModuleQuotient I (n + 1) (F.obj (op (n + 1)))) := by
      change IsZero (cokernel _)
      exact IsZero.of_epi (cokernel.π _) (hterm (n + 1))
    exact ⟨hq.iso (hterm n), (hterm n).eq_of_tgt _ _⟩

end AlgebraicGeometry
