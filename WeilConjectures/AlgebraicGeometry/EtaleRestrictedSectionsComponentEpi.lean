/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsFactors

/-! # Degreewise epimorphism of the restricted sections lift

Source: Stacks Project, Tag 015J, total-complex comparison and column filtration.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The restricted sections factor map is epimorphic in every degree
(Stacks, Tag 015J). -/
theorem etaleRestrictedSectionsLift_component_epi
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    Epi (((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
      (etaleRestrictedSections_factors X K T q)).f n) := by
  classical
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj T.I).flip
  let R := ((CartanEilenbergPresentation.mappedFunctor F).obj
    (etaleRestrictedBicomplex X K T q)).flip
  let f := (etaleRestrictedSectionsInclusion X K T q).f n
  let m := (etaleRestrictedMappedInclusion X K T q).f n
  let g := ((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
    (etaleRestrictedSections_factors X K T q)).f n
  let a := (T.L.step q).arrow.f n
  have hg : g ≫ a = f := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun h ↦ h.f n) ((T.L.step q).factorThru_arrow
        (etaleRestrictedSectionsInclusion X K T q)
        (etaleRestrictedSections_factors X K T q))
  have him : imageSubobject f = imageSubobject m := by
    dsimp [f, etaleRestrictedSectionsInclusion]
    exact imageSubobject_iso_comp _ _
  have hle : imageSubobject f ≤ Subobject.mk a :=
    imageSubobject_le_mk a f g hg
  have hge : Subobject.mk a ≤ imageSubobject f := by
    change Subobject.mk ((T.L.step q).arrow.f n) ≤ imageSubobject f
    rw [← imageSubobject_mono, ← DecreasingFiltration.complexStep,
      T.filtration_formula]
    change (Finset.Icc q n).sup (fun s ↦ imageSubobject
      (J.ιTotalOrZero (ComplexShape.up ℤ) (n - s) s n)) ≤ imageSubobject f
    apply Finset.sup_le
    intro s hs
    have hqs : q ≤ s := (Finset.mem_Icc.mp hs).1
    have he : (ComplexShape.embeddingUpIntGE q).f (s - q).toNat = s := by
      change q + ((s - q).toNat : ℤ) = s
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have : IsIso ((T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f s) :=
      T.I.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE q) he
    have : IsIso ((G.map ((T.I.ιStupidTrunc
        (ComplexShape.embeddingUpIntGE q)).f s)).f (n - s)) := inferInstance
    have hdiag : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (n - s, s) = n := by
      change (n - s) + s = n
      omega
    have hcomp : R.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag ≫ m =
        (G.map ((T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f s)).f (n - s) ≫
          J.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag := by
      dsimp [m, etaleRestrictedMappedInclusion]
      rw [HomologicalComplex₂.ιTotal_map]
      rfl
    rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - s) s n hdiag, him]
    calc
      imageSubobject (J.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag) =
          imageSubobject (R.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag ≫ m) := by
        rw [hcomp, imageSubobject_iso_comp]
      _ ≤ imageSubobject m := imageSubobject_comp_le _ _
  have heq : imageSubobject f = Subobject.mk a := le_antisymm hle hge
  let g' := g ≫ (Subobject.underlyingIso a).inv
  have : Epi g' := epi_of_imageSubobject_comp_arrow_eq g' (by
    simpa [g', hg] using heq)
  have : Epi (g' ≫ (Subobject.underlyingIso a).hom) := inferInstance
  simpa only [g', Category.assoc, Iso.inv_hom_id, Category.comp_id] using this

end AlgebraicGeometry.Etale
