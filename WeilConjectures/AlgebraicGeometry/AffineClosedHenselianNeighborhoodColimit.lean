/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.AffineClosedHenselianRingPresentation
import WeilConjectures.AlgebraicGeometry.SpecRingCohomologyDiagram
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules

/-! # Continuity at the henselization of a closed affine pair -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- A closed affine pair admits a henselian neighborhood whose cohomology is computed
by a small filtered system of etale neighborhoods. Torsion is not needed here.

Source: Stacks Project, Tag 0A51, second displayed equality in the affine proof;
Tags 0A02 and 09YQ. -/
theorem Etale.affine_closed_henselian_neighborhood_colimit
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    ∃ (A : Type u) (_ : CommRing A) (K : Ideal A) (_ : HenselianRing A K)
      (t : Spec (.of A) ⟶ X) (e : Z ≅ Spec (.of (A ⧸ K))),
      i = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ t ∧
      ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
        (Y : I → Scheme.{u}) (v : ∀ a, Y a ⟶ X),
        (∀ a, Etale (v a)) ∧
        ∃ (H : I ⥤ AddCommGrpCat.{u + 1}) (c : Cocone H),
          Nonempty (IsColimit c) ∧
          Nonempty (AddCommGrpCat.of (Sheaf.H
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
              ((t)^*[ModuleCat.{u + 1} Λ].obj J)) q) ≅ c.pt) ∧
          ∀ a, Nonempty (H.obj a ≅ AddCommGrpCat.of (Sheaf.H
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
              ((v a)^*[ModuleCat.{u + 1} Λ].obj J)) q)) := by
  obtain ⟨I, _, _, _, R, c, hc, K, hK, t, e, hi, v, wv, wt, hev⟩ :=
    Etale.affine_closed_henselian_ring_presentation i
  obtain ⟨H, eH, hH, B, eB, hB⟩ :=
    Etale.exists_spec_ring_cohomology_diagram R c hc X
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J) v wv t wt q
  obtain ⟨hcol⟩ := AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_spec_ring_colimit
    R c hc X ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
    ((fun a ↦ v a)) wv t wt q H eH hH B eB hB
  refine ⟨c.pt, inferInstance, K, hK, t, e, hi, I, inferInstance, inferInstance,
    (fun a ↦ Spec (R.obj a)), v, hev, H, B, ⟨hcol⟩, ?_, ?_⟩
  · obtain ⟨et⟩ := Etale.pullback_forget_modules_iso Λ t J
    exact ⟨(Sheaf.functorH _ q).mapIso et ≪≫ eB.symm⟩
  · intro a
    obtain ⟨ea⟩ := Etale.pullback_forget_modules_iso Λ (v a) J
    exact ⟨eH a ≪≫ (Sheaf.functorH _ q).mapIso ea.symm⟩

end AlgebraicGeometry
