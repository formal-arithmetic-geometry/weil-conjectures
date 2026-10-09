/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Acyclic envelopes of étale sheaves killed by an integer

Let `n ≠ 0`. Every abelian étale sheaf `G` on a scheme `X` with `n • 𝟙 G = 0` embeds into an
abelian sheaf `J` with `n • 𝟙 J = 0` which has no cohomology in positive degrees, and which stays
acyclic after pushforward along any morphism and after restriction along any étale morphism:
take for `J` the `n`-torsion subsheaf `I[n]` of an injective sheaf `I ⊇ G`. Pushforward and étale
restriction preserve injective sheaves and commute with taking `n`-torsion, and the `n`-torsion
of an injective sheaf is acyclic (`CategoryTheory.Sheaf.subsingleton_H_kernel_nsmul_of_injective`).
This allows dimension shifting within sheaves killed by `n`.

## Main statements

- `AlgebraicGeometry.Etale.injective_upperStar_obj_of_etale_addCommGrp`: restriction along an
  étale morphism preserves injective abelian sheaves.
- `AlgebraicGeometry.Etale.exists_mono_acyclic_of_nsmul_eq_zero`: the acyclic envelope.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Etale

variable {W X : Scheme.{u}}

/-- **Étale restriction preserves injective abelian sheaves**: for an étale `v : W ⟶ X`, the
pullback `v^*` has the exact left adjoint `v_!` (the extension by zero, left Kan extension along
the localization functor followed by sheafification). -/
theorem injective_upperStar_obj_of_etale_addCommGrp (v : W ⟶ X) [AlgebraicGeometry.Etale v]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((v)^*[AddCommGrpCat.{u + 1}].obj I) := by
  have h : AlgebraicGeometry.Etale v := inferInstance
  have : (MorphismProperty.Over.map ⊤ h).IsContinuous W.smallEtaleTopology
      X.smallEtaleTopology :=
    inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
      (W.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale))
  let adj := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ h) AddCommGrpCat.{u + 1} W.smallEtaleTopology
      X.smallEtaleTopology).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} v h).symm
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ h) AddCommGrpCat.{u + 1} W.smallEtaleTopology
        X.smallEtaleTopology) := by
    have heq : Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h)
        AddCommGrpCat.{u + 1} W.smallEtaleTopology X.smallEtaleTopology =
        sheafToPresheaf W.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (MorphismProperty.Over.map ⊤ h).op.lan ⋙
            presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
      rfl
    have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
        (W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
      SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian _ h
    rw [heq]
    exact comp_preservesFiniteLimits _ _
  exact adj.map_injective I inferInstance

variable (X) in
/-- **Acyclic envelopes of sheaves killed by `n`.** Let `n ≠ 0` and `G` an abelian étale sheaf on
`X` with `n • 𝟙 G = 0`. Then `G` embeds into a sheaf `J` with `n • 𝟙 J = 0` such that `J`, its
pushforward along any morphism `j : X ⟶ Y` and its restriction along any étale `w : W ⟶ X` have
no cohomology in positive degrees: `J` is the `n`-torsion `I[n]` of an injective sheaf `I ⊇ G`. -/
theorem exists_mono_acyclic_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : n • 𝟙 G = 0) :
    ∃ (J : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ι : G ⟶ J), Mono ι ∧
      n • 𝟙 J = 0 ∧ (∀ q, Subsingleton (Sheaf.H J (q + 1))) ∧
      (∀ {Y : Scheme.{u}} (j : X ⟶ Y) q,
        Subsingleton (Sheaf.H ((j)_*[AddCommGrpCat.{u + 1}].obj J) (q + 1))) ∧
      (∀ {W : Scheme.{u}} (w : W ⟶ X) [AlgebraicGeometry.Etale w] q,
        Subsingleton (Sheaf.H ((w)^*[AddCommGrpCat.{u + 1}].obj J) (q + 1))) := by
  let I := Injective.under G
  let J := kernel (n • 𝟙 I)
  have hι : Injective.ι G ≫ (n • 𝟙 I) = 0 := by
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (Injective.ι G),
      ← Preadditive.nsmul_comp, hG, zero_comp]
  refine ⟨J, kernel.lift _ (Injective.ι G) hι, ?_, ?_, ?_, fun {Y} j q ↦ ?_, fun {W} w _ q ↦ ?_⟩
  · exact mono_of_mono_fac (kernel.lift_ι _ _ hι)
  · rw [← cancel_mono (kernel.ι (n • 𝟙 I)), Preadditive.nsmul_comp, Category.id_comp,
      zero_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
  · exact fun q ↦ Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} I hn q
  · let P := (j)_*[AddCommGrpCat.{u + 1}]
    have : Injective (P.obj I) :=
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).map_injective I inferInstance
    have e : P.obj J ≅ kernel (n • 𝟙 (P.obj I)) :=
      PreservesKernel.iso P (n • 𝟙 I) ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
        (by simp)
    have : Subsingleton ((Sheaf.functorH _ (q + 1)).obj (kernel (n • 𝟙 (P.obj I)))) :=
      Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} (P.obj I) hn q
    exact ((Sheaf.functorH _ (q + 1)).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  · let P := (w)^*[AddCommGrpCat.{u + 1}]
    have : Injective (P.obj I) := injective_upperStar_obj_of_etale_addCommGrp w I
    have e : P.obj J ≅ kernel (n • 𝟙 (P.obj I)) :=
      PreservesKernel.iso P (n • 𝟙 I) ≪≫ kernel.mapIso _ _ (Iso.refl _) (Iso.refl _)
        (by simp)
    have : Subsingleton ((Sheaf.functorH _ (q + 1)).obj (kernel (n • 𝟙 (P.obj I)))) :=
      Sheaf.subsingleton_H_kernel_nsmul_of_injective.{_, u + 1, u, u + 1} (P.obj I) hn q
    exact ((Sheaf.functorH _ (q + 1)).mapIso e).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end Etale

end AlgebraicGeometry
