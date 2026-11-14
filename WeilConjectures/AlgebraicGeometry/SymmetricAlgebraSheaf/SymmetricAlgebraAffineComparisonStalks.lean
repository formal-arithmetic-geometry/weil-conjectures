/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineComparisonMap
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineSectionComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.RingSheafificationRestrictedStalks

/-! # Stalk comparison on an affine chart for the symmetric algebra

Source: Stacks Project, Modules, Lemma 01CH and Schemes, Lemma 01I8.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The tilde comparison is bijective on every stalk of the affine chart.
Source: Stacks Project, Modules, Lemmas 01CG and 01CH; Schemes, Lemma 01I8; Algebra, Lemma 0C6F.
This is step 6 of the affine symmetric algebra comparison. -/
theorem affineComparison_stalk_bijective {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (x : Spec Γ(X, W)) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf (Spec Γ(X, W))).map (affineComparison F hW))) := by
  let P := hW.fromSpec.opensFunctor.op ⋙ presheaf F ⋙
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u})
  let T := (Scheme.Modules.toPresheaf (Spec Γ(X, W))).obj
    (tilde (R := Γ(X, W)) (ModuleCat.of Γ(X, W) (sections F (op W))))
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let B : (Spec Γ(X, W)).affineOpens → (Spec Γ(X, W)).Opens := Subtype.val
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    simpa only [B, Subtype.range_coe] using (Spec Γ(X, W)).isBasis_affineOpens
  obtain ⟨δ, hδ, hδcomp⟩ := exists_affineSectionComparison F hW
  let TS : TopCat.Sheaf AddCommGrpCat.{u} (Spec Γ(X, W)) :=
    ⟨T, (tilde (R := Γ(X, W))
      (ModuleCat.of Γ(X, W) (sections F (op W)))).isSheaf⟩
  let γ : P ⟶ T := TopCat.Sheaf.restrictHomEquivHom P TS hB δ
  have hγapp (V : (Spec Γ(X, W)).affineOpens) :
      γ.app (op V.1) = δ.app (op V) :=
    TopCat.Sheaf.extend_hom_app P TS hB δ V
  have hγ (V : (Spec Γ(X, W)).Opens) (hV : IsAffineOpen V) :
      Function.Bijective (γ.app (op V)) := by
    change Function.Bijective (γ.app (op (B ⟨V, hV⟩)))
    rw [hγapp ⟨V, hV⟩]
    exact hδ ⟨V, hV⟩
  have hcomp : γ ≫
      (Scheme.Modules.toPresheaf (Spec Γ(X, W))).map (affineComparison F hW) =
      CategoryTheory.Functor.whiskerLeft hW.fromSpec.opensFunctor.op
        (CategoryTheory.Functor.whiskerRight
          (toSheafify (Opens.grothendieckTopology X) (presheaf F))
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u})) := by
    apply TopCat.Sheaf.hom_ext P
      ⟨_, (Scheme.Modules.restrict (algebra F).toModule hW.fromSpec).isSheaf⟩ hB
    intro V
    change γ.app (op V.1) ≫ _ = _
    rw [hγapp]
    exact hδcomp V
  have hγx : Function.Bijective (K.map γ) := by
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
      (Spec Γ(X, W)).isBasis_affineOpens (fun V hV ↦ (hγ V hV).1) x, ?_⟩
    intro t
    obtain ⟨V, hxV, hV, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
        (Spec Γ(X, W)).isBasis_affineOpens T x t
    obtain ⟨a, ha⟩ := (hγ V hV).2 s
    refine ⟨TopCat.Presheaf.germ P V x hxV a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha]
  have hθ := ringSheafification_restricted_stalk_bijective hW.fromSpec (presheaf F) x
  have hwhole : Function.Bijective
      (K.map (γ ≫ (Scheme.Modules.toPresheaf (Spec Γ(X, W))).map
        (affineComparison F hW))) := by
    rw [hcomp]
    exact hθ
  rw [Functor.map_comp] at hwhole
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := hγx.2 a
    obtain ⟨b', rfl⟩ := hγx.2 b
    exact congrArg (K.map γ) (hwhole.1 hab)
  · intro t
    obtain ⟨a, ha⟩ := hwhole.2 t
    exact ⟨K.map γ a, ha⟩

end AlgebraicGeometry.SymmetricAlgebraSheaf
