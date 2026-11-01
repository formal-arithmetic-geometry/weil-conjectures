/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.Integral.IntegralConstructibleReductionHom
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteDualizingCoherence
/-! Reconstruction of an isomorphism from compatible finite reductions.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 2-3
(blueprint: lem-sf-integral-finite-extension-u-invertibility).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
/-- A comparison whose reductions are all invertible is itself invertible.

Use `integralConstructibleReductionHom` on the inverse finite reductions. Its
successor compatibility follows from naturality of the reduction functor and
inversion of the transition square. The lifted inverse is a two-sided inverse
by the uniqueness clause of the same reconstruction theorem. This is the
Milnor/Roos effectivity step and is independent of the finite-level calculation.
(blueprint: lem-sf-integral-finite-extension-u-reconstruction)
-/
theorem comparison_invertibility_u_of_reductions
    (hred : ∀ n : ℕ,
      IsIso ((scalarReductionDerivedExtension l L X n).map
        (u l E L ι X D hl wE wL))) :
    IsIso (u l E L ι X D hl wE wL) := by
  let K : sfIntegralConstructibleCategory l L X := wL.omega
  let M : sfIntegralConstructibleCategory l L X :=
    ⟨(integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj,
      sfIntegralScalarExtension_constructible D.p l hl E L ι X
        wE.omega.obj wE.omega.property⟩
  let f₀ : ∀ n : ℕ, (scalarReductionDerivedExtension l L X n).obj M.obj ⟶
      (scalarReductionDerivedExtension l L X n).obj K.obj :=
    fun n ↦
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n ≫ (wL.reduction n).inv
  have hf₀ : ∀ {m n : ℕ} (h : n ≤ m),
      f₀ m ≫ normalizedDVRReductionTransition l L X D hl h K.obj =
        normalizedDVRReductionTransition l L X D hl h M.obj ≫
          (normalizedDVRRes l L X h).map (f₀ n) := by
    intro m n h
    simpa only [K, M, f₀] using
      (finiteDualizing_reduction_coherent l E L ι X D hl wE wL h)
  have hfu (n : ℕ) : f₀ n =
      (scalarReductionDerivedExtension l L X n).map
        (u l E L ι X D hl wE wL) := by
    dsimp only [f₀]
    apply (cancel_mono (wL.reduction n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (u_reduction l E L ι X D hl wE wL n).symm
  have hf₀_iso (n : ℕ) : IsIso (f₀ n) := by
    rw [hfu n]
    exact hred n
  let f : ∀ n : ℕ, (scalarReductionDerivedExtension l L X n).obj K.obj ⟶
      (scalarReductionDerivedExtension l L X n).obj M.obj :=
    fun n ↦ letI := hf₀_iso n; inv (f₀ n)
  have hf : ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ normalizedDVRReductionTransition l L X D hl h M.obj =
        normalizedDVRReductionTransition l L X D hl h K.obj ≫
          (normalizedDVRRes l L X h).map (f n) := by
    intro m n h
    let := hf₀_iso m
    let := hf₀_iso n
    apply (cancel_mono ((normalizedDVRRes l L X h).map (f₀ n))).1
    simp only [f, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
    rw [← hf₀ h]
    simp only [IsIso.inv_hom_id_assoc]
    rw [(normalizedDVRRes l L X h).map_id, Category.comp_id]
  obtain ⟨g, hg, huniq⟩ := integralConstructibleReductionHom D l hl L X K M f hf
  have unique_identity (A : sfIntegralConstructibleCategory l L X) :
      ∃! z : A.obj ⟶ A.obj,
        ∀ n : ℕ, (scalarReductionDerivedExtension l L X n).map z = 𝟙 _ := by
    let one : ∀ n : ℕ, (scalarReductionDerivedExtension l L X n).obj A.obj ⟶
        (scalarReductionDerivedExtension l L X n).obj A.obj := fun _ ↦ 𝟙 _
    have hone : ∀ {m n : ℕ} (h : n ≤ m),
        one m ≫ normalizedDVRReductionTransition l L X D hl h A.obj =
          normalizedDVRReductionTransition l L X D hl h A.obj ≫
            (normalizedDVRRes l L X h).map (one n) := by
      intro m n h
      simp only [one, Category.id_comp]
      rw [(normalizedDVRRes l L X h).map_id, Category.comp_id]
    exact integralConstructibleReductionHom D l hl L X A A one hone
  obtain ⟨idK, hidK, huniqK⟩ := unique_identity K
  obtain ⟨idM, hidM, huniqM⟩ := unique_identity M
  have hleft : g ≫ u l E L ι X D hl wE wL = idK := by
    apply huniqK
    intro n
    rw [Functor.map_comp, hg n, ← hfu n]
    dsimp only [f]
    simp only [IsIso.inv_hom_id]
  have hright : u l E L ι X D hl wE wL ≫ g = idM := by
    apply huniqM
    intro n
    rw [Functor.map_comp, ← hfu n, hg n]
    dsimp only [f]
    simp only [IsIso.hom_inv_id]
  have hidK' : (𝟙 K.obj) = idK := by
    apply huniqK
    intro n
    exact (scalarReductionDerivedExtension l L X n).map_id K.obj
  have hidM' : idM = (𝟙 M.obj) := by
    symm
    apply huniqM
    intro n
    exact (scalarReductionDerivedExtension l L X n).map_id M.obj
  refine ⟨⟨g, hright.trans hidM', hleft.trans hidK'.symm⟩⟩
end WeilConjectures.IntegralFiniteExtension
