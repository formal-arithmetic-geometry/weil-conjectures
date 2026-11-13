/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Images

import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-!
# Comparing extended ideal tensor products with categorical images

## References

* Stacks Project, Tags 09NW, 09NX and 01CD
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The image of an adjoint ideal inclusion, multiplied by an invertible module, agrees
with the extended ideal tensor product, compatibly with any linear comparison of the
ambient modules and any change of pullback adjunction.
(Stacks, Tags 09NW, 09NX and 01CD) -/
theorem ideal_tensor_image_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (N : Y.Modules) (P : X.Modules) [P.IsInvertible]
    (adj : tensorPullback f ⊣ pushforward f)
    (e : (tensorPullback f).obj N ≅ P) :
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    let μP := image.ι φ ▷ P ≫ (λ_ P).hom
    let N₁ := (tensorPullback f).obj N
    let μ₁ := (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
    ∃ q : Γ(image μP, ⊤) ≃+ Γ((I.comap f).toModules ⊗ N₁, ⊤),
      ∀ t, μ₁.app ⊤ (q t) =
        (c.app N).hom.app ⊤ (e.inv.app ⊤ ((image.ι μP).app ⊤ t)) := by
  classical
  dsimp only
  let T := tensorPullback f
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let a₀ := Classical.choice (nonempty_tensorPullbackAdjunction f)
  let j := I.subschemeι
  let v := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let φ := (adj.homEquiv I.toModules O).symm (I.toModulesι ≫ v)
  let φ₀ := (a₀.homEquiv I.toModules O).symm (I.toModulesι ≫ v)
  let d := adj.leftAdjointUniq a₀
  have hφ : φ = (d.app I.toModules).hom ≫ φ₀ := by
    dsimp [φ, φ₀]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [← d.hom.naturality_assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  have hker : (pullback.snd j f).ker = I.comap f := by
    calc
      _ = (pullback.fst f j).ker := by
        rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry j f).hom
          (pullback.fst f j), pullbackSymmetry_hom_comp_fst]
      _ = j.ker.comap f := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j f
      _ = I.comap f := congrArg (fun K ↦ K.comap f) I.ker_subschemeι
  have himg₀ : Subobject.mk (I.comap f).toModulesι = imageSubobject φ₀ := by
    have h := (closedSubscheme_baseChange_ideal_image j f).2
    rw [hker, I.ker_subschemeι] at h
    simpa only [φ₀, a₀, Adjunction.homEquiv_naturality_left_symm] using h
  have himg : Subobject.mk (image.ι φ) = Subobject.mk (I.comap f).toModulesι := by
    change imageSubobject φ = _
    rw [hφ, imageSubobject_iso_comp]
    exact himg₀.symm
  let k : image φ ≅ (I.comap f).toModules :=
    Subobject.isoOfMkEqMk (image.ι φ) (I.comap f).toModulesι himg
  have hk : k.hom ≫ (I.comap f).toModulesι = image.ι φ := by
    simp [k]
  let μP := image.ι φ ▷ P ≫ (λ_ P).hom
  have : Mono μP := inferInstance
  let N₁ := T.obj N
  let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction f))
  let h : P ≅ N₁ := e.symm ≪≫ c.app N
  let b : image φ ⊗ P ≅ (I.comap f).toModules ⊗ N₁ := k ⊗ᵢ h
  let q₀ : image μP ≅ (I.comap f).toModules ⊗ N₁ := imageMonoIsoSource μP ≪≫ b
  let μ₁ := (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
  have hb : b.hom ≫ μ₁ = μP ≫ h.hom := by
    change (k.hom ⊗ₘ h.hom) ≫ (I.comap f).toModulesι ▷ N₁ ≫ (λ_ N₁).hom =
      (image.ι φ ▷ P ≫ (λ_ P).hom) ≫ h.hom
    rw [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← comp_whiskerRight_assoc, hk]
    change image.ι φ ▷ P ≫ (𝟙_ X.Modules) ◁ h.hom ≫ (λ_ N₁).hom = _
    rw [leftUnitor_naturality]
    simp only [Category.assoc]
  have hq : q₀.hom ≫ μ₁ = image.ι μP ≫ h.hom := by
    dsimp only [q₀, Iso.trans_hom]
    rw [Category.assoc, hb, imageMonoIsoSource_hom_self_assoc]
  let q := ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso q₀).toLinearEquiv
    |>.toAddEquiv
  refine ⟨q, ?_⟩
  intro t
  exact congrArg (fun a ↦ a.app ⊤ t) hq


end AlgebraicGeometry.Scheme.Modules
