/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatDescentChart
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.AffineOpenDirectedRingSystem
import WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange

/-!
# Tensor-spectrum comparisons for one affine triple

## References

* Stacks Project, Tag 04AI
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- One affine triple admits a ring diagram whose tensor spectra identify the restricted
base changes at every stage and at the limit. The stage source open is exactly the inverse
image of the given source open. No flatness hypothesis or conclusion occurs here
(Stacks, Tags 04AI and 01YW). -/
theorem exists_flat_descent_chart_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFinitePresentation f₀.left]
    (W₀ : (D.obj (op i₀)).Opens) (V₀ : Y₀.left.Opens) (U₀ : X₀.left.Opens)
    (hW : IsAffineOpen W₀) (hV : IsAffineOpen V₀) (hU : IsAffineOpen U₀)
    (hVW : V₀ ≤ Y₀.hom ⁻¹ᵁ W₀) (hUV : U₀ ≤ f₀.left ⁻¹ᵁ V₀) :
    ∃ a : FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩,
      letI := a.sourceAlgebra
      letI := a.targetAlgebra
      (∀ j : {i : I // i₀ ≤ i},
        let q := D.map (homOfLE j.property).op
        let F := ((Over.pullback q).map f₀).left
        let R := a.rings.obj j
        letI := (a.rings.map (homOfLE (show (⟨i₀, le_rfl⟩ : {i : I // i₀ ≤ i}) ≤ j
          from j.property))).hom.toAlgebra
        ∃ (V : ((Over.pullback q).obj Y₀).left.Opens)
          (U : ((Over.pullback q).obj X₀).left.Opens) (h : U ≤ F ⁻¹ᵁ V),
          U = (pullback.fst X₀.hom q) ⁻¹ᵁ U₀ ∧
          Nonempty (Arrow.mk (F.resLE V U h) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom)))) ∧
      (let q := c.π.app (op i₀)
        let F := ((Over.pullback q).map f₀).left
        let R := colimit a.rings
        letI := (colimit.ι a.rings ⟨i₀, le_rfl⟩).hom.toAlgebra
        ∃ (V : ((Over.pullback q).obj Y₀).left.Opens)
          (U : ((Over.pullback q).obj X₀).left.Opens) (h : U ≤ F ⁻¹ᵁ V),
          Nonempty (Arrow.mk (F.resLE V U h) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom)))) := by
  classical
  obtain ⟨F, e0, hi, eL, hL⟩ := exists_affineOpen_ringSystem_of_isLimit D c hc i₀ W₀ hW
  let R := F.obj ⟨i₀, le_rfl⟩
  let B := Γ(V₀.toScheme, ⊤)
  let C := Γ(U₀.toScheme, ⊤)
  let : IsAffine V₀.toScheme := hV
  let : IsAffine U₀.toScheme := hU
  let f := f₀.left.resLE V₀ U₀ hUV
  let q := Y₀.hom.resLE W₀ V₀ hVW ≫ e0.hom
  let aB : R →+* B := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  let aC : R →+* C := f.appTop.hom.comp aB
  let : Algebra R B := aB.toAlgebra
  let : Algebra R C := aC.toAlgebra
  let φ : B →ₐ[R] C := { f.appTop.hom with commutes' := fun _ ↦ rfl }
  have hφ : φ.toRingHom.FinitePresentation := by
    change f.appTop.hom.FinitePresentation
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      f.finitePresentation_appLE (isAffineOpen_top V₀.toScheme)
        (isAffineOpen_top U₀.toScheme) (by simp)
  have hB : V₀.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom aB) = q := by
    change V₀.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
    change q ≫ (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = q
    rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hC : U₀.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
      f ≫ V₀.toScheme.isoSpec.hom := Scheme.isoSpec_hom_naturality f
  let a : FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩ :=
    ⟨F, B, C, aB.toAlgebra, aC.toAlgebra, φ, hφ⟩
  refine ⟨a, ?_, ?_⟩
  · intro j
    let Aj := F.obj j
    let : Algebra R Aj := (F.map
      (homOfLE (show (⟨i₀, le_rfl⟩ : {i : I // i₀ ≤ i}) ≤ j from j.property))).hom.toAlgebra
    obtain ⟨ej, hj⟩ := hi j
    exact affine_triple_tensor_base_change X₀ Y₀ f₀ W₀ V₀ U₀ hVW hUV R B C φ
      e0 V₀.toScheme.isoSpec U₀.toScheme.isoSpec hB hC
      (D.obj (op j.val)) (D.map (homOfLE j.property).op) Aj ej hj
  · let AL := colimit F
    let : Algebra R AL := (colimit.ι F ⟨i₀, le_rfl⟩).hom.toAlgebra
    obtain ⟨V, U, h, _, e⟩ :=
      affine_triple_tensor_base_change X₀ Y₀ f₀ W₀ V₀ U₀ hVW hUV R B C φ
        e0 V₀.toScheme.isoSpec U₀.toScheme.isoSpec hB hC
        c.pt (c.π.app (op i₀)) AL eL hL
    exact ⟨V, U, h, e⟩

end AlgebraicGeometry
