/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalAffineRectangleExact
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.ScalarSectionsIsoTransport

/-! # Transposition of external coefficient sections

## References

* Stacks Project, Varieties, Tag 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensorRight_pullback_iso {P Q : Scheme.{w}} (a : P ⟶ Q)
    (N : Q.Modules) :
    Nonempty (tensorRight N ⋙ tensorPullback a ≅
      tensorPullback a ⋙ tensorRight ((tensorPullback a).obj N)) := by
  obtain ⟨e, hn, hs⟩ := module_pullback_tensor a
  refine ⟨NatIso.ofComponents (fun M ↦ e M N) ?_⟩
  intro M M' φ
  simpa using hn M N M' N φ (𝟙 N)

/-- Transposition of the two factors identifies the right external section functor
with the left external section functor on the transposed rectangle (Stacks, Tag 0BED). -/
theorem picardExternal_right_rectangle_symmetry
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (A : X.Opens) (B : Y.Opens) (F : X.Modules) :
    Nonempty ((tensorPullback (pullback.snd f g) ⋙
        tensorLeft ((tensorPullback (pullback.fst f g)).obj F) ⋙
        picardScalarSectionsFunctor (pullback.fst f g ≫ f)
          (pullback.fst f g ⁻¹ᵁ A ⊓ pullback.snd f g ⁻¹ᵁ B)) ≅
      (picardExternalCoefficientFunctor g f F ⋙
        picardScalarSectionsFunctor (pullback.fst g f ≫ g)
          (pullback.fst g f ⁻¹ᵁ B ⊓ pullback.snd g f ⁻¹ᵁ A))) := by
  let e := pullbackSymmetry f g
  let N := (tensorPullback (pullback.snd g f)).obj F
  let E := picardExternalCoefficientFunctor g f F
  let T := tensorPullback e.hom
  let C := tensorPullback (pullback.snd f g)
  let M := (tensorPullback (pullback.fst f g)).obj F
  let c₁ : C ≅ tensorPullback (pullback.fst g f) ⋙ T :=
    tensorPullbackCompositionIso e.hom (pullback.fst g f) (pullback.snd f g)
      (pullbackSymmetry_hom_comp_fst f g)
  let c₂ : tensorPullback (pullback.fst f g) ≅ tensorPullback (pullback.snd g f) ⋙ T :=
    tensorPullbackCompositionIso e.hom (pullback.snd g f) (pullback.fst f g)
      (pullbackSymmetry_hom_comp_snd f g)
  obtain ⟨t⟩ := tensorRight_pullback_iso e.hom N
  let d : E ⋙ T ≅ C ⋙ tensorRight M :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c₁.symm _ ≪≫
      Functor.isoWhiskerLeft C ((tensoringRight _).mapIso (c₂.app F).symm)
  let W := pullback.fst g f ⁻¹ᵁ B ⊓ pullback.snd g f ⁻¹ᵁ A
  have hs : e.hom ≫ (pullback.fst g f ≫ g) = pullback.fst f g ≫ f := by
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullback.condition.symm
  have hW : e.hom ⁻¹ᵁ W = pullback.fst f g ⁻¹ᵁ A ⊓ pullback.snd f g ⁻¹ᵁ B := by
    dsimp [W, e]
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
      pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd, inf_comm]
  obtain ⟨s⟩ := scalarSections_iso_transport e (pullback.fst g f ≫ g) W
  rw [hs, hW] at s
  let S := picardScalarSectionsFunctor (pullback.fst f g ≫ f)
    (pullback.fst f g ⁻¹ᵁ A ⊓ pullback.snd f g ⁻¹ᵁ B)
  exact ⟨Functor.isoWhiskerRight (Functor.isoWhiskerLeft C
      (BraidedCategory.tensorLeftIsoTensorRight M)) S ≪≫
    Functor.isoWhiskerRight d.symm S ≪≫ Functor.associator E T S ≪≫ Functor.isoWhiskerLeft E s⟩

end AlgebraicGeometry.Scheme.Modules
