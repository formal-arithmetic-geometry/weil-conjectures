/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.PicardExternalRectangleSections

/-! # Affine rectangle comparison for external coefficients

## References

* Stacks Project, Tag 0BED.
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

set_option backward.isDefEq.respectTransparency.types true in
/-- External pullback and tensoring preserve zero maps. -/
instance picardExternalRectangleComparison_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) :
    (tensorPullback (pullback.fst f g) ⋙
      tensorRight ((tensorPullback (pullback.snd f g)).obj G)).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  infer_instance

/-- The affine external-section comparison respects both arrows of a short complex.
This statement does not assume exactness of the complex. (Stacks, Tag 0BED) -/
theorem picardExternal_affine_rectangle_comparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    Nonempty
      (((S.map (picardScalarSectionsFunctor f U)).map
        (tensorRight ((picardScalarSectionsFunctor g V).obj G))) ≅
        (S.map ((tensorPullback (pullback.fst f g) ⋙
          tensorRight ((tensorPullback (pullback.snd f g)).obj G)) ⋙
          picardScalarSectionsFunctor (pullback.fst f g ≫ f)
            (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)))) := by
  have hi (F : X.Modules) [F.IsQuasicoherent] :
      IsIso (picardExternalRectangleSectionsMap f g U V F G) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (picardExternalRectangleSectionsMap_bijective f g U V hU hV F G)
  have := hi S.X₁
  have := hi S.X₂
  have := hi S.X₃
  refine ⟨ShortComplex.isoMk
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₁ G))
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₂ G))
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₃ G)) ?_ ?_⟩
  · exact (picardExternalRectangleSectionsMap_naturality f g U V S.f G).symm
  · exact (picardExternalRectangleSectionsMap_naturality f g U V S.g G).symm

end
end AlgebraicGeometry.Scheme.Modules
