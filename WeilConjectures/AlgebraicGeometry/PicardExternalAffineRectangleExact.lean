/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.PicardExternalAffineRectangleComparison
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Exactness on affine rectangles of the external coefficient

## References

* Stacks Project, Tag 0BED.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The external coefficient, as a functor in the left module. (Stacks, Tag 0BED) -/
def picardExternalCoefficientFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) : X.Modules ⥤ (Limits.pullback f g).Modules :=
  tensorPullback (pullback.fst f g) ⋙
    tensorRight ((tensorPullback (pullback.snd f g)).obj G)

set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient functor preserves zero maps. -/
instance picardExternalCoefficientFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) : (picardExternalCoefficientFunctor f g G).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  unfold picardExternalCoefficientFunctor
  infer_instance

/-- External-coefficient sections on one affine rectangle are short exact in the left
quasi-coherent coefficient. No flatness over the structure sheaf of Y is required.
(Stacks, Tag 0BED) -/
theorem picardExternal_affine_rectangle_exact
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    (S.map (picardExternalCoefficientFunctor f g G ⋙
      picardScalarSectionsFunctor (pullback.fst f g ≫ f)
        (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))).ShortExact := by
  have hs := picardScalar_affine_sections_exact f U hU S hS
  have ht := hs.map_of_exact (tensorRight ((picardScalarSectionsFunctor g V).obj G))
  obtain ⟨e⟩ := picardExternal_affine_rectangle_comparison f g U V hU hV S G
  exact ShortComplex.shortExact_of_iso e ht

end
end AlgebraicGeometry.Scheme.Modules
