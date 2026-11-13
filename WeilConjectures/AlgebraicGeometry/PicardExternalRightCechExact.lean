/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechTensorExact
import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechProductExact
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Exactness of the fixed right-coefficient Cech sequences

## References

* Stacks Project, Varieties, Tag 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The two explicitly constructed Cech sequences are short exact.
No cover condition or cohomology comparison is needed (Stacks, Tag 0BED). -/
theorem picardExternal_right_cech_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    : (S.map (picardRightTensorCechFunctor f g U V F)).ShortExact ∧
      (S.map (picardRightProductCechFunctor f g U V F)).ShortExact := by
  constructor
  · exact picardExternal_right_cech_tensor_exact f g U V hU hV F S hS
  · exact picardExternal_right_cech_product_exact f g U V hU hV F S hS

end AlgebraicGeometry.Scheme.Modules
