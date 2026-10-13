/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalAffineRectangleExact

/-! # Transposition of external coefficient sections

Source: Stacks Project, Varieties, Tag 0BED, the right-variable version of the
coefficient diagram following `equation-kunneth-on-cech`.
(blueprint: lem-sc-picard-external-right-rectangle-symmetry).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Transposition of the two factors identifies the right external section functor
with the left external section functor on the transposed rectangle.
Source: Stacks Project, Varieties, Tag 0BED, right-variable coefficient argument
("Arguing in the same fashion for G"), using symmetry of pullback and tensor.
(blueprint: lem-sc-picard-external-right-rectangle-symmetry).

Proof: Let P = X ×_k Y and Q = Y ×_k X. The pullback universal property gives
the transposition isomorphism e : P ≅ Q, with e followed by the first projection
of Q equal to the second projection of P, and similarly for the other projection.
It identifies the rectangle pr₁⁻¹A ∩ pr₂⁻¹B in P with pr₁⁻¹B ∩ pr₂⁻¹A in Q.
For each O_Y-module G, functoriality of module pullback and its compatibility
with tensor identify the pullback along e of pr₁*G ⊗ pr₂*F on Q with
pr₂*G ⊗ pr₁*F on P. The tensor braiding then identifies this with
pr₁*F ⊗ pr₂*G. Take sections on the corresponding rectangles and invert
this composite to obtain the displayed isomorphism of section modules.
The equality of the two structure morphisms to Spec k makes it k-linear.
Pullback composition comparisons, tensor braiding, and section transport along
an isomorphism are all natural in G; composing their naturality equations gives
a natural isomorphism of the two functors. Reversing the transposition and the
braiding gives the inverse. This argument uses no affineness or quasi-coherence
assumption and includes empty opens, empty schemes, and zero coefficients. -/
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
          (pullback.fst g f ⁻¹ᵁ B ⊓ pullback.snd g f ⁻¹ᵁ A))) := by sorry

end AlgebraicGeometry.Scheme.Modules
