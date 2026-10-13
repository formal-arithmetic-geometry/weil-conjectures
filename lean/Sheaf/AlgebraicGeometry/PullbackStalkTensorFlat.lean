/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.RingTheory.Flat.Basic

/-! # Flatness of the fibre-product stalk over the tensor product of stalks

Source: Stacks Project, Examples, Tag 0FLS; Schemes, Tag 01I4; Algebra, Tag 00HT.
(blueprint: lem-pc-pullback-stalk-tensor-flat).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The canonical tensor-product map to a fibre-product stalk is flat.
Source: Stacks Project, Examples, Tag 0FLS, the paragraph on the canonical stalk map.
(blueprint: lem-pc-pullback-stalk-tensor-flat).

Proof: Choose affine neighbourhoods Spec R₀ of the common image and Spec A₀, Spec B₀
of the two projected points lying over it. Their fibre product is Spec(A₀ ⊗[R₀] B₀).
Its local ring C at x' is the localization at the prime of x'. The rings R, A and B
are the corresponding localizations of R₀, A₀ and B₀. Consequently A ⊗[R] B is
obtained by inverting the elements of A₀ and B₀ outside the two projected primes in
A₀ ⊗[R₀] B₀. All these elements are units in C, so C is a further localization of
A ⊗[R] B. The four equations identify this map with the stipulated algebra map.
Localization is flat. No flatness hypothesis on either scheme morphism is used. -/
theorem pullback_stalk_tensor_flat
    {S T X : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S)
    (x' : ↥(pullback f g))
    [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk ((pullback.fst f g)
      x'))] [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x'))] [Algebra ((X.presheaf.stalk ((pullback.fst f g) x'))
      ⊗[(S.presheaf.stalk (f ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g)
      x'))) ((pullback f g).presheaf.stalk x')]
    (hRA : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk
      ((pullback.fst f g) x')) = (f.stalkMap ((pullback.fst f g) x')).hom)
    (hRB : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x')) =
      (g.stalkMap ((pullback.snd f g) x')).hom.comp (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ : pullback f g ⟶ S => φ x') pullback.condition))).hom.hom)
    (hAC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp (algebraMap (X.presheaf.stalk ((pullback.fst f g) x'))
      ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f ((pullback.fst f g)
      x')))] (T.presheaf.stalk ((pullback.snd f g) x')))) =
      ((pullback.fst f g).stalkMap x').hom)
    (hBC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp
      Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap x').hom)
    : Module.Flat
      ((X.presheaf.stalk ((pullback.fst f g) x'))
        ⊗[S.presheaf.stalk (f ((pullback.fst f g) x'))]
        (T.presheaf.stalk ((pullback.snd f g) x')))
      ((pullback f g).presheaf.stalk x') := by sorry

end AlgebraicGeometry
