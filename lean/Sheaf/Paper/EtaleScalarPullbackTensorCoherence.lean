/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalCoefficientMaps

/-! # Tensor compatibility of the normalized scalar/pullback comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Binary scalar/pullback tensor coherence with categorical parameters shared.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-pullback-tensor-coherence). -/
def ScalarPullbackTensorLaw
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    (Q : C ⥤ D) (Q' : E ⥤ F) (L : C ⥤ E) (L' : D ⥤ F)
    (a : Q ⋙ L' ≅ L ⋙ Q')
    (dQ : Functor.uncurry.obj (curriedTensor C) ⋙ Q ≅
      Q.prod Q ⋙ Functor.uncurry.obj (curriedTensor D))
    (dQ' : Functor.uncurry.obj (curriedTensor E) ⋙ Q' ≅
      Q'.prod Q' ⋙ Functor.uncurry.obj (curriedTensor F))
    (dL : ∀ P R : C, L.obj (P ⊗ R) ≅ L.obj P ⊗ L.obj R)
    (dL' : ∀ P R : D, L'.obj (P ⊗ R) ≅ L'.obj P ⊗ L'.obj R) : Prop :=
  ∀ P R, a.hom.app (P ⊗ R) ≫ Q'.map (dL P R).hom ≫
      dQ'.hom.app (L.obj P, L.obj R) =
    L'.map (dQ.hom.app (P, R)) ≫ (dL' (Q.obj P) (Q.obj R)).hom ≫
      (a.hom.app P ⊗ₘ a.hom.app R)

/-- The normalized scalar/pullback isomorphism respects the binary tensor comparison.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-coherence).
Proof: choose flat K-flat representatives P and Q. Pullback preserves flat K-flat
complexes, and scalar extension on these models is ordinary extension of scalars.
Use the defining scalar/pullback representative square and the defining tensor
representative squares for scalar extension and geometric pullback. On a pair
of homogeneous local pure tensors, both composites send
((p tensor q) tensor b) to (f*p tensor b) tensor (f*q tensor 1).
The ordinary balancing relations identify any alternative distribution of b.
The total-complex maps use the same pair of degrees and the same Koszul sign,
so these equalities commute with both differentials. Sheafification preserves
this equality of the balanced morphisms. The representative maps for the chosen
models are invertible, so cancellation gives the displayed equality on the
localized models. Naturality and flat K-flat resolutions in both variables
extend it to arbitrary derived P and Q. This uses no flatness of the coefficient
map, no boundedness, and no properness of f. -/
theorem etaleScalarPullback_tensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ScalarPullbackTensorLaw (scalarExtension φ Y) (scalarExtension φ X)
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
      (scalarPullbackIso φ f) (ExceptionalCoefficients.tensorIso φ Y)
      (ExceptionalCoefficients.tensorIso φ X)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) f) := by
  sorry

end AlgebraicGeometry.Etale
