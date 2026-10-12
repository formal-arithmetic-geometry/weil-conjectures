/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Linearity of the cohomological scalar extension counit

Source: Stacks Project, Tags 06Y6 and 08IB, canonical tensor comparison
(blueprint: lem-pc-base-derived-tensor-counit-linear).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} B)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- The comparison uses the exact restriction-of-scalars homology isomorphism.
/-- Source: Stacks Project, Tags 06Y6 and 08IB, canonical tensor comparison
(blueprint: lem-pc-base-derived-tensor-counit-linear).

Proof: For each a in A, the supplied generator equation shows that ordinaryIso
intertwines multiplication by a: on b tensor q both composites are
(1 tensor b) tensor (a times q), and tensor induction proves equality on all terms.
Naturality of the supplied counit with respect to a times identity then shows that
its cohomology map intertwines the derived A-action with the ordinary A-action.
The homology factorization maps for localization and the homotopy quotient, and
restriction-of-scalars homology isomorphisms, are natural for these endomorphisms.
Compose cohomologyIso.hom, the homology counit, both factorization maps, homology
of ordinaryIso, and the forward restriction-of-scalars homology isomorphism.
Use haction to see that the resulting B-linear map out of cohomology commutes with
multiplication by a tensor 1. It also commutes with 1 tensor b by B-linearity.
Products and sums of pure tensors generate the algebra tensor product, so tensor
induction makes the map E-linear. Bundle it as comparison. Cancellation of the
restriction homology isomorphism gives the displayed equation. This uses no
left-derived universal property or existence of a derived functor or of an action. -/
theorem exists_baseDerivedTensorCounit_linear
    (Q : CochainComplex (ModuleCat.{max uR uA uB v} A) ℤ)
    [(extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).Additive]
    [(extendScalars.{_, _, max uR uA uB v}
      (algebraMap A (A ⊗[R] B))).Additive]
    (ordinaryIso :
      ((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q) ≅
    ((restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex
      (.up ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R]
      B))).mapHomologicalComplex (.up ℤ)).obj Q))
    (ordinaryIso_tmul : ∀ (i : ℤ) (b : B) (q : Q.X i),
      ordinaryIso.hom.f i (b ⊗ₜ[R,algebraMap R B] q) =
        (Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q))
    (derived : DerivedCategory (ModuleCat.{max uR uA uB v} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uB v} B))
    (counit : DerivedCategory.Qh ⋙ derived ⟶
    (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh)
    (cohomology : ℤ → ModuleCat.{max uR uA uB v} (A ⊗[R] B))
    (cohomologyIso : ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
      (cohomology i) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).obj
      (derived.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q)))))
    (haction : ∀ (i : ℤ) (a : A),
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (cohomology i)) ≫
      (cohomologyIso i).hom =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
        (derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).map (a • 𝟙 Q)))))) :
        ∃ (comparison : ∀ i : ℤ, cohomology i ⟶
    (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q).homology i),
          ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
      (comparison i) ≫
      (((((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
         (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)).inv =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
        (counit.app ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{max uR uA uB v} B) i).hom.app
        ((HomotopyCategory.quotient _ _).obj
          (((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex
      (.up ℤ)).obj
            (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{max uR uA uB v} B) (.up ℤ)
      i).hom.app
        (((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex
          (.up ℤ)).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj Q))
      ≫
      HomologicalComplex.homologyMap ordinaryIso.hom i := by sorry

end ModuleCat
