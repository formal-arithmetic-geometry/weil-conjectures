/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions

import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonFlatness
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparisonBeta
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarProjectionTriangle

/-!  # Derived assertions and projection for a specified finite free resolution -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/-- A specified finite-free short exact point resolution gives the normalized tensor
comparison, its pullback square, and its equality with the actual direct-image mate.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.proof.md, finite free/finitely presented paragraph and
formal properties; parent proof steps 3--7
(blueprint: lem-sfb-finite-free-scalar-derived-comparison).

Proof: exact monoidal point pullback carries the specified short exact sequence to each
scheme. The internal/section tensor equivalence and finite-free mono-cokernel theorem
make its augmented cone a K-flat resolution. On a flat-term K-flat representative Q of
K, tensoring the augmentation is a quasi-isomorphism; the restricted tensor computation
identifies its target with restricted derived scalar extension. Descent gives a natural
beta with the stated ordinary augmentation normalization. Exact geometric pullback
preserves these K-flat representatives, so naturality of the same augmentation gives
the pullback square with the prescribed scalar comparison, using its balancing-arrow
normalization. Transport the scalar and geometric adjunctions to section modules with
their specified units and counits. The ring-sheaf change-adjunction identity identifies
the restricted scalar mate with the O-adjunct of the restricted A-adjunct. Substitute
the pullback square and beta naturality at the geometric counit; the resulting adjunct
is precisely the displayed projection map. This proves equality of the actual arrows,
without claiming invertibility of the projection or of gamma. -/
theorem derivedAssertions_of_finite_integral_resolution
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
    (∀ Z : Scheme.{u}, QuasiIso (augmentation Λ S Z) ∧
      CochainComplex.IsKFlatIndependentCoefficients
        (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
          (.up ℤ)).obj (complex Λ S Z)) ∧
      ∀ C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Z) ℤ,
        IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q (complex Λ S Z) C)) ∧
    ∃ β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z,
      (∀ Z, AugmentationNormalized a S t Z (β Z)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
          (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
        (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
          (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
            ((scalarSixChange a Y).obj K) ≫
          (restriction a X).map ((D.theta a f).inv.app K) =
        tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
          ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
          (β X).hom.app ((scalarSixPull Λ f).obj K)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
          (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
        (β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
          (restriction a Y).map (gamma D a f K) ≫
          (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
          (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K) =
        projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
          (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K) := by
  exact ⟨finiteFreeScalarDerivedComparison_flatness D a S t hS r e₁ e₂,
    finiteFreeScalarDerivedComparison_beta D a S t hS r e₁ e₂⟩

/-- Projection is invertible on the pulled-back cone of a map between finite free
point modules. No exactness of the map or condition on its cokernel is needed.
Source: current scalar-six direct-image proof, finite free/finitely presented paragraph;
parent node step 8, Stacks Tag 0944
(blueprint: lem-sfb-finite-free-scalar-projection).

Proof: the normalized projection transformation, in the coefficient variable, is a
morphism between exact functors, including the connecting map of every triangle, by
the projection-mate exactness theorem transported through the section equivalence.
Its component at the tensor unit is the canonical identity. Additivity gives an
isomorphism at every finite biproduct of the unit. Exact monoidal point pullback
preserves the two given finite free identifications. Apply this transformation to the
cone triangle of S.f[0]; its first two components are invertible, hence its third is
invertible by the triangle two-out-of-three theorem. This third object is the specified
monoCokernelComplex. The scalar-first projection is the conjugate by the canonical
tensor braidings and the point-composition comparison modelPull. Thus its component
is invertible too, including rank zero and arbitrary unbounded K. -/
theorem finiteFreeScalarProjection (Λ : ScalarSixRing.{u})
    (S : ShortComplex (PointModules Λ)) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    IsIso (projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
      (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K) := by
  obtain ⟨T, T', φ, hT, hT', hY, hX, h₁, h₂, hφ⟩ :=
    finiteFreeScalarProjection_triangle Λ S r e₁ e₂ f K
  have h₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ φ hT hT' h₁ h₂
  have h₃' : IsIso (eqToHom hY.symm ≫ φ.hom₃ ≫ eqToHom hX) := by
    infer_instance
  rw [hφ hY hX] at h₃'
  exact h₃'

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
