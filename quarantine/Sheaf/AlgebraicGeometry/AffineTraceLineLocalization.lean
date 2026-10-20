/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTraceConstruction

/-!
# The affine-line localization triangle in normalized projective coordinates
Source: blueprint sk-prop-an, Step 5(b), detailed affine-space trace steps 2, 3 and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Push the open-closed triangle along the projective-line projection, retaining both
coordinates of the normalized projective-line decomposition.
Source: blueprint lem-amb-affine-space-top-trace, steps 2, 3 and 6
(blueprint: lem-amb-affine-trace-line-localization).

Proof: let i be the infinity section, complementary to the standard affine chart j.
The open-closed triangle on q* K tensor A_P(1)[2] has first arrow the open counit.
Apply the triangulated proper direct-image functor q*. Exactness of finite i*,
composition qi=id, and the Tate inverse-image comparison identify its closed term
with B=K tensor A_S(1)[2]. Tensor the given projective-line decomposition with K
and apply proper projection to obtain b:B biprod K ≅ q* (q* K tensor A_P(1)[2]).
Naturality of projection identifies the open arrow with the displayed one.
Restriction to infinity on the first summand is identity by the inverse-image
adjunction triangle and qi=id. No assertion on the other restriction component is
needed: a triangular change of coordinates removes it in the consumer proof.
The datum's counit normalization and tensor-unit constraints identify the
projective counit with second projection. These arguments use the proper projection
formula on arbitrary complexes and the unbounded open tensor comparison, so no
boundedness hypothesis on K is needed. The zero ring and empty scheme give the zero triangle. -/
theorem affineTraceLine_localization (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (D : OrdinaryFiniteP1Datum A N hA t S hS)
    (K : DerivedCategoryModule A S) :
    let F := ordinaryFinitePushforward A (ProjectiveLine S ↘ S)
    let J := affineTraceOpenAdjunction A S
    let M := (ordinaryFiniteP1Right A N hA S).obj K
    ∃ (B : DerivedCategoryModule A S) (r : F.obj M ⟶ B)
      (w : B ⟶ ((affineTraceLineLeft A S).obj
        ((affineTraceLineRight A N hA S).obj K))⟦(1 : ℤ)⟧)
      (b : B ⊞ K ≅ F.obj M),
      Triangle.mk (F.map (J.counit.app M)) r w ∈ distTriang _ ∧
        biprod.inl ≫ b.hom ≫ r = 𝟙 B ∧ b.hom ≫ D.adjunction.counit.app K = biprod.snd := by
  sorry

end AlgebraicGeometry.Etale
