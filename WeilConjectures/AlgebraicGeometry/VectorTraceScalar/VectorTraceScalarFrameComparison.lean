/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameRestriction
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarFrameSource

/-! # Frame descent of the affine scalar trace square

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-scalar-frame-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- On each single specified frame, the scalar square for vector integration follows
from the scalar squares for ordered affine towers.
Source: vector-bundle-purity proof paragraph 2; scalar-descent proof Steps 9--10.
Proof: choose a common Zariski frame cover for F for the two coefficient rings. By
vector-integration normalization, each restricted trace is the specified affine trace
after inverse-frame compact exchange and normalized Tate pullback. The open-restriction
square of compact scalar coherence, pullback compatibility of normalized balancing,
and proper/open scalar exchange identify the restricted scalar map with the affine
one. Refinement coherence removes any choice of compactification. Apply ha to each
frame. This proves equality after the one specified open restriction; it makes
no assertion about detecting global derived morphisms from their restrictions.
The same calculation includes rank zero, zero rings and empty frame opens.
(blueprint: lem-pur-vector-scalar-frame-comparison). -/
theorem frame_scalar_square (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (ha : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
      (d : ℕ), affine φ N hN hA hB T hT d ≫ affineTrace N hN B hB T hT d =
        (scalarExtension φ T).map (affineTrace N hN A hA T hT d) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank r]
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S r F V) :
    (ordinaryFinitePullback B V.ι).map
        (vector φ N hN hA hB S hS r F ≫ vectorBundleIntegration N hN B hB S hS r F) =
      (ordinaryFinitePullback B V.ι).map
        ((scalarExtension φ S).map (vectorBundleIntegration N hN A hA S hS r F) ≫
          unit φ S)   := by
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  rw [frame_scalar_restriction N hN φ hA hB ha S hS r F V e t D]
  exact frame_scalar_source N hN φ hA hB S hS r F V e t D

end AlgebraicGeometry.Etale.VectorTraceScalar
