/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionFamily
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionRigidity

/-! # Linear changes of coordinates preserve the affine-space counit trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Every invertible linear coordinate change preserves the actual coordinate-tower
counit trace. The existential square is the Cartesian-square certificate for the concrete
polynomial map v ↦ gv; it is not an extra hypothesis on g or a choice of action. -/
theorem affineSpaceLinearTraceInvariance (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    ∃ sq : IsPullback (affineTraceLinearMap S d g) (affineTraceProjection S d)
        (affineTraceProjection S d) (𝟙 S),
      affineLinearTraceAction N hN A hA t S hS d (affineTraceLinearMap S d g) sq ≫
        affineTraceCounit A N hA t D S hS d = affineTraceCounit A N hA t D S hS d  := by
  let sq := affineTraceLinearMap_isPullback S d g
  refine ⟨sq, ?_⟩
  have hcomp := affineLinearAction_family N hN A hA t S hS d
  let r := linearActionMatrix N hN A hA t (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d (linearUniversalMatrix S d)
  have hid : (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r = 𝟙 _ := by
    obtain ⟨C, hC⟩ := hcomp 1
    change (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r ≫ C.hom = _ at hC
    rw [affineLinearAction_one, Category.comp_id] at hC
    apply (cancel_mono C.hom).mp
    simpa only [Category.id_comp] using hC
  have hr : r = 𝟙 _ :=
    linearAction_eq_id_of_identitySection N hN A hA S hS d r hid
  obtain ⟨C, hC⟩ := hcomp g
  change (ordinaryFinitePullback A _).map r ≫ C.hom = _ at hC
  rw [hr, CategoryTheory.Functor.map_id, Category.id_comp] at hC
  have hg : linearActionMatrix N hN A hA t S hS d g = 𝟙 _ := by
    apply (cancel_epi C.hom).mp
    simpa only [Category.comp_id] using hC.symm
  change linearActionMatrix N hN A hA t S hS d g ≫ _ = _
  rw [hg, Category.id_comp]

end AlgebraicGeometry.Etale
