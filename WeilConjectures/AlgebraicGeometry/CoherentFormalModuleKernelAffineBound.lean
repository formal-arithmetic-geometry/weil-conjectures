/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.AdicKernelImageBound
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison

/-! # Affine Artin--Rees bound for formal kernel images

Stacks Project, Tag 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On one affine open there is a bound, uniform in the two levels, for the kernel images.
(Stacks, Tag 087X). -/
theorem coherentFormalModule_kernel_affine_bound {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (U : X.affineOpens) :
    ∃ c : ℕ, ∀ (l m : ℕ) (h : m + c ≤ l) (W : X.Opens), W ≤ U.1 →
      Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
        F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)).app W) =
      Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op)).app W) := by
  let A := Γ(X, U.1)
  let R := AdicCompletion (I.ideal U) A
  let J := (I.ideal U).map (algebraMap A R)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (I.ideal U)
  obtain ⟨M, N, f, _, hN, hcompare⟩ :=
    coherentFormalModule_affine_kernel_image_comparison I F H α U
  have : Module.Finite R N := hN
  obtain ⟨c, hc⟩ := LinearMap.adic_kernel_image_bound J f.hom
  refine ⟨c, fun l m h ↦ ?_⟩
  apply (hcompare l (m + c) m (Nat.le_trans (Nat.le_add_right m c) h)
    (Nat.le_add_right m c)).mp
  exact (hc l m h).trans (hc (m + c) m le_rfl).symm

end AlgebraicGeometry
