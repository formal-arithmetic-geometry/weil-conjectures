/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportRoot

/-! # Compatibility of the two root presentations with power transitions

Source: current blueprint, sk-def-sp-tate-twist, the integral inverse system.
(blueprint: lem-pur-integral-root-power-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
open Scheme

private theorem rootComparison_generator (X : Scheme.{u}) (N : ℕ)
    (U : X.ProEtᵒᵖ) (z : (rootsOfUnityPresheaf X N).obj U) :
    (proEtaleRootsOfUnityInclusion X N).hom.app U
      ((rootComparison X N).hom.hom.app U
        ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X N)).app U z)) =
      ULift.up (Additive.ofMul z.down.toMul.val) := by
  have h := (rootComparison_existsUnique X N).exists.choose_spec U z
  have hi := (existsUnique_proEtaleRootsOfUnitySections X N U).exists.choose_spec
    ((rootComparison X N).hom.hom.app U
      ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X N)).app U z))
  change ULift.up (Additive.ofMul
    (proEtaleRootsOfUnitySections X N U _).toMul.val) = _ at hi
  dsimp only [rootComparison, rootsOfUnitySheaf] at h hi ⊢
  rw [h] at hi
  exact hi.symm

/-- The section-normalized root comparison intertwines the actual power transitions.

Source: current blueprint, sk-def-sp-tate-twist, integral inverse system;
Stacks 03PK, the roots-of-unity sheaf.
(blueprint: lem-pur-integral-root-power-compatibility).

Proof: compose with the monic inclusion of the target kernel into the units sheaf.
The kernel-lift equation changes the kernel transition into multiplication by m on
units, since (m*N)/N=m. Morphisms out of the sheafification are determined on
presheaf generators. Naturality of sheafification moves the power map to a root
section. The normalized comparison sends each generator to that same root in the
kernel. Both resulting unit sections are its m-th power. -/
theorem rootComparison_power (X : Scheme.{u}) (N m : ℕ)
    (hN : 0 < N) (hm : 0 < m) :
    (rootComparison X (m * N)).hom ≫
        proEtaleRootsOfUnityTransition X N (m * N) hN (mul_pos hm hN)
          (dvd_mul_left N m) =
      rootsOfUnitySheafPow X N m ≫ (rootComparison X N).hom := by
  have : Mono (proEtaleRootsOfUnityInclusion X N) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion X N)).mp
  have ht : proEtaleRootsOfUnityTransition X N (m * N) hN (mul_pos hm hN)
      (dvd_mul_left N m) ≫ proEtaleRootsOfUnityInclusion X N =
      proEtaleRootsOfUnityInclusion X (m * N) ≫ (m • 𝟙 (proEtaleUnitsSheaf X)) := by
    dsimp only [proEtaleRootsOfUnityTransition, proEtaleRootsOfUnityInclusion]
    rw [kernel.lift_ι, Nat.mul_div_cancel m hN]
  rw [Category.assoc, ht]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _ (proEtaleUnitsSheaf X).property
  ext U z
  have hp := toSheafify_naturality (ProEt.topology X)
    (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow N m))
  have hp' := congrArg (fun f ↦ f.app U z) hp.symm
  change (rootsOfUnitySheafPow X N m).hom.app U
      ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z) =
    (toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X N)).app U
      ((Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
        (CommRingCat.rootsOfUnityPow N m)).app U z) at hp'
  change m • ((proEtaleRootsOfUnityInclusion X (m * N)).hom.app U
      ((rootComparison X (m * N)).hom.hom.app U
        ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z))) =
    (proEtaleRootsOfUnityInclusion X N).hom.app U
      ((rootComparison X N).hom.hom.app U
        ((rootsOfUnitySheafPow X N m).hom.app U
          ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z)))
  rw [hp', rootComparison_generator, rootComparison_generator]
  rfl

end AlgebraicGeometry.ProEtale.PurityTransport
