/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionAssembly
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionObjectwise

/-! # CoherentFormalModulesAffineReconstruction

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Surjective projections with ideal-power kernels reconstruct the formal sheaf system.
This is the formal-system half of the equivalence; no equivalence is assumed.
Source: Stacks Project, Lemma 087W, final quotient computation and the affine
sheaf/module correspondence, Schemes 01I7/01IB. -/
theorem coherentFormalModules_affine_reconstruction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N))
    (p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
    (hnatural : (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))))
    (hquotient : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj)))) :
    Nonempty (L ⋙ (coherentFormalModules_affine_quotientFunctor A I J hJ) ≅ 𝟭 _) := by
  apply coherentFormalModules_affine_reconstruction_assembly A I J hJ L p hnatural hquotient
  exact coherentFormalModules_affine_reconstruction_objectwise A I J hJ L p hquotient

end AlgebraicGeometry
