/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjectionSurjective
import WeilConjectures.AlgebraicGeometry.FormalModuleQuotientAffineProjectionKernel

/-!
# Affine sections of the explicit formal quotient projection

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- On an affine spectrum the actual sheaf quotient projection is surjective and has
kernel the ideal power times the original module. No completeness or finiteness is needed.
(Stacks, Tags 01I8, 01IC and 087W.) -/
theorem formalModuleQuotient_affine_projection
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (m : ℕ) (hm : 0 < m) :
    let p := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (formalModuleQuotientπ J m ((tilde.functor (CommRingCat.of A)).obj M))
    Function.Surjective p ∧ LinearMap.ker p.hom = I ^ m • (⊤ : Submodule A M) := by
  dsimp
  exact ⟨formalModuleQuotient_affine_projection_surjective A I J hJ M m hm,
    formalModuleQuotient_affine_projection_kernel A I J hJ M m hm⟩

end AlgebraicGeometry
