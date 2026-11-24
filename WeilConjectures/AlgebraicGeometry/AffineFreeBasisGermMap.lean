/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.AffineRegularStalkScalar

/-! # Matrix action on the explicit affine basis germs

## References

* Stacks Project, Tags 01HV, 01IB, 01C6 and 0098
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Sheafifying a linear map sends each actual basis germ to the combination of target
basis germs whose coefficients are the germs of its matrix entries
(Stacks, Tags 01HV, 01IB, 01C6 and 0098). -/
theorem affineFreeBasisGerm_map
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (n m : ℕ)
    (f : ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U))) ⟶
      ModuleCat.of Γ(X, U) (ULift.{0} (Fin m → Γ(X, U)))) (p : Fin n) :
    (affineFreeStalkFunctor X x U hU).map f (affineFreeBasisGerm X x U hxU hU n p) =
      ∑ q, X.presheaf.germ U x hxU ((f (ULift.up (Pi.single p 1))).down q) •
        affineFreeBasisGerm X x U hxU hU m q := by
  classical
  let H := affineFreeStalkFunctor X x U hU
  let a (q : Fin m) := (f (ULift.up (Pi.single p 1))).down q
  have hcomp : affineCoordinateInclusion X U n p ≫ f =
      ∑ q, affineScalarEnd X U (a q) ≫ affineCoordinateInclusion X U m q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hr : (ULift.up (Pi.single p r) : ULift.{0} (Fin n → Γ(X, U))) =
        r • ULift.up (Pi.single p 1) := by
      apply ULift.ext
      change (Pi.single p r : Fin n → Γ(X, U)) = _
      ext j
      by_cases h : j = p <;> simp [h]
    change f.hom (ULift.up (Pi.single p r)) = _
    rw [hr, map_smul]
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, affineCoordinateInclusion, affineScalarEnd, ModuleCat.hom_ofHom,
      LinearMap.coe_mk, AddHom.coe_mk]
    apply (ULift.moduleEquiv (R := Γ(X, U)) (M := Fin m → Γ(X, U))).injective
    rw [map_sum]
    simp only [map_smul, ULift.moduleEquiv_apply]
    change r • (f (ULift.up (Pi.single p 1))).down = ∑ q, Pi.single q (a q * r)
    ext j
    simp [a, mul_comm]
  change H.map f (H.map (affineCoordinateInclusion X U n p)
    (affineRegularStalkGerm X x U hxU hU)) = _
  rw [← ModuleCat.comp_apply, ← H.map_comp, hcomp, H.map_sum]
  change (∑ q, H.map (affineScalarEnd X U (a q) ≫
    affineCoordinateInclusion X U m q)).hom (affineRegularStalkGerm X x U hxU hU) = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [H.map_comp, ModuleCat.comp_apply]
  change H.map (affineCoordinateInclusion X U m q)
    ((affineFreeStalkFunctor X x U hU).map (affineScalarEnd X U (a q))
      (affineRegularStalkGerm X x U hxU hU)) = _
  rw [affineRegularStalkGerm_scalar, map_smul]
  rfl

end AlgebraicGeometry.Scheme
