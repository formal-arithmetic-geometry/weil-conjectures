/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteBetaRepresentative
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomOrdinaryRestrictionChain

/-! # The ordinary site mate on scalar-unit generators -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

set_option maxHeartbeats 0 in
-- The chosen normalized restriction comparison makes kernel checking expensive.
/-- The ordinary mate sends the quotient unit of an inverse-image section to the
inverse image of the etale quotient unit. Source: Stacks 03CZ, 07A4, and blueprint
thm-coef-finite-hom (blueprint: lem-coef-finite-hom-site-beta-unit).
Proof: the unit equation for mates followed by the restriction comparison is the
ordinary etale unit under inverse image. The quotient ordinary_unit equation gives
its section as 1 tensor x. Naturality of the comparison section and the normalized
restriction comparison identify the image; its invertibility cancels it. -/
theorem finiteHomSiteOrdinaryBeta_unit {n m : ℕ} (h : m ≤ n)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    ((finiteHomSiteOrdinaryBeta l E X h).app M).val.app (op (X.toProEt.obj U))
      (coefficientFiniteQuotientUnitSection l E X h
        ((finiteHomNuOrdinary l E X n).obj M) (op (X.toProEt.obj U))
        (finiteHomNuSection l E X n M U x)) =
    finiteHomNuSection l E X m
      ((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).obj M) U
      (((ProEtale.etaleSheafExtendScalarsAdjunction
        (finiteHomQuotient l E h) X).unit.app M).hom.app (op U) x) := by
  let a := ProEtale.etaleSheafExtendScalarsAdjunction (finiteHomQuotient l E h) X
  let b := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus
  let σ := finiteHomNuRestriction l E X h
  let V := op (X.toProEt.obj U)
  have hm := unit_mateEquiv_symm a (b.ordinaryAdjunction h)
    (TwoSquare.mk _ _ _ _ σ.inv) M
  have hu := b.ordinary_unit h ((finiteHomNuOrdinary l E X n).obj M) V
    (finiteHomNuSection l E X n M U x)
  have hn := nuSection_naturalityGeneral X
    (Padic.coefficientExtensionRing l E (n + 1)) (a.unit.app M) U x
  have hσ := (finiteHomNuRestriction_existsUnique l E X h).choose_spec.1
  change FiniteHomNuRestrictionNormalization l E X h σ at hσ
  let y := (a.unit.app M).hom.app (op U) x
  obtain ⟨z, w, hz, hw, he⟩ := hσ (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h)
      X).obj M)) U y
  have hz' : z = finiteHomNuSection l E X m (((ProEtale.etaleSheafExtendScalars
      (finiteHomQuotient l E h) X).obj M)) U y := eq_of_heq hz
  have hw' : w = y := eq_of_heq hw
  subst z w
  have hi := congrArg
    (fun f ↦ f.val.app V (finiteHomNuSection l E X m (((ProEtale.etaleSheafExtendScalars
      (finiteHomQuotient l E h) X).obj M)) U y))
    (σ.hom_inv_id_app (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).obj M)))
  change (σ.inv.app _).val.app V
      ((σ.hom.app _).val.app V
        (finiteHomNuSection l E X m (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h)
      X).obj M)) U y)) =
    finiteHomNuSection l E X m (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h)
      X).obj M)) U y at hi
  have he' := eq_of_heq he
  rw [he'] at hi
  have hb := congrArg
    (fun f ↦ f.val.app V (finiteHomNuSection l E X n M U x)) hm
  change (σ.inv.app _).val.app V
      (((finiteHomNuOrdinary l E X n).map (a.unit.app M)).val.app V
        (finiteHomNuSection l E X n M U x)) =
    ((finiteHomSiteOrdinaryBeta l E X h).app M).val.app V
      (((b.ordinaryAdjunction h).unit.app _).val.app V
        (finiteHomNuSection l E X n M U x)) at hb
  erw [hn] at hb
  change ((b.ordinaryAdjunction h).unit.app _).val.app V
    (finiteHomNuSection l E X n M U x) = _ at hu
  erw [hu] at hb
  exact hb.symm.trans hi

end WeilConjectures
