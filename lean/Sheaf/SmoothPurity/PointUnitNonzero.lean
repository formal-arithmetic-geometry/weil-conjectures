/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-! # Nonvanishing of the native coefficient unit at a geometric point

Source: the condensed-point equivalence and evaluation of the coefficient ring at a singleton.
(blueprint: lem-pur-geometric-point-unit-nonzero)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem condensed_unit_not_isZero (ℓ : ℕ) [Fact ℓ.Prime] :
    ¬ IsZero (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.padicAlgClRingObj ℓ))) := by
  intro hz
  let C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.padicAlgClRingObj ℓ)
  let S : Profinite.{u} := Profinite.of PUnit.{u + 1}
  have h := hz.eq_of_src (𝟙 (𝟙_ C)) 0
  have h10 := congrArg
    (fun f : (𝟙_ C ⟶ 𝟙_ C) ↦
      f.hom.hom.app (op S)
        (1 : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S))) h
  change (1 : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S)) = 0 at h10
  exact one_ne_zero h10

/-- The native regular condensed coefficient module on a separably closed point is nonzero.

Source: the condensed-point equivalence `isEquivalence_upperStarFromPointMod` and the
finite-intermediate-field-valued coefficient ring construction.
(blueprint: lem-pur-geometric-point-unit-nonzero)

Proof: if the native unit vanished, the monoidal unit comparison and full faithfulness
of pullback from condensed modules would make the condensed regular module vanish.
Its identity would then be zero. Evaluate its underlying sheaf at a singleton and
apply that identity to the constant section one. This gives one equals zero in the
lifted ring of finite-extension-valued continuous functions, a nontrivial ring. -/
theorem not_isZero_unit_on_separablyClosed_point
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    ¬ IsZero (𝟙_ (Mod (Sheaf (ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))) := by
  intro hz
  let F := upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))
  have hF : IsZero (F.obj (𝟙_ _)) :=
    hz.of_iso (Functor.Monoidal.εIso F).symm
  exact condensed_unit_not_isZero ℓ
    (IsZero.of_full_of_faithful_of_isZero F _ hF)

end AlgebraicGeometry.ProEtale.CondensedRing
