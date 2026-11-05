/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarModels
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageColumns
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageScalarShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageShift
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite-free direct-image coefficient coherence

Source: Stacks Project, Tags 0B56 and 0944
(blueprint: lem-sp-finite-free-direct-image-coherence).

All module and derived categories are the existing ones. The auxiliary records bundle
coefficient squares and normalized presentations of the existing scalar functors.
Balancing is the conjugate of the canonical restriction/direct-image comparison, and
its right mate is the specified counit-tensor map. No arbitrary comparison is bound.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem comparison_isIso_app {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    IsIso ((comparison sW sZ a).app M) := by
  obtain ⟨eW, eZ, hcol⟩ := finiteFreeDirectImage_columns q sW sZ R S a d hfree M
  let G := proEtaleRingDerivedDirectImage q R.target R.source R.identification
  let U := (proEtaleRingRestrictScalars a.target).mapDerivedCategory
  let δ := proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let f := (comparison sW sZ a).app M
  have heq : eW.hom ≫ U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M) =
      (Functor.mapBiproduct G (fun _ : Fin d ↦ M)).inv ≫ G.map eZ.hom := by
    apply biproduct.hom_ext'
    intro i
    simpa only [Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
      ← G.map_comp] using hcol i
  have : IsIso (eW.hom ≫ U.map f ≫
      δ.hom.app ((sZ.presentation a.source).derived.obj M)) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map f ≫ δ.hom.app ((sZ.presentation a.source).derived.obj M)) :=
    IsIso.of_isIso_comp_left eW.hom _
  have : IsIso (U.map f) := IsIso.of_isIso_comp_right _
    (δ.hom.app ((sZ.presentation a.source).derived.obj M))
  have : U.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.1
  exact isIso_of_reflects_iso f U

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
