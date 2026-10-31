/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeExceptionalForgetfulData
import WeilConjectures.WeilSheaf.NativeExceptionalOrdinaryCounitModelComparison

/-! # Ordinary exceptional counit comparison

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, first comparison step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The normalized ordinary exceptional comparison exists.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence. First use the canonical-model comparison;
then transport it across the fully faithful realization, using the realization
isomorphisms of the supplied ForgetModels. Full faithfulness makes the
objectwise transports into natural isomorphisms, and whiskering them with the
native exceptional and ordinary functors gives the claimed comparison.
(blueprint: lem-sf-native-exceptional-ordinary-counit-comparison). -/
theorem native_exceptional_ordinary_counit_comparison (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)) :
    Nonempty (nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F) := by
  obtain ⟨model, hmodel⟩ := native_exceptional_ordinary_counit_model_comparison D l R
  let MX := model X
  let MY := model Y
  let ffX : (rho D l R X).FullyFaithful := Classical.choice
    ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
      (R.data (geometric D X)).fully_faithful)
  let ffY : (rho D l R Y).FullyFaithful := Classical.choice
    ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
      (R.data (geometric D Y)).fully_faithful)
  let ix : VX.functor ≅ MX.functor :=
    ffX.whiskeringRight _ |>.preimageIso (VX.realization ≪≫ MX.realization.symm)
  let iy : VY.functor ≅ MY.functor :=
    ffY.whiskeringRight _ |>.preimageIso (VY.realization ≪≫ MY.realization.symm)
  obtain ⟨a⟩ := hmodel X Y f₀ S c
  refine ⟨Functor.isoWhiskerLeft (nativeShriek D l f₀) iy ≪≫ a ≪≫
    Functor.isoWhiskerRight ix.symm (S.ring.operation c .closed).F⟩

end WeilConjectures.NativeExceptionalForgetful
