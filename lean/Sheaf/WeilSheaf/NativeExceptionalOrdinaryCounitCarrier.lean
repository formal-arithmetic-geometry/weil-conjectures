/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalHomTransport

/-! # Ordinary exceptional counit carrier

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, carrier and invariance steps.
(blueprint: lem-sf-native-exceptional-ordinary-counit-carrier).
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

/--
The ordinary scalar counit construction supplies its carrier and its invariant
zero-shift equation for a fixed comparison and a fixed target object.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence.  Choose the scalar-normalized Frobenius mate, realize its
invertible action by a bounded fixed-pair complex, and transport the ordinary
adjunction counit through the comparison and the action-compatible isomorphism.
The mate-counit identity gives the transported-arrow equation; the zero-shift
coherence gives the displayed invariant condition.  This is the carrier part
of the ordinary witness and does not assert graded Hom bijectivity.
(blueprint: lem-sf-native-exceptional-ordinary-counit-carrier).
-/
theorem native_exceptional_ordinary_counit_carrier (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (a : nativeShriek D l f₀ ⋙ VY.functor ≅
      VX.functor ⋙ (S.ring.operation c .closed).F)
    (L : W D l Y) :
    ∃ (H : W D l X)
      (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
      (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
        WeilComplex.forget.obj L),
      ((ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
        sectionDerived l (geometric D Y).base.left
          (R.data (geometric D Y)).realization).map t =
        VY.realization.inv.app ((nativeShriek D l f₀).obj H) ≫
          (rho D l R Y).map (a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
            (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)) ≫
          VY.realization.hom.app L ∧
      (t ≫ (shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L)) ∈
        CyclicDerivedHomInvariants (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
          ((nativeShriek D l f₀).obj H).obj L.obj := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
