/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalHomTransport

/-! # Graded ordinary exceptional counit bijections

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, graded Hom step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-graded).
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
Postcomposition by the fixed ordinary counit carrier is bijective in every
graded ordinary Hom degree.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence.  Compose the shifted ordinary adjunction bijection with
the fixed comparison and the action-compatible ordinary isomorphism.  Counit
naturality and the shift-counit identity identify its inverse with
`counitHomTransport` followed by the shifted carrier.  The carrier equation
and invariant condition are retained as hypotheses so this statement isolates
only the graded Hom part of the argument.
(blueprint: lem-sf-native-exceptional-ordinary-counit-graded).
-/
theorem native_exceptional_ordinary_counit_graded (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (a : nativeShriek D l f₀ ⋙ VY.functor ≅
      VX.functor ⋙ (S.ring.operation c .closed).F)
    (L : W D l Y) (H : W D l X)
    (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
    (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
      WeilComplex.forget.obj L)
    (ht : ((ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
      sectionDerived l (geometric D Y).base.left
        (R.data (geometric D Y)).realization).map t =
      VY.realization.inv.app ((nativeShriek D l f₀).obj H) ≫
        (rho D l R Y).map (a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
          (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)) ≫
        VY.realization.hom.app L)
    (hinv : (t ≫ (shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L)) ∈
      CyclicDerivedHomInvariants (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
        ((nativeShriek D l f₀).obj H).obj L.obj) :
    ∀ (K : W D l X) (r : ℤ), Function.Bijective
      (fun v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
        K.obj H.obj r ↦ counitHomTransport D l f₀ K H r v ≫ t⟦r⟧') := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
