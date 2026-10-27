/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalHomTransport

/-! # Ordinary exceptional counit witness and graded Hom maps

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, ordinary witness and graded Hom steps.
(blueprint: lem-sf-native-exceptional-ordinary-counit-witness).

This statement fixes the comparison isomorphism supplied by the preceding
comparison statement. It contains the remaining ordinary counit carrier,
invariance, and graded Hom bijectivity assertions.
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

/-- The ordinary counit witness associated with a fixed comparison.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence. The scalar-normalized Frobenius mate is
invertible, so cyclic derived action realization supplies a bounded native
object H and an action-compatible ordinary isomorphism e. Its ordinary
counit gives t; the mate-counit identity and zero-shift coherence give the
invariant kernel condition and the transported-arrow equation. In every
integer degree, compose the shifted ordinary adjunction bijection with e and
the fixed transport comparison. Counit naturality and the shift-counit
identity identify its inverse with postcomposition by t, proving bijectivity.
Only ordinary Hom sets are used; no native lift or boundary map is asserted.
(blueprint: lem-sf-native-exceptional-ordinary-counit-witness). -/
theorem native_exceptional_ordinary_counit_witness (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (a : nativeShriek D l f₀ ⋙ VY.functor ≅
      VX.functor ⋙ (S.ring.operation c .closed).F) :
    ∀ L : W D l Y, ∃ (H : W D l X)
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
          ((nativeShriek D l f₀).obj H).obj L.obj ∧
      ∀ (K : W D l X) (r : ℤ), Function.Bijective
        (fun v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
          K.obj H.obj r ↦ counitHomTransport D l f₀ K H r v ≫ t⟦r⟧') := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
