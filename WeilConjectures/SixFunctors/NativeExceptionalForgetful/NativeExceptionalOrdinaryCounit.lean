/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalHomTransport
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalOrdinaryCounitWitness

/-! # Ordinary exceptional counit before lifting a native morphism

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, with its native-derived expansion.
(blueprint: lem-sf-native-exceptional-ordinary-counit).
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

/-- Closure transport followed by the specified section-module presentation.
Source: NativeExceptionalForgetfulData.lean, U
(blueprint: lem-sf-native-exceptional-ordinary-counit). -/
def counitOrdinaryTransport (R : Family l D) (X : Space D) :=
  (ProEtale.adicLowerStar l (closureMap D X)).rightDerivedFunctor ⋙
    sectionDerived l (geometric D X).base.left (R.data (geometric D X)).realization

/-- The ordinary adjunction supplies an invariant ordinary counit and bijections in
all ordinary Hom degrees. This statement chooses no native counit morphism and makes
no assertion about invariant subgroups, coinvariant quotients, or their boundary maps.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction sentence; lem-sf-native-exceptional-counit-hom-squares, Steps 1--3, restricted
to the ordinary adjunction and realization of its right-hand action.
(blueprint: lem-sf-native-exceptional-ordinary-counit).

Proof: choose the native compactification of f₀. Compose its unit-normalized
open/proper forgetting comparison with the inverse of the scalar-normalized
compact-support realization. Transport through the closure isomorphisms and exact
section presentations. The fully faithful specified realizations lift the comparison
to the given ForgetModels; refinement identifies it with the specified S and c.
The scalar Frobenius counit theorem gives an invertible mate on the ordinary
exceptional image of VY(L). Apply cyclic derived action realization, retaining the
bounded constructible interval, to obtain H and the action-compatible e. The ordinary
counit carrier t is obtained from F(e) followed by the specified counit, under these
comparison isomorphisms. The mate-counit identity makes t Frobenius invariant; the
canonical zero-shift identification expresses this as the displayed kernel condition.
For each integer r the shifted ordinary adjunction, composed with e[r] and the
canonical shift comparisons, is a bijection. Its inverse formula is precisely
counitHomTransport(v) followed by t[r], by counit naturality and the shift-counit
identity. This argument uses only ordinary Hom sets; it does not lift t to a native
morphism and does not use any cyclic boundary. On empty schemes the ordinary groups
are zero. For identity compactifications the formulas are the adjunction triangle
identities and canonical unitors. -/
theorem native_exceptional_ordinary_counit (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)) :
    ∃ a : nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F,
      ∀ L : W D l Y, ∃ (H : W D l X)
        (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
        (t : WeilComplex.forget.obj ((nativeShriek D l f₀).obj H) ⟶
          WeilComplex.forget.obj L),
        (counitOrdinaryTransport D l R Y).map t =
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
  exact native_exceptional_ordinary_counit_witness D l R X Y VX VY f₀ S c

end WeilConjectures.NativeExceptionalForgetful
