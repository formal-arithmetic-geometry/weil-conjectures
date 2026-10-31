/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalHomTransport
public import WeilConjectures.WeilSheaf.Localization

/-! # Normalized ordinary exceptional Frobenius action

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final sentence.
(blueprint: lem-sf-native-exceptional-normalized-right-action).
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

/-- The scalar-normalized comparison supplies the ordinary right Frobenius action.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence; scalar_frobenius_counit and its normalization equations.

Proof: use the actual native compactification and its unit-normalized open/proper
forgetting comparison. Its ordinary Frobenius exchange beta is obtained by composing
the open and proper reindexing comparisons. Their unit/counit equations identify the
localized native structure with beta, giving the first displayed square. Transport
the scalar-normalized common-stage compact-support comparison through the closure
isomorphism and section equivalence and lift it through the fully faithful rho to a.
For L, take N to be the ordinary exceptional image of its underlying object. The
invertible mate of the inverse exchange, followed by the image of theta_L, defines v;
ordinary constructibility gives hN. Let w be its adjunction counit. The scalar
Frobenius mate-counit equation is precisely the displayed equation for w. Finally,
for any ordinary identification d, full faithfulness of the closure/section and rho
presentations lifts d to e; the transported adjunction counit formula is the final
normalization equation. This step constructs no derived fixed-pair lift of N.
For an empty scheme N and w are zero; for the identity morphism these are the
original action and identity counit. All normalization maps are invertible, so any
ordinary isomorphism d is allowed in the final clause.
(blueprint: lem-sf-native-exceptional-normalized-right-action). -/
theorem native_exceptional_normalized_right_action (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)) :
    ∃ (a : nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F)
      (beta : counitOrdinaryShriek D l f₀ ⋙
          (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left).mapDerivedCategory ≅
        (WeilSheaf.frobeniusPullback D.k₀ l X.base.left).mapDerivedCategory ⋙
          counitOrdinaryShriek D l f₀),
      (∀ H : W D l X,
        (cyclicDerivedStructure _).hom.app ((nativeShriek D l f₀).obj H).obj ≫
            (counitForgetComparison D l f₀).hom.app H =
          (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left).mapDerivedCategory.map
              ((counitForgetComparison D l f₀).hom.app H) ≫
            beta.hom.app (WeilComplex.forget.obj H) ≫
            (counitOrdinaryShriek D l f₀).map ((cyclicDerivedStructure _).hom.app H.obj)) ∧
      ∀ L : W D l Y,
        ∃ (N : DerivedCategory (ProEtale.AdicSheaf l X.base.hom.geometricFiber))
          (v : (WeilSheaf.frobeniusPullback D.k₀ l X.base.left).mapDerivedCategory.obj N ≅ N)
          (w : (counitOrdinaryShriek D l f₀).obj N ⟶ WeilComplex.forget.obj L),
          ProEtale.DerivedCategory.boundedConstructibleAdic l X.base.hom.geometricFiber N ∧
          beta.hom.app N ≫ (counitOrdinaryShriek D l f₀).map v.hom ≫ w =
            (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left).mapDerivedCategory.map w ≫
              (cyclicDerivedStructure _).hom.app L.obj ∧
          ∀ (H : W D l X) (d : WeilComplex.forget.obj H ≅ N),
            ∃ e : VX.functor.obj H ≅
                (S.ring.operation c .closed).G.obj (VY.functor.obj L),
              ((ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ⋙
                sectionDerived l (geometric D Y).base.left
                  (R.data (geometric D Y)).realization).map
                    ((counitForgetComparison D l f₀).hom.app H ≫
                      (counitOrdinaryShriek D l f₀).map d.hom ≫ w) =
                VY.realization.inv.app ((nativeShriek D l f₀).obj H) ≫
                  (rho D l R Y).map
                    (a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
                      (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L)) ≫
                  VY.realization.hom.app L := by sorry

end WeilConjectures.NativeExceptionalForgetful
