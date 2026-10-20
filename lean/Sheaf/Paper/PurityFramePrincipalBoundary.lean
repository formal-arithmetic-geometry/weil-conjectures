/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.PurityFrameKummer
public import Sheaf.Paper.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# The individual principal-support Kummer boundary

Source: blueprint main-20261015, def-pur-frame-class, the individual closed-open
pair (blueprint: def-pur-frame-principal-boundary). The coefficient short exact
sequence realizes this support boundary by Yoneda composition, before any cup
product or passage to the common zero support.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Extension by zero of the open coefficient unit, followed by its adjunction counit.
Source: def-pur-frame-class, individual closed-open boundary
(blueprint: def-pur-frame-principal-boundary). -/
def frameOpenInclusion (P : PurityFiniteSetting.{u}) {W X : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) ⟶
      P.constant X :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) j).map
      (P.frameConstantPullback j).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) j).counit.app (P.constant X)

/-- The open inclusion followed by restriction to V(f) is zero.
Source: def-pur-frame-class, the individual pair (blueprint: def-pur-frame-principal-boundary).
Proof: an object over the basic open has empty base change to V(f). Restricting its
extension-by-zero section to that empty scheme is zero. The same holds after
sheafification, since extension by zero is the sheafification of this presheaf. -/
theorem frameCoefficientSequence_zero (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    P.frameOpenInclusion (X.basicOpen f).ι ≫
      cupCoefficientRestriction P (X.zeroLocusSubschemeι {f}) = 0 := by
  sorry

/-- The actual coefficient sequence for (X,V(f)); its right map restricts locally
constant functions and its left map is extension by zero followed by the counit.
Source: def-pur-frame-class, support boundary (blueprint: def-pur-frame-principal-boundary). -/
def frameCoefficientSequence (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (f : Γ(X, ⊤)) :=
  ShortComplex.mk (P.frameOpenInclusion (X.basicOpen f).ι)
    (cupCoefficientRestriction P (X.zeroLocusSubschemeι {f}))
    (P.frameCoefficientSequence_zero X f)

/-- This coefficient sequence is short exact on the actual pro-etale site.
Source: def-pur-frame-class, support boundary, and lem-pur-supported-hom Steps 2--4
(blueprint: def-pur-frame-principal-boundary).
Proof: constants are locally constant functions. Restriction to the closed subset
is locally surjective by extending a locally constant section as a constant near
each point, and using zero off the subset. A section in its kernel has clopen
nonzero locus contained in the basic open, hence comes uniquely from extension by
zero. The open counit is monic by that same section description. -/
theorem frameCoefficientSequence_shortExact (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (f : Γ(X, ⊤)) : (P.frameCoefficientSequence X f).ShortExact := by
  sorry

/-- The actual open-adjunction counit after normalized restriction of the twist.
Source: def-pur-frame-class, individual boundary (blueprint: def-pur-frame-principal-boundary). -/
def frameTwistCounit (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
      (P.frameTwist (X.basicOpen f).toScheme 1) ⟶ P.frameTwist X 1 :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).map
      (P.frameTwistPullback (X.basicOpen f).ι a 1).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (X.basicOpen f).ι).counit.app (P.frameTwist X 1)

/-- Exact extension by zero of the concrete Kummer extension, followed by its counit.
Source: def-pur-frame-class, individual boundary (blueprint: def-pur-frame-principal-boundary). -/
def frameOpenKummer (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    Abelian.Ext
      ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
        (P.constant (X.basicOpen f).toScheme)) (P.frameTwist X 1) 1 :=
  ((P.frameKummer (X.basicOpen f).toScheme ((X.basicOpen f).ι ≫ a)
    (X.basicOpenUnit f)).mapExactFunctor
      (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι)).comp
    (Abelian.Ext.mk₀ (P.frameTwistCounit X a f)) (add_zero 1)

/-- The concrete boundary of the Kummer class of f on its basic open. Yoneda
composition with the coefficient extension is the right-derived support boundary:
applying Hom(-,I) to that extension gives kernel-of-restriction sections, and the
connecting map of that short exact complex is the same Ext composition.
Source: def-pur-frame-class, alpha_j (blueprint: def-pur-frame-principal-boundary). -/
def frameBoundary (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι {f})
      ((cupSingle P X).obj (P.frameTwist X 1)) 2 :=
  ((P.frameCoefficientSequence_shortExact X f).extClass.comp
    (P.frameOpenKummer X a f) (rfl : 1 + 1 = 2)).hom

end WeilConjectures.PurityFiniteSetting
