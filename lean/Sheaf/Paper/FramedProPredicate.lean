module

public import Sheaf.Paper.FramedEtaleHom
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.SupportedHomPullback

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-pro-predicate).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Degree-zero pro-etale roots coefficients as a bounded-below derived object.
Source: Stacks 099W, bounded-below site comparison
(blueprint: def-pur-framed-pro-predicate). -/
abbrev divisorProCoefficient (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.frameTwist T 1)

/-- The actual degree-two supported cohomology of the finite positive twist.
Source: Stacks 0A45 and def-pur-support-cohomology
(blueprint: def-pur-framed-pro-predicate). -/
abbrev DivisorProGroup (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :=
  (proEtaleSupportHomPair P i).group (P.divisorProCoefficient T) 2

/-- The normalized supported class in the existing derived Hom model.
Source: Milne 9.4 and normalized supported-Hom comparison
(blueprint: def-pur-framed-pro-predicate). -/
@[irreducible] def divisorProHom (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (χ : (proEtaleSupportHomPair P i).Identification) (c : P.DivisorProGroup i) :
    P.FunctorialCupH true i 2 1 :=
  χ.chi (P.divisorProCoefficient T) 2 c

/-- Realization by every normalized support-Hom identification and canonical site transport.
The root presentation of frameTwist makes this precisely sigma rho after comparison.
Source: Stacks 099W, 0A45 and def-pur-frame-class
(blueprint: def-pur-framed-pro-predicate). -/
@[irreducible] def DivisorProRealizes (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2) (c : P.DivisorProGroup i) : Prop :=
  ∀ χ : (proEtaleSupportHomPair P i).Identification,
    P.divisorProHom i χ c = P.functorialCupCompare i 2 1 (P.divisorEtaleHom i b)



end WeilConjectures.PurityFiniteSetting
