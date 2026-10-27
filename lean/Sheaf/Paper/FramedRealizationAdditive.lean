module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-realization-additive).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Both realizations are additive in the integral extension class.
Source: Stacks 03PL and framed-line refinement, additivity clause
(blueprint: def-pur-framed-realization-additive). -/
@[irreducible] def DivisorRealizationAdditive (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (i : Z ⟶ T) [IsClosedImmersion i],
   P.divisorScalarRealization a i 0 = 0 ∧ P.divisorProRealization a i 0 = 0 ∧
    ∀ β γ, P.divisorScalarRealization a i (β + γ) =
      P.divisorScalarRealization a i β + P.divisorScalarRealization a i γ ∧
      P.divisorProRealization a i (β + γ) =
        P.divisorProRealization a i β + P.divisorProRealization a i γ
end WeilConjectures.PurityFiniteSetting
