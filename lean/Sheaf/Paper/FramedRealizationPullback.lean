module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-realization-pullback).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Etale pullback preserves the framed realization, on both sites.
Source: Stacks 03AJ, 03PL, 0A45 and 099W
(blueprint: def-pur-framed-realization-pullback). -/
@[irreducible] def DivisorRealizationPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {Z T Z' T' : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (v : T' ⟶ T) [Etale v] (g : Z' ⟶ Z) (sq : ChosenCartesianSquare g i' i v)
    (hW : i'.openComplement = v ⁻¹ᵁ i.openComplement)
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))),
   P.functorialCupPullback false i i' v g sq a 2 1
        (P.divisorEtaleHom i (P.divisorScalarRealization a i (divisorRelativeExtension i L s))) =
      (P.divisorEtaleHom i' (P.divisorScalarRealization (v ≫ a) i'
        (divisorRelativeExtension i' ((Scheme.Modules.tensorPullback v).obj L)
          (divisorPulledFrame i i' v hW L s)))) ∧
    ∀ (χ : (proEtaleSupportHomPair P i).Identification)
      (χ' : (proEtaleSupportHomPair P i').Identification),
      P.functorialCupPullback true i i' v g sq a 2 1
          (P.divisorProHom i χ
            (P.divisorProRealization a i (divisorRelativeExtension i L s))) =
        P.divisorProHom i' χ'
          (P.divisorProRealization (v ≫ a) i'
            (divisorRelativeExtension i' ((Scheme.Modules.tensorPullback v).obj L)
              (divisorPulledFrame i i' v hW L s)))
end WeilConjectures.PurityFiniteSetting
