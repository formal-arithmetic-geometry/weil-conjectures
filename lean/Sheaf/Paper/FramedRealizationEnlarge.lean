module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-realization-enlarge).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Enlarging support restricts the frame and precomposes the realized class.
Source: Stacks 03AJ and 0A45 (blueprint: def-pur-framed-realization-enlarge). -/
@[irreducible] def DivisorRealizationEnlarge (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {Z Z' T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (g : Z ⟶ Z') (hg : g ≫ i' = i) (hW : i'.openComplement ≤ i.openComplement)
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))),
   P.functorialCupChangeSupport false i' i g hg 2 1
        (P.divisorEtaleHom i (P.divisorScalarRealization a i (divisorRelativeExtension i L s))) =
      (P.divisorEtaleHom i' (P.divisorScalarRealization a i'
        (divisorRelativeExtension i' L (divisorRestrictedFrame i i' hW L s)))) ∧
    ∀ (χ : (proEtaleSupportHomPair P i).Identification)
      (χ' : (proEtaleSupportHomPair P i').Identification),
      P.functorialCupChangeSupport true i' i g hg 2 1
          (P.divisorProHom i χ
            (P.divisorProRealization a i (divisorRelativeExtension i L s))) =
        P.divisorProHom i' χ'
          (P.divisorProRealization a i'
            (divisorRelativeExtension i' L (divisorRestrictedFrame i i' hW L s)))
end WeilConjectures.PurityFiniteSetting
