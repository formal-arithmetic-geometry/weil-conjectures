module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
public import Sheaf.Paper.FramedForgetSupport
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-realization-property).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- The normalized supported Kummer realization, with positive ordinary image.
Source: Stacks 03AJ, 03PL and 0A45; blueprint lem-pur-divisor-class, first sentence
and final paragraph (blueprint: def-pur-framed-realization-property). -/
@[irreducible] def DivisorNormalizedRealization (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (i : Z ⟶ T) [IsClosedImmersion i] (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))),
   ∃! b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2,
      P.divisorAbelianRealization i b =
        P.divisorIntegralSplice a i (divisorRelativeExtension i L s) ∧
      P.divisorEtaleForget i b = P.divisorOrdinaryKummer a L ∧
      ∀ χ : (proEtaleSupportHomPair P i).Identification,
        P.divisorProForget i χ
            (P.divisorProRealization a i (divisorRelativeExtension i L s)) =
          P.functorialCupOrdinaryCompare T 2 1 (P.divisorEtaleForgetHom i b)
end WeilConjectures.PurityFiniteSetting
