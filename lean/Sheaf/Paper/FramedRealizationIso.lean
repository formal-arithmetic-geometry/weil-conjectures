module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.FramedProRealization
public import Sheaf.Paper.FramedTransport
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.PurityRelativeCone

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-realization-iso).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- Isomorphisms of framed pairs preserve both the integral extension and its two realizations.
Source: Stacks 03AJ and framed-line refinement, invariance clause
(blueprint: def-pur-framed-realization-iso). -/
@[irreducible] def DivisorRealizationIso (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {Z T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (i : Z ⟶ T) [IsClosedImmersion i] (L M : T.Modules)
    [Scheme.Modules.IsInvertible L] [Scheme.Modules.IsInvertible M]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (t : (divisorFrameTorsor M).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
    (e : Sheaf.Torsor.Iso (divisorFrameTorsor L) (divisorFrameTorsor M))
    (_he : e.iso.hom.hom.app (op (Scheme.Etale.mk i.openComplement.ι)) s = t),
   divisorRelativeExtension i L s = divisorRelativeExtension i M t ∧
    P.divisorScalarRealization a i (divisorRelativeExtension i L s) =
      P.divisorScalarRealization a i (divisorRelativeExtension i M t) ∧
    P.divisorProRealization a i (divisorRelativeExtension i L s) =
      P.divisorProRealization a i (divisorRelativeExtension i M t)
end WeilConjectures.PurityFiniteSetting
