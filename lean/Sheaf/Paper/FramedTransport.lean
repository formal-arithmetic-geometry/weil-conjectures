module

public import Sheaf.Paper.FramedIntegralExtension
public import Sheaf.Paper.PurityFrameKummer
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-transport).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- The canonical pullback of the specified complementary frame.
Source: Stacks 03AJ, restriction of the Isom torsor
(blueprint: def-pur-framed-transport). -/
def divisorMathlibPulledFrame {Z T Z' T' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T') [IsClosedImmersion i'] (v : T' ⟶ T)
    (hW : i'.openComplement = v ⁻¹ᵁ i.openComplement)
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    (divisorFrameTorsor ((Scheme.Modules.pullback v).obj L)).sheaf.obj.obj
      (op (Scheme.Etale.mk i'.openComplement.ι)) :=
  hW.symm ▸
    (divisorFrameTorsor ((Scheme.Modules.pullback v).obj L)).sheaf.obj.map
      (Etale.openSectionPullback v i.openComplement).op
        (@Scheme.etaleIsoTorsorPullback T' T v L
          (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L)
          (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
            ((Scheme.Modules.pullback v).obj L))
          (op (Scheme.Etale.mk i.openComplement.ι)) s)

/-- Restrict a frame when the closed support is enlarged.
Source: Stacks 0A45, restriction to the smaller complement
(blueprint: def-pur-framed-transport). -/
def divisorRestrictedFrame {Z Z' T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (hW : i'.openComplement ≤ i.openComplement)
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i'.openComplement.ι)) :=
  (divisorFrameTorsor L).sheaf.obj.map
    (MorphismProperty.Over.homMk (T.homOfLE hW) (Scheme.homOfLE_ι T hW)).op s

/-- The positive ordinary Kummer image of the frame torsor.
Source: Stacks 03AJ and 03PL (blueprint: def-pur-framed-transport). -/
def divisorOrdinaryKummer (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (L : T.Modules) [Scheme.Modules.IsInvertible L] :=
  Sheaf.H.map (Etale.ordinaryFiniteRootMap P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T) 2
      (T.kummerδ₁ P.diagonalExponent (P.diagonalExponent_isUnit a)
        (Sheaf.Torsor.classH1 T.gmSheaf
          (MorphismProperty.Over.mkIdTerminal @Etale T) (Quotient.mk _ (divisorFrameTorsor L))))

/-- The adjunction-normalized comparison from tensor pullback to Mathlib pullback.
Source: Stacks 0096, uniqueness of the left adjoint
(blueprint: def-pur-framed-transport). -/
def divisorTensorPullbackComparison {T T' : Scheme.{u}} (v : T' ⟶ T) :
    Scheme.Modules.tensorPullback v ≅ Scheme.Modules.pullback v :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction v)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction v)

/-- Tensor pullback preserves invertibility by the canonical comparison.
Source: Stacks 0096 and local rank-one freeness
(blueprint: def-pur-framed-transport). -/
instance divisorTensorPullbackInvertible {T T' : Scheme.{u}} (v : T' ⟶ T)
    (L : T.Modules) [Scheme.Modules.IsInvertible L] :
    Scheme.Modules.IsInvertible ((Scheme.Modules.tensorPullback v).obj L) :=
  Scheme.Modules.IsInvertible.of_iso ((divisorTensorPullbackComparison v).app L).symm

/-- Transport a frame by a given line-module isomorphism, on the actual Isom torsor.
Source: Stacks 03AJ, Isom torsor construction
(blueprint: def-pur-framed-transport). -/
def divisorMapFrame {T : Scheme.{u}} (L M : T.Modules)
    [Scheme.Modules.IsInvertible L] [Scheme.Modules.IsInvertible M]
    (e : L ≅ M) (W : T.Opens)
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk W.ι))) :
    (divisorFrameTorsor M).sheaf.obj.obj (op (Scheme.Etale.mk W.ι)) :=
  @Scheme.Modules.etaleIsoTorsorMk T M
    (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M) (op (Scheme.Etale.mk W.ι))
    (@Scheme.Modules.etaleIsoTorsorVal T L
      (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L)
      (op (Scheme.Etale.mk W.ι)) s ≫ (Scheme.Modules.pullback W.ι).map e.hom)
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      s.down.2
      (Functor.map_isIso (Scheme.Modules.pullback W.ι) e.hom))

/-- Pull back the frame to the tensor-formula pullback, through the canonical adjunction.
Source: Stacks 03AJ and 0096
(blueprint: def-pur-framed-transport). -/
def divisorPulledFrame {Z T Z' T' : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (i' : Z' ⟶ T') [IsClosedImmersion i'] (v : T' ⟶ T)
    (hW : i'.openComplement = v ⁻¹ᵁ i.openComplement)
    (L : T.Modules) [Scheme.Modules.IsInvertible L]
    (s : (divisorFrameTorsor L).sheaf.obj.obj (op (Scheme.Etale.mk i.openComplement.ι))) :
    (divisorFrameTorsor ((Scheme.Modules.tensorPullback v).obj L)).sheaf.obj.obj
      (op (Scheme.Etale.mk i'.openComplement.ι)) :=
  divisorMapFrame ((Scheme.Modules.pullback v).obj L) ((Scheme.Modules.tensorPullback v).obj L)
    ((divisorTensorPullbackComparison v).app L).symm i'.openComplement
    (divisorMathlibPulledFrame i i' v hW L s)


end WeilConjectures.PurityFiniteSetting
