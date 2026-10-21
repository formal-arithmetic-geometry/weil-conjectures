/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.Paper.IntegralModelOpenClosedBasic
import all Sheaf.Paper.ContinuousModuleOpenRestriction
import all Sheaf.Paper.OpenClosedAdjunctionTransport
import all Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.ContinuousModuleEncodingScalarExtension

/-!
# Scalar extension commutes with continuous extension by zero

Source: Stacks Project, Tags 03D7, 03DI and 0E8I
(blueprint: lem-weil-pbc-continuous-extension-scalar-change).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private def extensionRestrictionAdjunction {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousModuleExtensionByZero U T ⊣ continuousRestriction U T := by
  exact openAdjunctionTransport (openSliceEquivalence U T) (continuousRestriction U T)
    (Scheme.proEtaleRingedExtensionByZero U (latticeCoefficientSheaf X T))
    (SheafOfModules.overFunctor (latticeModuleRing X T) U)
    (SheafOfModules.extensionSheafAdjunction (latticeModuleRing X T) U)
    (restrictionToSlice U T)

/-- Extension by zero commutes with any continuous change of the coefficient ring.
Source: Stacks Project, Tags 03D7, 03DI and 0E8I
(blueprint: lem-weil-pbc-continuous-extension-scalar-change).
Proof: take the sheafified tensor left adjoints to scalar restriction on X and U.
The two composites of scalar restriction and restriction to U have identical
section groups, maps and scalar actions. Transport the composite adjunctions
through this identity comparison and use uniqueness of left adjoints. Evaluate
at M; the object equations of the scalar adjunctions identify the resulting
isomorphism with the displayed ordinary changes of rings. This proof needs no
flatness and includes the empty open and zero module. -/
theorem continuousExtension_scalar_change {X : Scheme.{u}} (U : X.ProEt)
    (T S : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (a : T →+* S) (ha : Continuous a)
    (M : SheafOfModules.{u + 1} (latticeModuleRing U.left T)) :
    Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (latticeCoefficientSheafMap X a ha)
        ((continuousModuleExtensionByZero U T).obj M) ≅
      (continuousModuleExtensionByZero U S).obj
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (latticeCoefficientSheafMap U.left a ha) M)) := by
  obtain ⟨FX, hX, ⟨aX⟩⟩ := SheafOfModules.exists_siteChangeOfRingsAdjunction
    (latticeCoefficientSheafMap X a ha)
  obtain ⟨FU, hU, ⟨aU⟩⟩ := SheafOfModules.exists_siteChangeOfRingsAdjunction
    (latticeCoefficientSheafMap U.left a ha)
  let l := (extensionRestrictionAdjunction U T).comp aX
  let r := aU.comp (extensionRestrictionAdjunction U S)
  let RX := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeCoefficientSheafMap X a ha))
  let RU := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeCoefficientSheafMap U.left a ha))
  let d : RX ⋙ continuousRestriction U T ≅ continuousRestriction U S ⋙ RU :=
    NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)))
    (by intro N N' f; ext V x; rfl)
  let e := (l.ofNatIsoRight d).leftAdjointUniq r
  exact ⟨by simpa only [Functor.comp_obj, hX, hU] using e.app M⟩

end AlgebraicGeometry.ProEtale
