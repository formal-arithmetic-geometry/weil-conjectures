/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DiagonalCompletedPushSquare
public import Sheaf.Paper.CanonicalDiagonalRightDerived

/-! # Ordinary normalization for completed supported coefficient transport

Source: diagonal tower coefficient changes, initial supported-source identification.
(blueprint: lem-diagonal-completed-supported-transport-normalization).

The theorem below is the ordinary (degree-zero) normalization step in the
transport argument.  It is independent of the derived acyclicity argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The composite ordinary comparison has the support normalization required
by a normalized source.  This is the ordinary part of the proof of
`completedSupportedCoefficient_transport`; the derived square and acyclicity
are handled separately there.

Source: diagonal tower coefficient changes, initial supported-source
identification; the ordinary normalization paragraph of the proof.
Proof: expand the composite, use naturality of the completed realization's
underlying comparison, cancel the coefficient-unit isomorphism, and apply the
normalizations of the input supported source and ordinary square together with
the prescribed normalization of the coefficient isomorphism.
(blueprint: lem-diagonal-completed-supported-transport-normalization). -/
theorem completedSupportedCoefficient_transport_normalization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (a : DiagonalTrace.SupportedSource l Y f R)
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (s : CompletedOrdinarySquare l f eW eP)
    (i : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (hi : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ i.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
          eP.unitIso.hom.hom))) :
    SupportNormalization (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y f
      (eP.unitIso.symm ≪≫ (eP.F.mapIso a.iso) ≪≫
        (s.ordinary.app (diagonalCompletedSource l Y)) ≪≫
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapIso i)) a.over_eq := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
