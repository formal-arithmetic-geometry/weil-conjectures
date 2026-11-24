/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.BaseChangeDimensionExtension
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Base change of a curve

Base change of a curve along an extension of algebraically closed fields.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a curve along an extension of algebraically closed fields preserves the
curve structure, dimension, and the listed geometric properties (Stacks, Tags 00OY, 00GU). -/
theorem baseChange_curve {k k' : Type u} {C : Scheme.{u}} [Field k] [Field k'] [Algebra k k']
    [IsAlgClosed k] [IsAlgClosed k'] (f : C ⟶ Spec (.of k)) [IsCurve f] :
    IsCurve (CategoryTheory.Limits.pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      topologicalKrullDim (CategoryTheory.Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) =
        topologicalKrullDim C ∧
      (Smooth f → Smooth (CategoryTheory.Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) ∧
      (IsProper f → IsProper (CategoryTheory.Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) ∧
      (IsAffine C → IsAffine (CategoryTheory.Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) ∧
      (IsConnectedCurve f → IsConnectedCurve (CategoryTheory.Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) := by
  have hdim := baseChange_dim (k' := k') f
  have hcurve : IsCurve (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    { krullDim_le_one := hdim.trans_le (IsCurve.krullDim_le_one (f := f)) }
  refine ⟨hcurve, hdim, ?_, ?_, ?_, ?_⟩
  · intro hf
    exact smooth_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f _) hf
  · intro hf
    exact IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f _) hf
  · intro hC
    let : IsAffine C := hC
    let : IsAffineHom f := inferInstance
    infer_instance
  · intro hf
    let : IsConnectedCurve f := hf
    let : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
    let : GeometricallyConnected f :=
      GeometricallyConnected.of_connectedSpace_of_isSepClosed f
    exact
      { toIsCurve := hcurve
        connectedSpace := GeometricallyConnected.connectedSpace_of_subsingleton
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
        krullDim_eq_one := hdim.trans (IsConnectedCurve.krullDim_eq_one (f := f)) }

end AlgebraicGeometry
