/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso

/-! # Normalized self-Tor coordinates on wedges of affine ideal sections

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e3-self-tor-ideal-wedge-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The normalized chart comparisons agree on wedges of ideal sections from the smaller
ambient affine chart. The entries here must come from the pullback unit; arbitrary
conormal sections are not included.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e3-self-tor-ideal-wedge-coordinates).

Proof: On U = Spec A identify the closed chart with Spec(A/I). Choose a projective
resolution of A/I with its augmentation and sheafify it using
exists_affine_quotient_sheafified_resolution. The bounded-above flat cochain complex is
K-flat, so comparison with the fixed derived tensor identifies its quotient-tensored
homology with Q on the closed chart. The quotient ideal annihilates this homology,
which gives the target coordinates. For the source coordinates apply
affineOpen_kernel_conormal_sections with identity ring coordinates: each ideal section
maps to its conormal class under the pullback unit. Exterior powers and open restriction
then give the source coordinates. Make these choices on every chart.
For V contained in U, cover V by principal opens of U contained in V and refine by
principal opens of V. Localize both augmented resolutions on each refinement; flat
localization preserves homology. The tuple b is a tuple of actual ideal sections on V,
so its restrictions give the same ideal elements in both localized coordinates.
Lift its Koszul augmentation to the projective resolutions. The normalization of
selfTorConormalComparison identifies the image of the wedge cycle with the algebraic
comparison on its conormal classes. Resolution comparison and homotopy independence
identify these homology classes in Q. The source coordinates preserve the unit, hence
the two chart maps have equal values on the displayed wedge on every refinement.
Separatedness of Q gives equality on the full inverse image of V. There is no need to
lift arbitrary conormal sections here. In degree zero the cycle is the quotient unit;
the empty chart and the zero quotient give the unique section. No regularity or Koszul
acyclicity is assumed. -/
theorem exists_ideal_wedge_selfTor_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let E := Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let c := fun U : Y.affineOpens ↦
      selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ (s : ∀ U : Y.affineOpens,
        E.over (i ⁻¹ᵁ U.1) ≅ ((T U).obj _).over (i ⁻¹ᵁ U.1))
      (t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
      let φ := fun U ↦ (s U).hom ≫ ((T U).map (c U)).over (i ⁻¹ᵁ U.1) ≫ (t U).hom
      let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
      let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (b : Fin n → i.ker.toModules.val.obj (op V.1)),
        (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
            (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ V.1)
              (fun j ↦ η.val.app (op V.1) (b j))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
            (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ V.1)
              (fun j ↦ η.val.app (op V.1) (b j))) := by sorry

end AlgebraicGeometry
