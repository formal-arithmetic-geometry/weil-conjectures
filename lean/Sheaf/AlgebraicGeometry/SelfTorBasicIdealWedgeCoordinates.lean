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

/-! # Self-Tor coordinates on principal affine localizations

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-u4-self-tor-basic-ideal-wedge-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Source and target coordinates agree under principal affine localization on
restrictions of ideal tuples from the larger chart. The input tuple is defined on U,
not on its principal open V. General ideal tuples on V and general affine inclusions
are not asserted here.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-u4-self-tor-basic-ideal-wedge-coordinates).

Proof: For each U = Spec A identify the closed chart with Spec(A/I). Choose an
augmented projective resolution of A/I and sheafify it using
exists_affine_quotient_sheafified_resolution. Exactness of associated-sheaf formation
and the bounded-above flat resolution comparison with the fixed derived tensor give
the target coordinates t_U. The quotient ideal acts by zero on its homology, so
pulling back gives the associated Tor module on the closed chart. For s_U use
affineOpen_kernel_conormal_sections with identity ring coordinates and form its
exterior power, using exteriorSheaf_restrict_iso. Specify these coordinates by the
augmentation and by the pullback-unit equation, respectively, on every affine chart.

Suppose V = D(f) in U and let b be an ideal tuple defined on U. Its inclusion into
O_U gives g:Fin(n) -> I. The Koszul complex on g has its quotient augmentation over A.
Lift it to the projective resolution chosen on U. Tensoring with A/I makes its top
wedge a cycle. The defining normalization selfTorConormalComparison_spec identifies
its homology image with c_U on the conormal wedge of g. Localizing at f is exact,
preserves projective resolutions, and takes this cycle and augmentation to the cycle
and augmentation for g/1 over A_f. Compare the localized projective resolution with
the resolution chosen on V, over the quotient augmentation. The two Koszul lifts are
homotopic, hence have equal homology images. Applying the same normalization over
A_f identifies the latter image with c_V on the restricted conormal tuple.
The sheafified resolution comparison identifies these images in the fixed Q,
compatibly with restriction: it is induced by the localized augmentation and the
K-flat comparison, not an arbitrary homology isomorphism. The source coordinate unit
equations identify the input wedges with these same conormal wedges. This proves
exactly the displayed equality for the restricted global tuple; neither clearing
denominators for an arbitrary ideal tuple on V nor section descent is needed here.
Degree zero uses the empty Koszul wedge, namely the quotient unit. For f=0 both sides
are sections on the empty chart; f=1 uses the identity localization. A zero quotient
gives zero modules. Regularity, finiteness of I, and acyclicity of the Koszul complex
are not assumed. -/
theorem exists_basic_ideal_wedge_selfTor_coordinates
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
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
        (b : Fin n → i.ker.toModules.val.obj (op U.1)),
        (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
            (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ V.1)
              (fun j ↦ η.val.app (op V.1)
                (i.ker.toModules.val.map (homOfLE h).op (b j)))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
            (Scheme.Modules.exteriorSheafSection N n (i ⁻¹ᵁ V.1)
              (fun j ↦ η.val.app (op V.1)
                (i.ker.toModules.val.map (homOfLE h).op (b j)))) := by sorry


end AlgebraicGeometry
