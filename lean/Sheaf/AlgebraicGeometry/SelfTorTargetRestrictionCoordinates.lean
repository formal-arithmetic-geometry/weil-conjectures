/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

public import Sheaf.AlgebraicGeometry.SelfTorAffineSection

public import Sheaf.RingTheory.SelfTorRestrictionCertificate

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification

/-! # Affine Tor coordinates compatible with resolution-induced restriction

Source: Stacks Project, Tags 06YH, 06YG and 00LS.
(blueprint: new-t2-self-tor-target-restriction-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The derived-homology coordinates commute with the actual algebraic Tor restriction
on every Tor element, independently of the exterior-conormal comparison.
Source: Stacks Project, Tags 06YH and 06YG (K-flat comparison), 00LS (resolution
comparison), and 01I6 (associated sheaves).
(blueprint: new-t2-self-tor-target-restriction-coordinates).

Proof: For each affine U, resolve A/I by projective A-modules and sheafify its
augmentation using exists_affine_quotient_sheafified_resolution. Projective terms
are summands of free modules, so their associated sheaves are flat. Extend the
chain complex to nonpositive cochain degrees. It is bounded above and K-flat;
its quotient tensor computes the restriction of the fixed derived tensor.
Exact tilde commutes with homology, and the projective-resolution Tor isomorphism
identifies that homology with tilde Tor. The ideal acts trivially on this homology.
Applying tensor pullback therefore gives the required chart isomorphism t_U.
Use the augmentation comparison, rather than an arbitrary chart isomorphism.
For V=D(f), localize the chosen resolution on U and compare it over the quotient
augmentation with the resolution on V. Flat localization preserves its exactness
and projectivity. The resulting tensor chain map induces q. Comparison lifts for
any other pair of resolutions are homotopic, so q has the displayed certificate
for every P,Q. The K-flat augmentation comparisons commute with this map and
restriction, yielding the equation for every homology class x. The tilde unit
sends x to its associated section; naturality of the tensor-pullback unit then
gives exactly the section equation displayed below. All choices are used only
as existential witnesses in this theorem. Degree zero, the empty basic open,
and zero quotient rings are included by the same augmentation construction. -/
theorem exists_selfTor_target_restriction_coordinates
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
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        ∃ q : (((Tor' (ModuleCat.{u} (Γ(Y, U.1) : Type u)) n).obj
            (ModuleCat.of _ ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).obj
            (ModuleCat.of _ ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))) →
          (((Tor' (ModuleCat.{u} (Γ(Y, V.1) : Type u)) n).obj
            (ModuleCat.of _ ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))).obj
            (ModuleCat.of _ ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))),
          IsSelfTorRestrictionMap (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u)
            (i.ker.ideal U) (i.ker.ideal V) (Y.presheaf.map (homOfLE h).op).hom n q ∧
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
                (((T U).obj _).val.map (homOfLE (i.preimage_mono h)).op
                  (selfTorAffineSection i U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
                (selfTorAffineSection i V _ (q x)) := by sorry

end AlgebraicGeometry
