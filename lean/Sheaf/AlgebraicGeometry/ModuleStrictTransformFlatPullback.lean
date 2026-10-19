/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.ModuleStrictTransform

/-!
# Flat pullback of module strict transforms

Source: Stacks Project, Divisors, Tags 080D, 0805 and 080F; Flatness, Tag 0814,
proof paragraph 1; Properties, Tag 07ZP
(blueprint: lem-trf-module-strict-transform-flat-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The map `jᵇ` induced by the square and the specified flat blowup comparison.
The first projection of the upstream comparison is the map to the old blowup;
its second projection is the blowup map over `T`.
Source: Stacks, Tags 0805 and 080D
(blueprint: lem-trf-module-strict-transform-flat-pullback). -/
noncomputable def moduleStrictTransformFlatPullbackMap {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] (I : S.IdealSheafData) :
    Limits.pullback g (I.comap e).blowupMap ⟶ Limits.pullback f I.blowupMap :=
  pullback.lift (pullback.fst g (I.comap e).blowupMap ≫ j)
    (pullback.snd g (I.comap e).blowupMap ≫
      (I.blowupFlatBaseChangeIso e).hom ≫ pullback.fst I.blowupMap e)
    (by
      simp only [Category.assoc, h, pullback.condition]
      rw [← Category.assoc (I.blowupFlatBaseChangeIso e).hom
        (pullback.snd I.blowupMap e) e, I.blowupFlatBaseChangeIso_hom_snd e]
      exact congrArg (fun k ↦ k ≫ e)
        (pullback.condition (f := g) (g := (I.comap e).blowupMap)))

/-- The canonical comparison between the ordinary iterated pullbacks.
It uses the section-normalized composition isomorphisms, and the first-projection
identity of the explicitly constructed `jᵇ`.
Source: Stacks, Tag 080D, and Sheaves, Tag 0097
(blueprint: lem-trf-module-strict-transform-flat-pullback). -/
noncomputable def moduleStrictTransformFlatPullbackSourceIso {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] (I : S.IdealSheafData) (F : X.Modules) :
    (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).obj
        ((tensorPullback (pullback.fst f I.blowupMap)).obj F) ≅
      (tensorPullback (pullback.fst g (I.comap e).blowupMap)).obj
        ((tensorPullback j).obj F) :=
  (tensorPullbackSectionComp (moduleStrictTransformFlatPullbackMap f e g j h I)
    (pullback.fst f I.blowupMap)).symm.app F ≪≫
  (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F)
    (pullback.lift_fst _ _ _))) ≪≫
  (tensorPullbackSectionComp (pullback.fst g (I.comap e).blowupMap) j).app F

/-- Strict transform commutes with flat source and base pullback, uniquely compatibly
with the quotient maps from the ordinary pullbacks. The target cokernel is exactly
`moduleStrictTransform g (I.comap e) ((tensorPullback j).obj F)` unfolded: using the
cokernel expression avoids requiring finite-type and quasi-coherence instances as
extra hypotheses for the transported objects.
Source: Stacks, Tags 080D, 0805, 080F, 0814 (proof paragraph 1), and 07ZP
(blueprint: lem-trf-module-strict-transform-flat-pullback).

Proof: (1) The flat blowup comparison identifies the new blowup with the base change
of the old one. Fibre-product associativity identifies `jᵇ` with the base change of `j`,
so it is flat. The exceptional locus on its source is the inverse image of that on
its target, since extension of an ideal commutes with its vanishing locus.
(2) Write the strict transforms as quotients of the ordinary pullbacks by their
supported-section kernels, using def-trf-module-strict-transform and
lem-trf-strict-transform-sheaf-kernel. The normalized composition comparisons give
`moduleStrictTransformFlatPullbackSourceIso` between the ordinary pullbacks.
(3) Principalization of the blowup centre gives affine charts with exceptional locus
`V(a)`. On these charts supported sections are precisely the a-power torsion, by
lem-weil-pbc-affine-module-basic-open-localization. The affine pullback-sections
bijection identifies pullback with tensor product. Flat tensor exactness identifies
the pulled-back kernel with the power-torsion kernel after base change: tensor the
exact sequence from a-power torsion into M and then M localized at a; localization
commutes with tensor. Equality on this affine basis gives equality of the sheaf kernels.
(4) Pullback is a left adjoint, hence preserves cokernels. The kernel identification
therefore induces an isomorphism of the two cokernels with the displayed quotient
identity. The pulled-back quotient is epi, so this identity determines the isomorphism
uniquely, giving canonicity. -/
theorem existsUnique_moduleStrictTransform_flatPullback {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (e : T ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X)
    (h : j ≫ f = g ≫ e) [Flat e] [Flat j]
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃! θ : (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).obj
        (moduleStrictTransform f I F) ≅
      cokernel (kernel.ι
        (moduleStrictTransformRestriction g (I.comap e) ((tensorPullback j).obj F))),
      (tensorPullback (moduleStrictTransformFlatPullbackMap f e g j h I)).map
          (moduleStrictTransformπ f I F) ≫ θ.hom =
        (moduleStrictTransformFlatPullbackSourceIso f e g j h I F).hom ≫
          cokernel.π (kernel.ι
            (moduleStrictTransformRestriction g (I.comap e) ((tensorPullback j).obj F))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
