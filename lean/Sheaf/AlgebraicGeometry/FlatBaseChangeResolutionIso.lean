/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Invertibility of the resolution-defined flat base-change map

Source: Stacks Project, Tag 02KH, part (1).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- The actual resolution-defined comparison is invertible for qcqs direct image
of a quasi-coherent module, for every augmented comparison lift.
Source: Stacks Project, Tag 02KH, part (1), using the map of Tag 02N7.
(blueprint: lem-weil-pbc-flat-base-change-resolution-iso)

Proof: Work locally on the two bases, reducing to a flat map of affine rings A → B.
On a finite affine cover of the qcqs source use the Cech-to-cohomology spectral
sequence. Intersections are quasi-compact separated, so their cohomology is computed
by finite affine Cech covers. Base change of their sections is tensor with B and
flat tensor commutes with cohomology. It therefore identifies the spectral sequences
and their abutments. Quasi-coherence of the higher direct images identifies the
result with the sheaf comparison. The comparison is the resolution-defined map:
its augmented lift induces the unit on cocycles, as in 02N7; different augmented
lifts are homotopic and induce the same map. Thus every displayed beta is invertible.
The argument includes degree zero, a zero module, and an empty source. -/
theorem Scheme.Modules.flatBaseChangeResolutionBeta_isIso
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((Scheme.Modules.pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (pullback.snd g f))).unit.app F ≫
          (Scheme.Modules.pushforward (pullback.snd g f)).map (J.ι.f 0)) (p : ℕ) :
    IsIso (Scheme.Modules.flatBaseChangeResolutionBeta f g I J t p) := by sorry

end AlgebraicGeometry
