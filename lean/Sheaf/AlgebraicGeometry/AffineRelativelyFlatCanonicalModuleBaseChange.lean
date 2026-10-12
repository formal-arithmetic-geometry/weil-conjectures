/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Sheaf.AlgebraicGeometry.BaseChangeMapCech
import Sheaf.AlgebraicGeometry.CechResolution
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Affine computation of relatively flat canonical module base change

Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--5;
Stacks Project, Tag 0A1D, specializing to a module in degree zero.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Over affine bases the canonical module base-change composite is invertible.
Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--5, and Stacks Tag 0A1D.
(blueprint: lem-pc-affine-relatively-flat-canonical-module-base-change).

Proof: choose a finite ordered affine cover of X. Separatedness over Spec A makes
all finite intersections affine. Their modules of sections of G are flat over A
by relative flatness. The finite alternating Cech complex K thus consists of flat
A-modules and is bounded; its sheafification computes Rf_*G. Use the flat-complex
counit comparison to compute Lg^* on this complex by ordinary tensor with B.
For each intersection Spec C, the affine section-pullback isomorphism identifies
Gamma(G, Spec C) tensor_A B with the sections of the pulled-back module on
Spec (C tensor_A B). The pure-tensor formula respects restrictions, so these
isomorphisms commute with the alternating differentials. They identify the tensor
complex with the Cech complex of the pulled-back cover. The Cech characterization
of base change identifies its map with the displayed canonical mate followed by
Rf'_*c. This identifies the map, not merely its source and target. Consequently it
is a composite of isomorphisms. Derived tensor of G[0] has no positive cohomology,
and its degree-zero cohomology is ordinary pullback. A map from it to (p*G)[0]
factors through degree-zero cohomology. Two left-derived counits differ by a natural
automorphism of Lp*, by right Kan extension uniqueness; on degree-zero cohomology
this induces an automorphism of p*G. Thus changing the counit changes c by an
invertible ordinary-target map. Its derived direct image is invertible as well.
For an empty X the empty Cech complex is zero, and the same argument applies.
No flatness over O_X is used. -/
theorem canonicalModuleBaseChange_isIso_affine_of_isFlatOver
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (c : (derivedPullback (pullback.fst f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))
    (hc : IsDerivedModulePullbackComparison (pullback.fst f g) G c) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map c) := by sorry

end AlgebraicGeometry
