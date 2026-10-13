/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import Sheaf.RingTheory.KoszulProjectiveResolution
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.AlgebraicGeometry.AffineConormalFrame
import Sheaf.RingTheory.KoszulConormalBasis
import Sheaf.RingTheory.KoszulGeneratorChainMap

/-! # Alignment of local Koszul identifications

Source: Stacks Project, Tag 0BQY, comparison of regular generators. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry



/-- Local isomorphisms can be adjusted by automorphisms of the source so that
all their components agree on overlaps.

Source: Stacks Project, Tag 0BQY, change of generators in the Koszul resolution.
(blueprint: new-w4-koszul-self-ext-local-alignment).

Proof: On each regular chart use the normalized Koszul Hom coordinate map.
On intersections refine by affine subopens around each point. The conormal
bases over its nonzero local ring have equal length; shrink so that a generator
substitution is invertible modulo the ideal. Empty intersections need no check.
A substitution between the two regular generator sets induces a chain map by
exterior powers in every degree.
The contraction identity checks the chain equation. Modulo the immersion ideal
its exterior powers are the conormal coordinate changes, whose duals are precisely
the Hom coordinate changes. Resolution comparison homotopies remove the choices
of substitutions, and localization preserves the formulas. Separatedness gives
agreement on every smaller open. Thus normalized comparisons glue, together with
their inverses, on each of the supplied neighborhoods. Comparing a supplied local
isomorphism e_z with the glued normalized one c_z gives the source automorphism
a_z = c_z followed by e_z.inv; its composite with e_z.hom is c_z.hom by the
inverse identity. This proves the asserted overlap
identities without assuming that arbitrary local isomorphisms already agree.
The empty scheme imposes no conditions, and degree zero uses the quotient unit. -/
theorem koszulRegularImmersion_self_ext_conormal_local_alignment
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∀ (W : V.toScheme → V.toScheme.Opens)
      (e : ∀ z : V.toScheme, F.over (W z) ≅ T.over (W z)),
      (∀ z : V.toScheme, z ∈ W z) →
      ∃ a : ∀ z : V.toScheme, F.over (W z) ≅ F.over (W z),
        ∀ (x y : V.toScheme) (U : V.toScheme.Opens)
          (hx : U ≤ W x) (hy : U ≤ W y),
          ((a x).hom ≫ (e x).hom).val.app (op (Over.mk (homOfLE hx))) =
            ((a y).hom ≫ (e y).hom).val.app (op (Over.mk (homOfLE hy))) := by sorry

end AlgebraicGeometry
