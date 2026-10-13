/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
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

/-! # Self Ext as the dual of the exterior conormal

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The Koszul Hom calculation identifies self Ext with the internal dual of the
exterior conormal, before using any exterior power of the internal dual.

Source: Stacks Project, Tag 0BQY, the displayed identification of Ext with
Hom of the negative-degree Koszul term, and Tag 062I for the conormal basis.
(blueprint: lem-sc-koszul-self-ext-dual-exterior-conormal).

Proof: On a regular affine chart write A = O_Y(U), I = ker(i)(U), and B = A/I.
Use the augmented Koszul projective resolution and sheafify it. Restriction of
RHom and the bounded finite-free Hom comparison identify the restricted self
Ext with degree n of Hom(K,B). All differentials are zero because their
coefficients belong to I. This degree is Hom_B(wedge^n(B^m),B). The conormal
basis identifies B^m with I/I^2, so it is the internal dual of wedge^n C.
The quotient action is the B action; hence tensor pullback after cohomology
does not change this identification. For a change of regular generators
f' = A f, the chain map on Koszul resolutions is wedge^p A in degree -p.
Modulo I its degree-one map is the map on conormal classes. Hom into B
therefore transforms in degree n by the transpose of wedge^n of that
conormal map, exactly the transition map of the dual exterior conormal.
Two expressions for A differ by Koszul syzygies, which vanish modulo I;
comparison maps lifting the identity of B are homotopic and so induce the
same cohomology map. Localization gives the identical formula. Refine every
intersection by affine opens carrying such comparisons and glue the maps
and their inverses by the sheaf condition on V. No affine-intersection or
quasi-separatedness assumption is needed. Compare derived universes using
a common K-injective resolution. For n=0 this is the quotient unit; above
the local sequence length both terms vanish. Empty V is also covered. -/
theorem koszulRegularImmersion_self_ext_dual_exterior_conormal
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
    Nonempty (F ≅ T) := by sorry

end AlgebraicGeometry
