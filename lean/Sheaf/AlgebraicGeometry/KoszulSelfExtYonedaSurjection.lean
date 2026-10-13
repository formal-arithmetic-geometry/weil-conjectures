/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
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

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

import Sheaf.RingTheory.KoszulProjectiveResolution
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.RingTheory.KoszulConormalBasis

/-! # Surjectivity of the exterior Yoneda comparison

Source: Stacks Project, Tags 0BQW and 0BQY. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The alternating Yoneda products give a surjection from the exterior sheaf to
self Ext on the Koszul-regular open. This asserts generation, not injectivity.

Source: Stacks Project, Tags 0BQW and 0BQY, the degree-one boundary and the
contraction-product spanning argument.
(blueprint: lem-sc-koszul-self-ext-yoneda-surjection).

Proof: The second-order thickening sequence gives the intrinsic degree-one map
from the conormal dual to self Ext by pushing out extensions. Compose n such
classes using derived internal Hom composition. On a regular affine chart,
represent these classes by the degree-one derivations of the augmented Koszul
DG algebra. Each derivation squares to zero and distinct derivations anticommute.
Thus the product vanishes when two arguments agree, even in characteristic two;
it is alternating, rather than merely skew symmetric. The exterior universal
property and module sheafification give a map on the regular locus. All maps
come from the intrinsic boundary and composition, so they commute with restriction
and agree on overlaps without a quasi-separatedness hypothesis. The resulting
map is linear for the quotient action. Tensor pullback of cohomology preserves
this action and restriction yields the displayed morphism on V.
On a chart of length m, Hom of the Koszul resolution into the quotient has zero
differentials. Products of n distinct contraction classes span its degree-n term,
so the morphism is surjective on each stalk. Use a common K-injective Hom model
to compare the given derived universe. For n=0 the empty product is the unit;
for n>m the target stalk is zero. Empty V has no stalk obligations. -/
theorem koszulRegularImmersion_self_ext_yoneda_surjection
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
    let E := Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf))) n
    ∃ φ : E ⟶ T, ∀ z : V.toScheme, Function.Surjective (φ.stalkLinearMap z) := by sorry

end AlgebraicGeometry
