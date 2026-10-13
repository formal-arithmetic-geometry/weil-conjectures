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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

import Sheaf.RingTheory.KoszulProjectiveResolution
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.RingTheory.KoszulConormalBasis
import Sheaf.AlgebraicGeometry.AffineConormalFrame
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison

/-! # Finite bases for self Ext and exterior stalks on a Koszul chart

Source: Stacks Project, Tags 0BQY, 062I and 01R3. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The self Ext stalk and exterior stalk have finite bases with the same index
set on a single Koszul-regular chart. No compatibility of the two bases is asserted.

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation;
Tags 062I and 01R3 for the conormal basis.
(blueprint: lem-sc-koszul-self-ext-stalk-bases).

Proof: Let A be the section ring of U, I its closed-immersion ideal and B=A/I.
Sheafify the actual augmented Koszul projective resolution of B. Restriction of
derived internal Hom and the bounded finite free Hom model compute self Ext on U
as Hom of this resolution into B. The differential is zero because all regular
generators act by zero on B. Its degree n is the dual of the nth exterior power
of A^m with coefficients in B. The increasing wedge basis gives a B-basis indexed
by n-element subsets of Fin m. Sheafification, tensor pullback after cohomology,
restriction to V and then the stalk at z transport this to the first basis.
Independently, the regular conormal classes form a B-basis of I/I². The affine
conormal frame makes its sheaf locally free of rank m. Internal duality gives
the dual frame and the exterior sheaf local-free comparison gives its increasing
wedge frame with the same index set. Restrict and take germs of this frame to
obtain the second basis. Finite coordinate projections and inclusions show that
these germs form a basis over the stalk ring of V. Use a common K-injective model
for derived-universe comparison. The index set is a singleton for n=0 and empty
for n>m; empty charts cannot contain z. Only regularity on U is used. -/
theorem koszulRegularImmersion_self_ext_stalk_bases
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (z : V.toScheme) (U : Y.affineOpens) (hzU : i z.1 ∈ U.1)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
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
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (T.presheaf.stalk z)) ∧
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (E.presheaf.stalk z)) := by sorry

end AlgebraicGeometry
