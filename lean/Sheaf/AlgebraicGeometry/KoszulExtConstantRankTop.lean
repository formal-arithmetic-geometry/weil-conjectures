/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
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
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.RingTheory.KoszulRegularSequenceDualComplex
import Sheaf.RingTheory.KoszulConormalBasis
import Sheaf.AlgebraicGeometry.AffineConormalFrame

/-! # Constant-rank top scalar Koszul Ext

Source: Stacks Project, Tag 0BQZ. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The top scalar Ext on a constant conormal-rank open is its dual determinant.

Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-ext-constant-rank-top).

Proof: Fix z in V and choose an affine Koszul chart with regular sequence f of
length m. Its conormal basis localizes to a basis at z; the affine conormal frame
computes the stalk finrank as m, so hVrank gives m=n. Shrink within V. The Koszul
augmentation resolves the quotient by finite free modules. Restrict derived
internal Hom to the chart and compute it by bounded finite free Hom into the
structure sheaf in degree zero. Exact associated-module sheafification identifies
this complex with the sheafified dual Koszul complex, extended by zero to integer
degrees. The normalized dual Koszul comparison identifies degree-n cohomology
with the quotient-module determinant of the dual of I/I². Pullback AFTER taking
cohomology tensors this quotient module with the quotient ring, canonically
leaving it unchanged. The affine conormal identification and finite free internal
Hom identify the result with exteriorSheaf of the restricted conormal dual.
The intrinsic Ext determinant comparison is independent of regular generators
and commutes with localization. On overlaps refine by affine standard opens;
the normalized comparisons and their inverses agree there. The sheaf condition
glues both directions to the stated isomorphism on V. This does not require
quasi-separatedness, a rank function away from V, or regularity away from V.
For n=0 the empty Koszul resolution gives the structure sheaf, the zeroth
exterior power. For empty V both objects are zero. The common K-injective Hom
complex transports the calculation to the supplied derived universe. -/
theorem koszulRegularImmersion_ext_constantRank_top
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (hVrank : ∀ z : Z, z ∈ V →
      Module.finrank (Z.presheaf.stalk z)
        ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) = n) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj F) ≅
      Scheme.Modules.exteriorSheaf
        ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf))) n) := by sorry

end AlgebraicGeometry
