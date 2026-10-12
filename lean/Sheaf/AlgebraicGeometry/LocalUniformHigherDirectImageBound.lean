/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
import Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Topology.RestrictInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Local bounds uniform in the quasi-coherent coefficient module

Source: Stacks Project, Tag 01XJ, finite-cover argument over an affine base.
(blueprint: lem-pc-local-uniform-higher-direct-image-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every point has a neighbourhood with a higher-direct-image bound independent of
its quasi-coherent coefficient module. The target need not be quasi-compact.
Source: Stacks Project, Tag 01XJ, proof of (3), affine-base finite-cover argument.
(blueprint: lem-pc-local-uniform-higher-direct-image-bound).

Proof: Choose an affine neighbourhood U of s. The inverse image of U is quasi-compact
and quasi-separated. Apply quasi-compact-open induction to the property that an open W
has a cohomological bound valid for every affine base change T -> U and every
quasi-coherent module on T times_U W. For affine W take bound 1: the base change is
affine and affine vanishing applies. For a union W1 union W2 use the bounds a, b, c
on W1, W2, W1 intersection W2; restriction preserves quasi-coherence and the
Mayer-Vietoris sequence makes max(a,b,c)+1 a bound on the union. The induction
principle handles the quasi-compact separated intersections with affine charts.
Thus a single finite bound works on f^{-1}U after every affine base change. This is
the finite-cover argument of Tag 01XJ (equivalently the quantitative Tag 071L). Apply this
to affine open neighbourhoods in U. By Tag 01E4, higher direct images are the
sheafifications of these cohomology presheaves; hence their restrictions to U vanish
in this range. Open restriction preserves injective resolutions (Tag 01E1), identifying
this restriction with that of the displayed right derived functor. Neither the cover
nor the bound uses M. Empty inverse images give zero sections in every degree. -/
theorem exists_local_uniform_higherDirectImage_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (s : S) :
    ∃ (U : S.Opens) (n : ℕ), s ∈ U ∧
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)), M.IsQuasicoherent →
        ∀ p : ℕ, n ≤ p → IsZero
          (Scheme.Modules.restrict
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M)
            U.ι) := by sorry

end AlgebraicGeometry
