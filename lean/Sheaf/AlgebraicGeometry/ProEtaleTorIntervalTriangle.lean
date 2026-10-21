/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent

/-!
# Tensor cohomology segments and Tor intervals on the pro-etale site

Source: Stacks Project, Cohomology on Sites, Tag 08G2, lemma-cone-tor-amplitude (2),
and Tag 08FZ, definition-tor-amplitude.
(blueprint: lem-weil-proetale-tor-interval-triangle).

We use the recorded coefficient-sized model of the small pro-etale site, its ordinary
constant ring sheaf, and the existing K-flat derived tensor. Exactness of the two
cohomology maps is expressed by exactness of their short complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- The canonical module-sheaf abelian structure with all universe arguments fixed.
This only specializes Mathlib's existing instance and the published sheafification
instance, avoiding inference through an older successor-universe interface.
Source: Stacks Tags 03DA and 08G2
(blueprint: lem-weil-proetale-tor-interval-triangle). -/
instance coefficientProEtaleTorModulesAbelian (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Abelian (ConstantCompletion.Mod.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)) :=
  @SheafOfModules.instAbelian.{max v (u + 1), max v (u + 1),
    max v (u + 1), max v (u + 1)} _ _ _ _
    (coefficientModelAdditiveSheafify.{u, v} Y) inferInstance

/-- The published derived tensor with an arbitrary module sheaf in degree zero.
This is the existing K-flat tensor on the same small site as the Tor predicate;
it uses the standard derived localization, with no new choice of resolutions.
Source: Stacks Tags 06YU and 08G2
(blueprint: lem-weil-proetale-tor-interval-triangle). -/
def coefficientProEtaleTorTensor (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (N : ConstantCompletion.Mod.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)) :
    ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A) ⥤
    ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A) :=
  let R := ConstantCompletion.constant.{max v (u + 1)} (coefficientProEtaleModelTopology.{u, v} Y) A
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod.{max v (u + 1)} R)
  (Functor.curry.obj
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), (max v (u + 1)) + 1} _ R)).flip.obj
    ((DerivedCategory.singleFunctor (ConstantCompletion.Mod.{max v (u + 1)} R) 0).obj N)

/-- Tensor cohomology is exact at the middle vertex, and Tor intervals of the two
outside vertices give their minimum/maximum interval for the middle vertex.
The last clause spells out the common-interval specialization; it does not assert
optimality of the endpoints.

Source: Stacks Tag 08G2, lemma-cone-tor-amplitude (2), and Tag 08FZ
(blueprint: lem-weil-proetale-tor-interval-triangle).

Proof plan:
1. Fix a module sheaf N. By lem-pc-kflat-resolution choose a flat-term K-flat
   resolution P of N[0]. By lem-weil-pbc-kflat-fixed-tensor-triangulated, tensoring
   with P descends to an exact functor, with its signed shift comparison. For each
   complex K choose a flat-term K-flat resolution P_K. The two quasi-isomorphisms
   from P_K tensor P to P_K tensor N[0] and to K tensor P identify this functor
   with the recorded derived tensor; lem-weil-derived-tensor-resolution-independent
   makes the identification independent of the resolution. Thus it sends the given
   distinguished triangle to a distinguished triangle, including its last arrow.
2. Apply lem-sf-derived-homology-long-exact to that tensor triangle. Its degree-i
   segment is exact, meaning that the image subobject of the first map equals the
   kernel subobject of the second map. These are the cohomology sheaves of
   def-weil-derived-cohomology-sheaves, computed by the standard homology functor.
3. Put c = min(a_U,a_W) and d = max(b_U,b_W). The ordered outside intervals give
   c <= d. For i < c or d < i, both outside cohomology sheaves vanish by
   def-weil-proetale-tor-amplitude, for every N. Exactness forces the middle sheaf
   to vanish as well. This is precisely Tor amplitude in [c,d].
4. Set a_U = a_W = a and b_U = b_W = b. The minimum and maximum are a and b,
   respectively, giving the last clause. No finiteness or constructibility is used.
-/
theorem coefficientProEtale_tor_interval_triangle (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (T : Triangle (ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A)))
    (hT : T ∈ distTriang (ConstantCompletion.D.{max v (u + 1)}
      (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A))) :
    (∀ (N : ConstantCompletion.Mod.{max v (u + 1)}
        (ConstantCompletion.constant.{max v (u + 1)}
        (coefficientProEtaleModelTopology.{u, v} Y) A))
      (i : ℤ),
      ∃ h : (((coefficientProEtaleTorTensor Y A N) ⋙
          coefficientModelCohomology.{max v (u + 1)}
            (ConstantCompletion.constant.{max v (u + 1)}
              (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₁) ≫
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₂) = 0,
        (ShortComplex.mk
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₁)
          (((coefficientProEtaleTorTensor Y A N) ⋙
            coefficientModelCohomology.{max v (u + 1)}
              (ConstantCompletion.constant.{max v (u + 1)}
                (coefficientProEtaleModelTopology.{u, v} Y) A) i).map T.mor₂) h).Exact) ∧
    (∀ (aU bU aW bW : ℤ), aU ≤ bU → aW ≤ bW →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₁ aU bU →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₃ aW bW →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₂ (min aU aW) (max bU bW)) ∧
    (∀ (a b : ℤ), a ≤ b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₁ a b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₃ a b →
      HasCoefficientProEtaleTorAmplitude Y A T.obj₂ a b) := by
  sorry

end AlgebraicGeometry.Scheme
