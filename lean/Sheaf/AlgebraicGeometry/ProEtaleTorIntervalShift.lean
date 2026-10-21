/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Shifts and quantitative Tor bounds on the pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 06YU and 08FZ;
Homology, Tags 011G and 011H (blueprint: lem-weil-proetale-tor-interval-shift).
The coefficient-sized small model is equivalent to the original small pro-etale site.
All tensor tests use the published K-flat derived tensor and ordinary module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

/-- Restrict the published derived tensor to module sheaves in degree zero in its
second argument. This is composition of existing functors, with no new resolutions.
Source: Stacks Tag 06YU (blueprint: lem-weil-proetale-tor-interval-shift). -/
def coefficientProEtaleTorTensorTest (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) ×
    ConstantCompletion.Mod (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A)) ⥤
    ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) :=
  let R := ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} Y) A
  letI : HasSheafify (coefficientProEtaleModelTopology.{u, v} Y)
      AddCommGrpCat.{max v (u + 1)} := coefficientModelAdditiveSheafify Y
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  (𝟭 (ConstantCompletion.D R)).prod
    ((HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0) ⋙
      ConstantCompletion.Q R) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), max v (u + 1) + 1}
      (coefficientProEtaleModelTopology.{u, v} Y) R

/-- Natural tensor and cohomology shift comparisons, the exact interval translation,
isomorphism invariance, and the zero test for arbitrary commutative coefficients.
The natural isomorphisms are on the product of the derived category and the entire
module-sheaf category, so they include naturality in both K and N.

Source: Stacks Tags 06YU and 08FZ, and Homology Tags 011G and 011H
(blueprint: lem-weil-proetale-tor-interval-shift).

Proof (the node's five steps):
1. Apply lem-pc-kflat-resolution to each N[0]. The fixed-tensor exact descent of
   lem-weil-pbc-kflat-fixed-tensor-triangulated gives the shift comparison in K.
   Its compatibility with maps of flat-term K-flat fixed arguments, followed by
   lem-weil-pbc-site-derived-tensor-descent, gives naturality in every N as well.
   The representative comparison identifies this with def-weil-derived-tensor.
2. Apply def-weil-derived-cohomology-sheaves to that natural comparison and compose
   with lem-sp-derived-cohomology-shift: H^i(T[m]) is H^(i+m)(T).
3. Unfold def-weil-proetale-tor-amplitude. An integer i is outside [a-m,b-m]
   precisely when i+m is outside [a,b]. This proves one implication. For the
   converse substitute i=j-m for every j outside [a,b]. The ordered endpoints
   remain ordered under subtraction, for positive, zero and negative m.
4. Tensor a derived isomorphism with every N and then apply cohomology. IsZero
   is invariant under isomorphism, so every vanishing test is equivalent.
5. Compute the total tensor of zero with a K-flat resolution of N. By
   def-pc-tensor-complex-sheaves each term is a direct sum of zero modules and
   every differential is zero. Its derived object and all its cohomology vanish.
   The Tor tests outside [0,0] therefore vanish for every N.
-/
theorem coefficientProEtaleTor_interval_shift (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (∀ m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m)) ∧
    (∀ i m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) i ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) (i + m))) ∧
    (∀ (K : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (a b m : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A (K⟦m⟧) (a - m) (b - m))) ∧
    (∀ (K L : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (_e : K ≅ L)
      (a b : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A L a b)) ∧
    (∀ N : ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A),
      Nonempty (@Functor.obj _
        (CategoryTheory.prod'.{max v (u + 1) + 1, max v (u + 1)}
          (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))
          (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))
        (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) inferInstance
        (coefficientProEtaleTorTensorTest.{u, v} Y A)
        ((0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))), N) ≅
        (0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))))) ∧
    HasCoefficientProEtaleTorAmplitude Y A 0 0 0 := by
  sorry

end AlgebraicGeometry.Scheme
