/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Tor bounds over a constant field sheaf

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Project, Tags 03ER, 08FC, 06YQ, 06YP, 06YS and 08FZ
(blueprint: lem-sfb-constant-field-tor-bounds).

The existing coefficient-sized small representative accommodates every enclosing
coefficient universe. All objects are intrinsic module sheaves over the constant ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Over a constant field sheaf, cohomological support and Tor amplitude have exactly
 the same ordered interval. No finiteness or enough-points hypothesis is used.

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Tags 03ER, 08FC, 06YQ, 06YP, 06YS and 08FZ
(blueprint: lem-sfb-constant-field-tor-bounds).

Proof:
1. Apply lem-exc-constant-field-module-flat to the small representative: every module
sheaf is flat, using the local equational criterion rather than stalks.
2. By lem-sfb-bounded-representative choose a complex P vanishing termwise outside
[a,b]. Every test sheaf N in degree zero is K-flat by
lem-weil-pbc-independent-bounded-flat-kflat with upper bound zero.
3. By lem-pur-kflat-tensor-quasiiso-independent, tensoring with N[0] descends to the
localization. Thus the ordinary K-flat derived tensor is computed using P, and its
only degree-i summand is P^i tensor N. It vanishes outside [a,b], as does its homology.
4. Conversely test with the coefficient module itself. On a K-flat resolution of B,
the sectionwise unit maps p tensor r to r*p and p to p tensor 1 identify this tensor
with the resolution. Derived cohomology is invariant under the resulting isomorphism.
5. HasCoefficientProEtaleTorAmplitude is exactly this universal degree-zero tensor
vanishing test, independent of the K-flat representative. The interval is unchanged. -/
theorem constant_field_tor_bounds (X : Scheme.{u})
    (κ : Type (max v (u + 1))) [Field κ]
    (B : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ))
    (a b : ℤ) (hab : a ≤ b) :
    (∀ i : ℤ, i < a ∨ b < i →
      IsZero ((coefficientModelCohomology
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ) i).obj B)) ↔
      HasCoefficientProEtaleTorAmplitude X κ B a b := by
  sorry

/-- Finite Tor amplitude over the constant field is equivalent to bounded cohomology.
The ordered interval is a single common bound for every test module sheaf.

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Tag 08FZ (blueprint: lem-sfb-constant-field-tor-bounds).

Proof: apply constant_field_tor_bounds to each ordered integer interval and take
existence of its endpoints. This is proof step 5 of the node. The zero object works
in every ordered interval, including [0,0], and no geometric hypothesis enters. -/
theorem constant_field_finite_tor_amplitude_iff (X : Scheme.{u})
    (κ : Type (max v (u + 1))) [Field κ]
    (B : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ)) :
    HasFiniteCoefficientProEtaleTorAmplitude X κ B ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((coefficientModelCohomology
          (ConstantCompletion.constant
            (coefficientProEtaleModelTopology.{u, v} X) κ) i).obj B) := by
  sorry

end AlgebraicGeometry.Scheme
