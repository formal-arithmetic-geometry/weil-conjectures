/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.RelativeCyclicRestrictionModel
public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Paper.IndUnipotentSystem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Sheaf.RepresentationTheory.ProcyclicScalarCochainEvaluation
import Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic
import Sheaf.CategoryTheory.NormAlgclBarAugmentation
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Trivial norm-scalar procyclic restriction

Source: latest blueprint, six-functors direct-images proof, paragraph (3), scalar
analytic base of the rank-one polynomial-translation input. This is an agent-formulated
auxiliary obligation; an exact external reference is wanted.
(blueprint: lem-sfb-trivial-procyclic-restriction-isomorphism).

The maps are the recorded invariant-normalized cyclic restriction, compatible bar
augmentation, and evaluation at the positive generator. All modules and derived
categories are ordinary internal modules, including for noncomplete coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CondensedBar CategoryTheory.RelativeCyclic
open Profinite.CondensedAction Profinite.CondensedAction.IndUnipotent
open Profinite.CondensedAction.ContinuousRepresentation Profinite.CondensedAction.PrimeToEll

namespace ContinuousCohomology.TrivialProcyclic

/-- The actual inclusion of the discrete integers into the additive p-adic integers,
written multiplicatively and lifted to the common site universe: k maps to k.
Source: node statement, u(k)=k in direct-images paragraph (3)
(blueprint: lem-sfb-trivial-procyclic-restriction-isomorphism). -/
def integerInclusion (ℓ : ℕ) [Fact ℓ.Prime] :
    CategoryTheory.RelativeCyclic.Z.{u} →ₜ* IntegerGroup.{u} ℓ where
  toFun k := Multiplicative.ofAdd (ULift.up (k.toAdd.down : ℤ_[ℓ]))
  map_one' := by
    change ULift.up ((0 : ℤ) : ℤ_[ℓ]) = ULift.up (0 : ℤ_[ℓ])
    exact congrArg ULift.up Int.cast_zero
  map_mul' a b := by
    change ULift.up (((a.toAdd.down + b.toAdd.down : ℤ) : ℤ_[ℓ])) =
      ULift.up ((a.toAdd.down : ℤ_[ℓ]) + (b.toAdd.down : ℤ_[ℓ]))
    exact congrArg ULift.up (Int.cast_add _ _)
  continuous_toFun := continuous_of_discreteTopology

/-- Scalar invertibility and the equality of the actual arrows, for every compatible
bar model, its invariant normalization, and every nonnegative equivariant resolution.
The underived bar is the function complex C(S x H^q,F), by its free-module internal-Hom
coordinates. The recorded evaluation is identity in degree zero, evaluation at u(1)
in degree one, and zero above one. The expression is j followed by eta inverse and c.
Source: node statement, scalar clauses and displayed equality, direct-images paragraph (3)
(blueprint: lem-sfb-trivial-procyclic-restriction-isomorphism). -/
def ScalarAssertion (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [NormedField F] : Prop :=
  ∀ (K : TotalModel (continuousScalarRing F) PUnit.{u + 1})
    (C : HasComparison (continuousScalarRing F) PUnit.{u + 1} K)
    (M : BarModel (continuousScalarRing F) (IntegerGroup.{u} ℓ))
    (b : BarNormalization M)
    (I : InjectiveResolution
      (CondensedDerivedRestriction.regularTrivial (continuousScalarRing F) (IntegerGroup.{u} ℓ))),
    IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap
      (barAugmentation (barFunctions M) (barDiagram M)
        (CondensedDerivedRestriction.regularTrivial (continuousScalarRing F)
          (IntegerGroup.{u} ℓ)) I) ComplexShape.embeddingUpNat)) ∧
    IsIso (trivialCyclicMap C (integerInclusion ℓ)) ∧
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (barAugmentation (barFunctions M) (barDiagram M)
          (CondensedDerivedRestriction.regularTrivial (continuousScalarRing F)
            (IntegerGroup.{u} ℓ)) I) ComplexShape.embeddingUpNat) ≫
      (barEta M b
        (CondensedDerivedRestriction.regularTrivial (continuousScalarRing F)
          (IntegerGroup.{u} ℓ)) I).inv ≫
      trivialCyclicMap C (integerInclusion ℓ) =
    DerivedCategory.Q.map (HomologicalComplex.extendMap
      (CategoryTheory.RelativeCyclic.evaluation (barFunctions M) (barDiagram M)
        (integerInclusion ℓ)) ComplexShape.embeddingUpNat)

/-- The canonical cyclic restriction on all finite trivial tensor coefficients.
The existing Extended is F tensor_E W with its finite-dimensional module topology;
Realization fixes every continuous section, scalar, restriction, and group action.
The residual group is trivial. Its exact conservative forgetful functor detects the
same invertibility in ordinary internal modules. Dimension zero is not excluded.
Source: node statement, finite biproduct clause, direct-images paragraph (3)
(blueprint: lem-sfb-trivial-procyclic-restriction-isomorphism). -/
def FiniteAssertion (ℓ : ℕ) [Fact ℓ.Prime] (E F : Type u)
    [NormedField E] [NormedField F] [Algebra E F] : Prop :=
  ∀ (W : Type (u + 1)) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (K : TotalModel (continuousScalarRing F) PUnit.{u + 1})
    (C : HasComparison (continuousScalarRing F) PUnit.{u + 1} K)
    (N : Realization F (PUnit.{u + 1} × IntegerGroup.{u} ℓ) (Extended E F W)
      (Representation.trivial F (PUnit.{u + 1} × IntegerGroup.{u} ℓ) (Extended E F W))),
    IsIso (cyclicMap (continuousScalarRing F) PUnit.{u + 1} C (integerInclusion ℓ) N.object)

/-- The actual scalar augmentation and cyclic comparison are invertible, their normalized
composite is generator evaluation, and cyclic restriction is invertible on every finite
trivial tensor coefficient, over both E and the norm-topological algebraic closure.
Source: latest blueprint direct-images proof, paragraph (3), scalar analytic base;
agent-formulated auxiliary obligation, exact external reference wanted
(blueprint: lem-sfb-trivial-procyclic-restriction-isomorphism).

Proof, following the six DAG steps:
1. Apply lem-sfb-procyclic-scalar-cochain-evaluation to E and Omega. Its ordinary
function-sheaf evaluation is epsilon here, so localization makes Q epsilon invertible.
2. For E, identify each augmentation column using
lem-sfb-normed-scalar-profinite-hom-acyclic at H^q. Both double complexes are first
quadrant and have finite total diagonals. Apply
lem-sc-first-quadrant-total-column-comparison to the actual augmentation to invert j.
3. For Omega, use lem-sfb-norm-algcl-bar-augmentation on the same compatible resolution.
This inverts the actual total augmentation without asserting termwise acyclicity or
completeness of Omega.
4. Specialize lem-sfb-relative-cyclic-restriction-model to residual group one and
u(k)=k. Its barEvaluation gives j followed by eta inverse and c equal to Q epsilon.
The normalized eta is invertible by lem-sfb-condensed-derived-invariant-bar.
Cancel j and eta to conclude that the specified c is invertible.
5. Choose a finite E-basis of W, with d its dimension. The product topology identifies
F tensor_E W with F^d homeomorphically. Continuous sections identify N with the finite
biproduct of d copies of A, compatibly with scalars, restrictions, and trivial action.
For d=0 these are zero modules, including at the empty profinite test object.
6. Derived invariants and the two-term functor are additive; c is natural by the relative
cyclic restriction model. With coordinate inclusions i_r and projections p_r, the
inverse is the sum of QK(p_r), inverse c_A, and R Gamma(i_r), in that order.
Naturality and sum i_r p_r = identity give both inverse equations. The empty sum gives
the same equations for W=0. Exact conservative forgetting of the trivial residual
action identifies this assertion with scalar c_N and does not change its normalization.
-/
theorem trivial_procyclic_restriction_isomorphism (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E] :
    ScalarAssertion ℓ E ∧ ScalarAssertion ℓ Ω ∧
      FiniteAssertion ℓ E E ∧ FiniteAssertion ℓ E Ω := by
  sorry

end ContinuousCohomology.TrivialProcyclic
