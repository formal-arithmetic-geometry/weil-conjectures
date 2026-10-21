/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.RingTheory.DerivedCompleteModuleComplex

/-! # Integral geometric stalks and their finite reductions -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Constructibility of the first reduction controls the uniformizer cone of the stalk.
Source: blueprint `fix-lem-finite-tor-perfect`, proof, finite reduction and residue steps;
Stacks Tags 06YS, 06YY and 06Y6.
(blueprint: lem-t5-integral-stalk-residue-finite).

Proof: resolve K by a flat-term K-flat sheaf complex P. Multiplication by the
uniformizer is injective on the completed coefficient sheaf; its cokernel is the
first finite coefficient sheaf. Tensor this sequence with P. Flatness gives the
termwise exact sequence P --uniformizer--> P --> P/ uniformizer. Thus the cone of
multiplication represents restriction of the first derived reduction. Exact stalks
commute with its cone and homology. The specified constant-to-completed map followed
by the finite projection is the actual quotient map on constant integral scalars,
so its first map is exactly uniformizer multiplication on the stated module stalk.
Constructible finite-coefficient cohomology has finite geometric stalks: descend it
to a constructible etale sheaf and apply the canonical comparison of geometric
stalks. Hence every cohomology module of this cone is finite. A quasi-isomorphism
P to K induces one on these cones, so the conclusion holds for the given K without
any flatness, completeness or boundedness hypothesis. In particular zero complexes
and n=1 use precisely the same sequence. -/
theorem integralStalk_residue_finite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hred : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((scalarReductionDerivedExtension.{u, u} l E Y 0).obj (DerivedCategory.Q.obj K))) :
    let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
    let C := ((integralCoefficientModuleStalkFunctor l E y).mapHomologicalComplex (.up ℤ)).obj K
    ∀ i : ℤ, Finite ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} R) (.up ℤ) i).obj
      (CochainComplex.mappingCone ((ULift.up
        (Padic.coefficientExtensionUniformizer l E)) • 𝟙 C))) := by sorry

end WeilConjectures
