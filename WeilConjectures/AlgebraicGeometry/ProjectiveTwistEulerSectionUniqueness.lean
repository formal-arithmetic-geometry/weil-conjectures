/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Polynomial.Eval.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.NagataAffineProjScalarExtension
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistCohomologyBound
import WeilConjectures.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionSerreVanishing
import WeilConjectures.AlgebraicGeometry.PQFCohomologySupplement
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Twisted projective cohomology and uniqueness of eventual section polynomials

Source: Stacks Project, coherent.tex Tag 01YS (2)--(4), varieties.tex Tag 08AE.
(blueprint: lem-sfb-projective-twist-euler-section-uniqueness)

The three helper definitions specialize the existing twist, cohomology and Euler
characteristic to the closed immersion and its induced map to Spec k.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- F tensor i^* O(m), with O(m) the existing Proj twist of the polynomial ring.
Source: Stacks Project, Tags 01MN, 01YS.
(blueprint: lem-sfb-projective-twist-euler-section-uniqueness). -/
noncomputable def projectiveClosedTwist {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}}
    (i : X ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (N + 1))) k)
    (F : X.Modules) (m : ℕ) : X.Modules :=
  letI := MvPolynomial.gradedAlgebra (σ := ULift.{u} (Fin (N + 1))) (R := k)
  F ⊗ (tensorPullback i).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) (m : ℤ))

/-- Right-derived module sections, restricted to k along the induced structure map.
Source: Stacks Project, Tags 01EO, 01YS.
(blueprint: lem-sfb-projective-twist-euler-section-uniqueness). -/
noncomputable def projectiveClosedTwistCohomology {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}}
    (i : X ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (N + 1))) k)
    (F : X.Modules) (m q : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (i ≫ Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k).appTop).hom).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (projectiveClosedTwist i F m))

/-- The existing Euler characteristic for the k-structure induced by i.
Source: Stacks Project, Tag 08AE.
(blueprint: lem-sfb-projective-twist-euler-section-uniqueness). -/
noncomputable def projectiveClosedTwistEuler {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}}
    (i : X ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (N + 1))) k)
    (F : X.Modules) (m : ℕ) : ℤ :=
  @eulerChar k _ X
    (OverClass.ofHom (i ≫ Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k))
    (projectiveClosedTwist i F m)

/-- All nonnegative twists have finite cohomology; sufficiently high twists have only
H^0 and their Euler characteristic is its dimension. Eventual rational section
polynomials are unique, and on the empty scheme all cohomology, Euler values and
any such polynomial vanish. The arbitrary F includes the structure sheaf.
Source: Stacks Project, Tag 01YS (2)--(4), Tag 08AE; elementary root argument.
(blueprint: lem-sfb-projective-twist-euler-section-uniqueness).

Proof: (1) On D_+(z_j), degree-m fractions are freely generated by z_j^m;
on overlaps the transition is (z_j/z_l)^m. Thus the Proj twist is O_P(m), and
pullback followed by tensor identifies E_m locally with F, preserving its finite
presentation and quasi-coherence. (2) A field is Noetherian. Use
lem-nagata-affine-proj-scalar-extension with Z -> k and the graded polynomial
scalar-extension isomorphism lem-weil-pbc-polynomial-scalar-extension to identify
polynomial Proj with the base-change projective space. The resulting closed
immersion lets lem-pc-m1-projective-affine-finite-cohomology-independent give finite
cohomology in every degree for each m. (3) Apply
lem-weil-pbc-closed-immersion-serre-vanishing and the chart identification from (1)
to get a single natural bound for every positive degree. (4) The finite affine
cover makes X quasi-compact. Its projective structure morphism is proper by
lem-pc-projective-proper, and X is Noetherian by
lem-weil-pbc-finite-type-over-noetherian. The twists are coherent by
pqf-lem-coherent-ft-locnoeth. The bound
lem-pc-j4-closed-immersion-twist-cohomology-bound kills degrees above N, so the Euler
sum is finite; above the Serre bound only its degree-zero term remains. Higher
direct images to the one-point Spec k are the derived global sections used here.
(5) The difference of two eventual polynomials has infinitely many distinct rational
roots. Polynomial division by t-a and induction on degree show that a nonzero
polynomial has at most its degree many distinct roots, hence the difference is zero.
(6) On the empty space the empty-cover sheaf axiom forces every module sheaf to be
zero, hence all derived sections and Euler values vanish for every m. Apply (5)
to the proposed polynomial and zero. The structure sheaf has the finite presentation
O^0 -> O -> O -> 0 and is quasi-coherent, so it is included. -/
theorem projective_twist_euler_section_uniqueness
    {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
    (i : X ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (N + 1))) k)
    [IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    (∀ m q : ℕ, FiniteDimensional k (projectiveClosedTwistCohomology i F m q)) ∧
    (∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (∀ q : ℕ, 0 < q → IsZero (projectiveClosedTwistCohomology i F m q)) ∧
      projectiveClosedTwistEuler i F m =
        (Module.finrank k (projectiveClosedTwistCohomology i F m 0) : ℤ)) ∧
    (∀ P₁ P₂ : Polynomial ℚ,
      (∃ a : ℕ, ∀ m : ℕ, a ≤ m →
        P₁.eval (m : ℚ) = (Module.finrank k (projectiveClosedTwistCohomology i F m 0) : ℚ)) →
      (∃ a : ℕ, ∀ m : ℕ, a ≤ m →
        P₂.eval (m : ℚ) = (Module.finrank k (projectiveClosedTwistCohomology i F m 0) : ℚ)) →
      P₁ = P₂) ∧
    (IsEmpty X →
      (∀ m q : ℕ, IsZero (projectiveClosedTwistCohomology i F m q)) ∧
      (∀ m : ℕ, projectiveClosedTwistEuler i F m = 0) ∧
      (∀ P : Polynomial ℚ,
        (∃ a : ℕ, ∀ m : ℕ, a ≤ m →
          P.eval (m : ℚ) = (Module.finrank k (projectiveClosedTwistCohomology i F m 0) : ℚ)) →
        P = 0)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
