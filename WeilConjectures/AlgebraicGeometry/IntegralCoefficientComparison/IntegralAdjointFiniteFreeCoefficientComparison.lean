/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointFiniteFreeCoefficientComparisonData
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointFiniteFreeCoefficientComparisonData
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOperationsExistence
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData

/-! Finite-free coefficient comparison theorem. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
open IntegralDirectImageTower CurrentNativeIntegralTower

variable (ell : ℕ) [Fact ell.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic ell) Ω] [IsAlgClosure (Padic ell) Ω]

variable (s : ∀ E : Padic.FiniteCoefficientFields ell Ω, Presentation ell E.val)
/-- Finite-free coefficient comparison on the native Dbc categories, together with
its canonical whole-tower construction and realization equations.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1)--(2)
(blueprint: lem-pur-integral-adjoint-finite-free-coefficient-comparison).

Proof (1): O_F is finite free over O_E. The sheafified tensor functor on the
strict sequence site therefore has the displayed quotient formula, including
transitions and multiplication units. Its universal derived functor yields C.
Tensor associativity gives the normalized reduction square. Finite freeness
commutes with total derived inverse limit; transpose the reduction square under
the actual reduction/limit adjunction to obtain its specified limit comparison.
The constructible scalar theorem and normalized tower equivalence give the
bounded constructible restrictions and the reconstruction units.

Proof (2): form the proper scalar counit mate and the ordinary open scalar square
on the sequence site. Their composite is the whole-tower compact-support map.
On normalized constructible towers its finite evaluations are isomorphisms, so
it is an isomorphism. Transpose its inverse followed by the tower counit to
obtain the tower exceptional comparison. The normalized integral edge transports
these two arrows through reduction and total limit, giving precisely the native
scalarCompactSupportMap and v. Mate-pasting proves the two displayed realization
equations; the triangle identities give the actual unit and counit equations.
Pasting the canonical tensor associators and units before localization gives the
identity and cocycle for v. Multiplication on coefficients and the compatible
root projections identify the native coefficient unit and Tate lines.
No equality of derived-system arrows is deduced from separate finite evaluations. -/
theorem integralAdjointFiniteFreeCoefficientComparison
    (p : ℕ) (hp : 0 < p) (hne : p ≠ ell) (k : Type u) [Field k] [CharP k p]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left)
    (e : ∀ E : Padic.FiniteCoefficientFields ell Ω, Edge ell E.val (s E) c) :
    letI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    letI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    Nonempty (Result ell Ω s c e) := by
  letI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  letI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨A⟩ := scalarCore_exists ell Ω s p hp hne k X Y f d c e
  obtain ⟨B⟩ := towerCore_exists ell Ω s p hp hne k X Y f d c e A
  exact ⟨{
    systems := A.systems
    native_lines := A.native_lines
    preserves := A.preserves
    b := A.b
    b_canonical := A.b_canonical
    v := A.v
    transpose := A.transpose
    counit := A.counit
    unit := A.unit
    identity := A.identity
    cocycle := A.cocycle
    right_normalized := B.right_normalized
    left_normalized := B.left_normalized
    tower_b := B.tower_b
    tower_b_canonical := B.tower_b_canonical
    tower_j := B.tower_j
    tower_transpose := B.tower_transpose
    tower_counit := B.tower_counit
    tower_unit := B.tower_unit
    limit_v := B.limit_v
    limit_b := B.limit_b }⟩
end AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
