/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.RationalTensorRealization.RationalRealizationTensorComparisonStructures

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ContinuousRational
namespace WeilConjectures.RationalTensorRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l)
  (X : ContinuousRational.Base.{u} l) (E : Padic.FiniteCoefficientFields l Ω)
  [CompactSpace X.scheme] [QuasiSeparatedSpace X.scheme]

/-- The specified raw rational realization preserves tensor and unit, symmetrically
and compatibly with all finite coefficient extensions.

Source: BS Proposition 6.8.14(2), Remark 6.8.15; Stacks 07A4, 0D6D
(blueprint: lem-zl-rational-realization-tensor-comparison).

Proof:
1. A finite-type scheme over the algebraic closure of a finite field is Noetherian
and finite-dimensional, by lem-weil-pbc-finite-type-over-noetherian and
lem-kun-dimension-finite-type. Separation and finite type give qcqs by
lem-weil-pbc-qcqs-over-affine; l differs from p, so is a unit. The identity integral
comparison and continuous realization give J(QM)=E_T tensor^L_B M and the fraction
formula, with actual continuous coefficients, by the two realization dependencies.
2. Apply lem-fix-constructible-tensor-completion to the prescribed completed tensor.
Its map chi is the simultaneous quotient augmentation and has zero shifted Roos
coordinate. It is invertible on constructible pairs, so ordinary tensor is complete.
3. Apply lem-sfb-ringed-derived-monoidal-comparisons to B to E_T. Compose ordinary
extension's tensor comparison with L(chi inverse). The rank-one perfect model and
lem-weil-pbc-constant-completion-equivalence identify the completed unit with B[0];
lem-pur-completed-operation-tower-substitution identifies its action unitors.
4. Choose simultaneous flat-term K-flat models; lem-pur-kflat-total-tensor-model
allows their total tensors as models again. The substitution lemma identifies whole
iterated quotient towers. Both associator routes send (x tensor y) tensor z to
xbar tensor (ybar tensor zbar). Unit routes are coefficient multiplication and the
symmetry route sends x tensor y to (-1)^(pq) ybar tensor xbar. These are equal maps
of entire towers, with zero shifted component, so their Roos limits agree.
5. Ordinary extension is symmetric monoidal. Step 4 transfers all its equations
to completed tensor. Descend on raw Hom localizations: fractions f/varpi^a and
g/varpi^b multiply both naturality routes by varpi^(-a-b), independent of their
representatives. Additivity treats sums; the integral identity equivalence is the
identity on these localized arrows, so these are comparisons for J itself.
6. For E contained in F, lem-weil-finite-free-completed-scalar-comparison identifies
ordinary completed-coefficient extension with prescribed completed extension by its
actual quotient map. The finite-stage equivalence uses that map's inverse. Both
scalar/realization composites are therefore the balanced iterated extension to F_T;
lem-sfb-ringed-derived-monoidal-comparisons supplies its composition and unit maps.
No finite quotient map is assumed flat and no two uniformizers are identified.
7. By lem-pur-scalar-extension-tower-coherence the completed scalar/tensor map is
the whole quotient-system balanced map. After inserting the same chi maps, both
routes send c tensor (x tensor y) to (c tensor x) tensor (1 tensor y), including
transitions and zero shifted coordinates. Thus the scalar/tensor square is the
ordinary monoidal composition square, which commutes. Its unit formula is cb.
Localize as in step 5. The same balanced maps satisfy the three-field composition
identity, proving every asserted comparison and coherence clause. -/
theorem rational_realization_tensor_comparison (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.scheme.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of D.k))]
    [QuasiCompact (X.scheme ↘ Spec (.of D.k))]
    [IsSeparated (X.scheme ↘ Spec (.of D.k))] :
    Nonempty (System l Ω S R X) := by
  sorry


end WeilConjectures.RationalTensorRealization
