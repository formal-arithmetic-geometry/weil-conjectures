/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.NormalizedDVRTower

/-! # Uniform bounds for finite compact-support reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Every finite compact-support reduction is constructible and has a common
cohomological support interval.  This is the boundedness part of the compact-support
normalization argument, independent of the normalized tower assembly.
Source: current blueprint `lem-fix-operation-reduction.proof.md`, compact-support
paragraph; Bhatt--Scholze Lemmas 6.7.7 and 6.8.14; Stacks Tags 08J9 and 0FPT.
The proof applies finite compact-support constructibility levelwise, then transports
the common interval for the input reductions across exact extension by zero and the
proper finite-type cohomological bound.  The interval is independent of the exponent.
It includes exponent one, zero input, and empty schemes and assumes no base structure
over the finite-field datum.
(blueprint: lem-sf-compact-support-normalized-reduction-tower-bounds). -/
theorem compactSupport_normalizedReductionTower_bounds
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∃ b₀ b₁ : ℤ, b₀ ≤ b₁ ∧ ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((sfAmbientCompactSupportCandidate
          (Padic.coefficientExtensionRing l E (n + 1)) c).obj
            ((scalarReductionDerivedExtension l E X n).obj K)) ∧
      proEtaleCohomologicalSupport
        ((sfAmbientCompactSupportCandidate
          (Padic.coefficientExtensionRing l E (n + 1)) c).obj
            ((scalarReductionDerivedExtension l E X n).obj K)) ⊆ Set.Icc b₀ b₁ := by
  sorry

end WeilConjectures
