/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement

/-! The naturality square for finite reduction of the native projection map.

This is the proper/open mate calculation in step 2 of
`det-prop-sf-pf-reduction` (blueprint: det-prop-sf-pf-reduction).  It is
deferred as one statement because its proof must expand the specified proper
and open factors and then use the two counit naturality equations together.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Functor
noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite reduction square of the native projection map commutes:
`Rf_!(a^f) ∘ c_f(H) ∘ ρ(PF^A_{f,K,L}) = PF^B_{f,K_m,L_m} ∘ (c_f(K) ⊗ 1) ∘ s`.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
det-prop-sf-pf-reduction.proof.md`, step 2 ("Transpose and paste the proper and open factors"),
node `det-prop-sf-pf-reduction`.

Proof: (1) by [det-def-sf-exchanges], `PF^R = Rr_{*,R}(γ_R) ∘ π_R` at `R = A, B`, with `π_R` the
counit-defined proper projection and `γ_R` the open tensor map; (2) the proper/open identities
of [lem-sf-pf-reduction-proper-open-identities] give `R_B(a^r) c_W ρ(π_A) = π_B (c_M ⊗ 1) s` and
`j_{!,B}(a^f) d_H ρ(γ_A) = γ_B (d_K ⊗ 1) a^r`; (3) naturality of `c` at `γ_A` and naturality of
the counit-defined `π_B` at `d_K` move `ρ(γ_A)` and `d_K` past the proper factors; (4) pasting
these equalities with `c_f(V) = Rr_*(d_V) c_{j_!V}` gives the displayed square, the tensor and
pullback comparisons being those of [lem-fix-operation-reduction].
(blueprint: det-prop-sf-pf-reduction-square) -/
theorem finiteReduction_projection_square
    (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] {m n : ℕ} (hmn : m ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] {f : X ⟶ Y}
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (K : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) X)
    (L : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) Y) :
    (FiniteReduction.reduction ell E hmn).map
          (CompactificationReindexing.pf
            (DerivedNakayama.quotientRing ell E (n + 1))
            (HasCompactification.compactification f) K.obj L.obj) ≫
        FiniteReduction.c_f (f := f) ell E hmn
          (K.obj ⊗ (CompactificationReindexing.P
            (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L.obj) ≫
        (CompactificationReindexing.F
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)).map
          (FiniteReduction.a_f (f := f) ell E hmn K.obj L.obj) =
      FiniteReduction.s ell E hmn
          ((CompactificationReindexing.F
            (DerivedNakayama.quotientRing ell E (n + 1))
            (HasCompactification.compactification f)).obj K.obj) L.obj ≫
        (FiniteReduction.c_f (f := f) ell E hmn K.obj ⊗ₘ 𝟙 _) ≫
        CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)
          ((FiniteReduction.reduction ell E hmn).obj K.obj)
          ((FiniteReduction.reduction ell E hmn).obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
