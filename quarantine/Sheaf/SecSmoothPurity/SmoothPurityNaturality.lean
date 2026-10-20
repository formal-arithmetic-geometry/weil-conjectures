/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
import Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurityDiagonalDualizingObject
import Sheaf.Paper.PurityDncInvariance
import Sheaf.Targets.VectorBundlePurity
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution

/-!
# Naturality and choice-independence of the smooth purity map

Source: Weil conjectures blueprint, sec-smooth-purity/sk-thm-smooth-purity,
proposition `prop-pur-smooth-purity-naturality-cover`, order 2015
(blueprint: prop-pur-smooth-purity-naturality-cover).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical smooth purity map is natural in the coefficient object, and its
presentation-level formula is independent of all choices of an etale presentation.
Source: Weil conjectures blueprint, sec-smooth-purity/sk-thm-smooth-purity,
proposition `prop-pur-smooth-purity-naturality-cover`, order 2015
(blueprint: prop-pur-smooth-purity-naturality-cover).

Proof (the node's six steps; composition below is right to left, as in the node).
1. Write `M_K = Lf^*K`, `T = Λ_X(d)[2d]`, `ω = Rf^!Λ_Y`, and `γ_K = θ_K (1 ⊗ Π_f⁻¹) τ_K`
   (def-pur-smooth-purity-map). The adjoint of `θ_K` under `Rf_! ⊣ Rf^!` is `a_K`: tensor
   symmetry, the inverse projection map `PF⁻¹`, the fixed counit `ε_{f,Λ_Y} ⊗ 1_K` and the
   unitor (def-pur-co-smoothness). For `u : K ⟶ K'` and `m = Lf^*u`, naturality of the
   projection isomorphism (fix-prop-projection-formula), symmetry and unitors gives
   `u a_K = a_{K'} Rf_!(m ⊗ 1_ω)`. Transposing through the natural Hom bijection
   (thm-sf-ambient-adjoint-class) gives `Rf^!u θ_K = θ_{K'} (m ⊗ 1_ω)`; the tensor formula
   (thm-pur-cohomological-smoothness) applies on this smooth finite-coefficient domain.
2. With `L = Λ_X(d)`, `τ_K` is the shift identification `(M_K ⊗ L)[2d] ≅ M_K ⊗ L[2d]`. On a
   K-flat model the total differentials `d_P ⊗ 1 + (-1)^p 1 ⊗ d_L` agree since `L` sits in
   degree zero and `2d` is even, and the identity commutes with maps in the first factor, so
   `τ_{K'} (m ⊗ 1_L)[2d] = (m ⊗ 1_T) τ_K`. By the bifunctor law
   (lem-weil-derived-tensor-functorial), `(m ⊗ 1_ω)(1 ⊗ Π_f⁻¹) = (1 ⊗ Π_f⁻¹)(m ⊗ 1_T)`.
3. Pasting: `Rf^!u γ_K = θ_{K'} (m ⊗ 1_ω)(1 ⊗ Π_f⁻¹) τ_K = θ_{K'} (1 ⊗ Π_f⁻¹)(m ⊗ 1_T) τ_K
   = γ_{K'} (m ⊗ 1_L)[2d]`, the first conjunct (in Lean's left-to-right order).
4. `Π_f` is the specified diagonal orientation (thm-pur-diagonal-dualizing-object); the DNC
   comparison normalized on standard pairs is unique (thm-pur-dnc-invariance; `X` is
   Noetherian by lem-weil-pbc-finite-type-over-noetherian and `ℓ ≠ char k`), and the
   vector-bundle integration is unique (thm-amb-vector-bundle-purity). So coordinate, cover
   or frame choices do not change `Π_f`; no arbitrary isomorphism `ω ≅ T` is selected.
5. Changing a K-flat model of `M_K` is absorbed by the canonical resolution comparison with
   its identity and cocycle laws (lem-weil-derived-tensor-resolution-independent); tensoring
   `Π_f⁻¹` and the shift identification commute with these comparisons.
6. The adjoint `a_K` determines `θ_K` by injectivity of the Hom bijection; changing the
   compactification or etale-origin witness identifies the Hom bijections canonically
   (thm-sf-ambient-adjoint-class), compatibly with the projection formula. Hence, for any two
   etale representatives `K₀`, `K₀'` with comparison isomorphisms `e`, `e'`, the two
   presentation composites `(1 ⊗ Π_f⁻¹) ≫ θ` agree, which is the second conjunct.
-/
theorem smoothPurityMap_naturality_choice_independence
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K K' : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K)
    (hK' : finiteTorConstructible P.coefficients.l P.extension P.level
      P.level_pos Y K')
    (u : K ⟶ K') :
    P.smoothPurityMap f d K hK ≫
        (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u)) =
      (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
          ((shiftFunctor _ (2 * (d : ℤ))).map
            (((smoothPurityTensor P.Coefficient X).map
              ((P.smoothPurityPullback f).map
                ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.map u))).app
              ((P.diagonalTwist X d)⟦-(2 * (d : ℤ))⟧))) ≫
        P.smoothPurityMap f d K' hK' ∧
    ∀ (K₀ K₀' : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀ ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
      (e' : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K₀' ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K),
      P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀ e =
        P.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of P.field.k))
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) K₀' e' := by
  sorry

end WeilConjectures.PurityFiniteSetting
