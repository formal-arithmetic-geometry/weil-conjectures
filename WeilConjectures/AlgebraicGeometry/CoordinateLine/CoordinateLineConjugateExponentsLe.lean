/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.NativeCoordinateLine.NativeCoordinateLineConjugateExponents

/-! Source-comparison transport for coordinate-line exponent changes.

The displayed equality is the naturality square for the realization of the
ordinary tensor source.  It is kept separate from the ordinary conjugate
calculation so that the two genuinely independent compatibilities can be
checked independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

/-- Ordinary source transition induced by the finite root-power comparison. -/
def coordinate_line_ordinary_source_transition
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (Ke : Etale.DerivedCategoryModule (Ring P) T) :
    AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke ≅
      AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) T r' hA' Ke := by
  unfold AffineLinePurity.etaleSource AffineLinePurity.ordinarySourceObject
  exact ((Etale.derivedTensor (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback (Ring P)
        (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)).mapIso
    (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) T r hA) ≪≫
      (Etale.ordinaryFinitePullback (Ring P) (ProjectiveLine.affineChart T)).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso
            (NativeCoordinateLine.transition P (ProjectiveLine T)
              ((ProjectiveLine T ↘ T) ≫ aT) r r' hA hA'))) ≪≫
      (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
        (P.level - 1) T r' hA')).symm)

/-- Naturality of the source comparison under the coefficient twist isomorphism.
Source: the source-comparison naturality square in the final paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-conjugate-exponents-le).

Proof: write `C` for the exact site comparison on `X = A¹_T` and `w` for the
isomorphism `etaleCoefficient r ≅ etaleCoefficient r'` obtained, through
`etaleCoefficient_eq`, by pulling back along the affine chart the root-power
transition `τ = ρ_{M,r'} ∘ ρ_{M,r}⁻¹` (`M = max r r'`) placed in degree zero and
shifted by two; by definition `coordinate_line_ordinary_source_transition` is the
derived tensor with `p^*Ke` applied to `w`.
1. `sourceComparison` is `C` of an `eqToIso`, then `realizedTensorComparison`
   for the coefficient `etaleCoefficient r`, then an `eqToIso`. The realized
   tensor/pullback comparison is natural in the coefficient object, so
   `sourceComparison r⁻¹ ≫ C.map q = tensorCoefficientIso (C.mapIso w) ≫
   sourceComparison r'⁻¹`; the `eqToIso` coordinate changes cancel by proof
   irrelevance.
2. It remains that `coefficientTwistIso r ≪≫ (coefficientTwistIso r')⁻¹` equals
   `C.mapIso w` in these coordinates. Unfolding `coefficientTwistIso` gives
   `comparedLinePullback` followed by `twistDerived`. The compared pullback is
   natural in the finite line, and the pulled-back `τ` is again the unique
   root-power-normalized comparison of `twistCompatibility`. The identification
   `twistDerived` at level `a` is induced by the projection of the inverse-limit
   Tate tower to `μ_{ℓ^{a+1}} ⊗ A`; the tower transitions are `u ↦ u^ℓ`, so the
   projection at level `a` is `ρ_{b,a}` after the projection at level `b`. Hence
   `twistDerived r' ∘ C τ = twistDerived r`, which is the required equality.
3. Tensoring with `Lp^*K` (`tensorCoefficientIso` is `mapIso` of the derived
   tensor, hence functorial) and combining 1 and 2 gives the displayed square. -/
theorem coordinate_line_source_comparison_naturality
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (tensorCoefficientIso (Ring P) T _ _
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm)
      K.obj).hom ≫
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r' hA' K.obj Ke eK).inv =
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
        (coordinate_line_ordinary_source_transition P T aT r r' hA hA' Ke).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CoordinateLine
