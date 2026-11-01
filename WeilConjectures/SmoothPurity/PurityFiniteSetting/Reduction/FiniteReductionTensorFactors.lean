/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorSource
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons

/-! # The two factors of the finite purity tensor map

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 2–3.
(blueprint: def-pur-finite-reduction-tensor-factors)

The comparison on the intermediate tensor with omega uses the exceptional coefficient
mate on omega, not the diagonal orientation or the purity map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The inverse diagonal orientation tensored with the identity, then realized.
Source: def-pur-smooth-purity-map, first factor of gamma^sm
(blueprint: def-pur-finite-reduction-tensor-factors). -/
def finitePurityInverseOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :=
  letI := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  letI : HasCompactification f := inferInstance
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).map
          (P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))).inv)

/-- The specified theta in a supplied etale presentation, then realized.
Source: def-pur-smooth-purity-map, second factor of gamma^sm
(blueprint: def-pur-finite-reduction-tensor-factors). -/
def finitePurityTheta (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (J : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅
        (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) :=
  letI := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  letI : HasCompactification f := inferInstance
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.smoothPurityTheta f
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) J e)

/-- The coefficient comparison on the intermediate tensor M tensor omega.
Source: reduction proof Step 2, scalar tensorator and exceptional-unit mate
(blueprint: def-pur-finite-reduction-tensor-factors). -/
def finiteReductionTensorOmegaComparison
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :=
  letI := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  letI : HasCompactification f := inferInstance
  let Q := P.finiteReductionSetting m hm
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let p := (P.finiteTensorPullbackComparison m hm hmn f
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)).hom ≫
    (Q.smoothPurityPullback f).map
      (P.finiteReductionTensorInputComparison m hm hmn Y K).hom
  (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X).hom.app
        (((smoothPurityTensor P.Coefficient X).obj M).obj (P.diagonalDualizing f)) ≫
    (Scheme.sfIntrinsicDerivedEquivalence X Q.Ring).functor.map
      ((P.finiteTensorCore m hm hmn X).μIso M (P.diagonalDualizing f)).inv ≫
    (Scheme.sfIntrinsicDerivedEquivalence X Q.Ring).functor.map
      (p ⊗ₘ FiniteDiagonalReduction.omegaMap P m hm hmn f
        (Y ↘ Spec (.of P.field.k)))

end Morphism
end WeilConjectures.PurityFiniteSetting
