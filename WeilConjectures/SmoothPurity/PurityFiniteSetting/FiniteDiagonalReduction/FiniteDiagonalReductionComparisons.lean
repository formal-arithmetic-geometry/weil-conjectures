/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationScalarPresentation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.PurityDncCoefficientTransport

/-! # Canonical coefficient maps for the diagonal and normal section invariants

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: def-pur-finite-diagonal-reduction-comparisons).

The fixed-scalar pro-etale presentation is canonically equivalent to the intrinsic
one. All maps below are the published root-generator, scalar-unit and counit mates.
Positive affine coefficient levels are indexed by their predecessors, as in the
published supported-product API; no divisibility by a ramification index is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Coefficient map on omega_f, obtained from the reduced exceptional counit and unit.
Source: node proof Step 5
(blueprint: def-pur-finite-diagonal-reduction-comparisons). -/
@[irreducible]
def omegaMap :=
  letI := P.noetherian aY
  letI := Dnc.compactifiable P f aY
  presented (quotient P m hm hmn) X
    (P.diagonalDualizingComparison f)
    ((P.finiteReductionSetting m hm).diagonalDualizingComparison f)
    ((ordinaryScalar (quotient P m hm hmn) X).map (P.chartDualizingUnit f).inv ≫
      DncCoefficientTransport.dualizingMap (quotient P m hm hmn) f ≫
      ((P.finiteReductionSetting m hm).chartDualizingUnit f).hom)

/-- Coefficient map on the actual diagonal section invariant, with the canonical
pullback scalar mate followed by the exceptional counit mate.
Source: node proof Steps 5--7
(blueprint: def-pur-finite-diagonal-reduction-comparisons). -/
@[irreducible]
def diagonalSectionMap :=
  letI := P.noetherian aY
  letI := P.noetherian (f ≫ aY)
  letI := Dnc.compactifiable P (pullback.fst f f) (f ≫ aY)
  presented (quotient P m hm hmn) X
    (Dnc.sourceComparison P d (pullback.fst f f) (f ≫ aY) (pullback.diagonal f))
    (Dnc.sourceComparison (P.finiteReductionSetting m hm) d (pullback.fst f f)
      (f ≫ aY) (pullback.diagonal f))
    (DncCoefficientTransport.sectionMap (quotient P m hm hmn)
      (pullback.fst f f) (pullback.diagonal f))

/-- Coefficient map on the normal cone's actual augmentation section invariant.
The cone is the associated graded of the diagonal ideal, not an arbitrary bundle.
Source: node proof Steps 6--8
(blueprint: def-pur-finite-diagonal-reduction-comparisons). -/
@[irreducible]
def normalSectionMap :=
  letI := P.noetherian (f ≫ aY)
  letI := Dnc.normalCompactifiable P d (pullback.fst f f) (f ≫ aY)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  presented (quotient P m hm hmn) X
    (Dnc.normalComparison P d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f))
    (Dnc.normalComparison (P.finiteReductionSetting m hm) d (pullback.fst f f)
      (f ≫ aY) (pullback.diagonal f) (pullback.diagonal_fst f))
    (DncCoefficientTransport.sectionMap (quotient P m hm hmn)
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (pullback.diagonal f).normalConeZeroSection)

/-- The vector-bundle factor, with the published root-pullback transport, restricted
to the actual normal zero section. Source: node proof Step 8
(blueprint: def-pur-finite-diagonal-reduction-comparisons). -/
@[irreducible]
def vectorFactor :=
  P.chartDiagonalBeta d f aY
    (Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
      P.Coefficient P.diagonalExponent_annihilates)

end Diagonal

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
