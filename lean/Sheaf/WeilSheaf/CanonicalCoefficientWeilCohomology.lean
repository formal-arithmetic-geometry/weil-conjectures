/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CoefficientCohomologyComparison
public import Sheaf.Paper.FixedPairTruncationCohomology

/-! # Signed standard cohomology of coefficient Frobenius pairs -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Standard cohomology with the finite-stage signed shift normalization retained.
Source: BBD 1.3; the finite-stage and common-stage normalizations of
fixedPairCommonTruncationCohomology.
(blueprint: def-sf-canonical-coefficient-weil-cohomology)

The shift is fixed on integral representatives by rational Roos normalization and
on arbitrary common-stage maps by the finite-stage inclusion formula. The truncation
comparisons are uniquely fixed by their counit and unit equations. Thus the selected
data determine the induced cohomology pair up to its canonical intertwining isomorphism;
no arbitrary realization or object of a mere existence theorem is used. The underlying
functor is exactly the two standard truncations followed by the degree shift. -/
def canonicalCoefficientWeilCohomology (n : ℤ) :
    Pairs P X₀ ⥤ sfCommonStageWeilSheaf P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar := by
  let h := fixedPairCommonTruncationCohomology P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar
  let q := h.choose_spec.choose
  letI := q
  let hc := h.choose_spec.choose_spec.2.2
  let cLE := hc.choose
  let cGE := hc.choose_spec.choose
  let H := (IsoAlgebra.mapOfNatIso (cLE n) ⋙ IsoAlgebra.mapOfNatIso (cGE n)) ⋙
    IsoAlgebra.mapOfNatIso ((sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l
      P.coefficients.different X₀ P.coefficients.Qbar).commShiftIso n)
  refine ((sfCommonStageHeartProperty P.coefficients.l
    (P.field.geometricFiber X₀).left P.coefficients.Qbar).inverseImage
      (sfCommonStageWeilForget P.field P.coefficients.l P.coefficients.different
        X₀ P.coefficients.Qbar)).lift H ?_
  intro K
  rw [← (sfCommonStageHeart_properties P.coefficients.l
    (P.field.geometricFiber X₀).left P.coefficients.Qbar P.field
      P.coefficients.different).1]
  have hn := hc.choose_spec.choose_spec.2.2.2 n
  obtain ⟨H', hH', _, hheart⟩ := hn
  subst H'
  exact hheart K

end WeilConjectures.NativeCoefficientCohomology
