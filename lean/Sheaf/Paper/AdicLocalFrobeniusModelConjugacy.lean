/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.LocalFrobeniusTrace

import Sheaf.Paper.LocalFrobeniusConjugacyClass
import Sheaf.Paper.LocalWeilModelTraceIndependence
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.IntegralPullbackComparisonRealization

/-!
# Local Frobenius conjugacy for common-stage Weil models

Source: blueprint `lem-weil-local-frobenius-conjugacy-class` and the finite-model
comparison in `def-fd-trace-function`, Deligne, Weil II (1.1.7)--(1.1.10).
The assertion compares operators in every cohomological degree, before taking
characteristic polynomials or imposing the heart condition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Isomorphic common-stage Weil models give conjugate local operators after scalar
extension to the coefficient closure, independently of the residue-field embedding.
Source: blueprint `lem-weil-local-frobenius-conjugacy-class`, and the finite-model
comparison in `def-fd-trace-function`; Deligne, Weil II (1.1.7)--(1.1.10).

Proof: represent the given isomorphism, its inverse, the two Weil structures and
all their commutation and inverse equations at a common finite coefficient stage.
The representative/equality criterion for common-stage Hom groups permits enlarging
that stage until every equation holds. Pulling the isomorphism to the chosen geometric
point then intertwines the iterated Weil structures. Naturality of point transport
and the specified pullback-composition comparisons intertwines each of the three
factors of the local Frobenius operator. The scalar comparisons of point sections and
cohomology turn this into a conjugacy of the scalar-extended cohomology operators,
as in the degreewise clause of localWeilModelTraceIndependence. For different residue
embeddings, first use localFrobeniusConjugacyClass: the embeddings differ by a power of
Frobenius on the finite residue extension, and the product of the intervening point
transports intertwines their cyclic return operators. Extend this conjugacy to the
coefficient closure and compose it with the model comparison. The scalar tensor tower
isomorphisms identify this composite with extension along the displayed coefficient
embeddings. This gives the asserted isomorphism and intertwining equation for every
integer degree, including zero-dimensional cohomology.
(blueprint: lem-wf-adic-local-frobenius-model-conjugacy). -/
theorem sfLocalFrobenius_model_conjugacy
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (L L' : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (K' : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L'))
    (hK : Nonempty (sfWeilStageObject D l hl Y₀ Ω L K ≅
      sfWeilStageObject D l hl Y₀ Ω L' K'))
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι ι' : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (hι' : ι'.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (j : ℤ) :
    ∃ e :
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) j).obj
          (localPointComplex l _ D hl Y₀ K (localClosedPoint D Y₀ y ι hι))) ≅
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L')).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L') j).obj
          (localPointComplex l _ D hl Y₀ K' (localClosedPoint D Y₀ y ι' hι'))),
      e.hom ≫ (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L')).map
          (localClosedFrobeniusCohomology l _ D hl Y₀ K' y ι' hι' j) =
        (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).map
          (localClosedFrobeniusCohomology l _ D hl Y₀ K y ι hι j) ≫ e.hom := by
  sorry

end WeilConjectures
