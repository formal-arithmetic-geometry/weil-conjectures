/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.Paper.CoefficientCohomologyModules
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-! # Independence of the local Frobenius operator from the embedding

Source: Weil conjectures blueprint, `sec-poincare-duality/sk-lem-finite`,
`lem-weil-local-frobenius-conjugacy-class.md`, order 2429
(blueprint: lem-weil-local-frobenius-conjugacy-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- For two compatible residue-field embeddings, the local Frobenius maps are conjugate.
Proof plan from the source: the residue field is a finite extension of `k₀`, so its two
`k₀`-embeddings differ by a power of geometric Frobenius.  Reparametrized geometric
points `zᵢ` therefore form a finite Frobenius orbit and satisfy the pointwise return
equations.  The point-fibre transport maps `τᵢ` are natural isomorphisms, and their
iterated composites `Qᵢ,ₙ` agree with the specified iterated transport by induction,
using pullback-composition coherence.  If `Aᵢ` is the transport followed by the Weil
structure, the corresponding cyclic products `Pᵢ,ₙ` agree with the local return
operators by a second induction using naturality.  At the orbit length, consecutive
cyclic products satisfy `Fᵢ Aᵢ = Aᵢ Fᵢ₊₁`; the product from the first embedding to the
second consequently gives an isomorphism intertwining the two operators.  Applying
the coefficient cohomology functor yields the displayed conjugacy, including zero
cohomology modules.
Source: Weil conjectures blueprint,
`sec-poincare-duality/sk-lem-finite/lem-weil-local-frobenius-conjugacy-class.md`,
order 2429 (blueprint: lem-weil-local-frobenius-conjugacy-class). -/
theorem localFrobeniusConjugacyClass (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : sfWeilComplex D c.l c.different Y₀ E.val)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι ι' : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (hι' : ι'.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (j : ℤ) :
    ∃ e :
      (DerivedCategory.coefficientFdCohomology E.val j).obj
        (localPointComplex c.l E.val D c.different Y₀ K
          (localClosedPoint D Y₀ y ι hι)) ≅
      (DerivedCategory.coefficientFdCohomology E.val j).obj
        (localPointComplex c.l E.val D c.different Y₀ K
          (localClosedPoint D Y₀ y ι' hι')),
      e.hom ≫ (localClosedFrobeniusCohomology c.l E.val D c.different Y₀ K y
        ι' hι' j) =
      (localClosedFrobeniusCohomology c.l E.val D c.different Y₀ K y
        ι hι j) ≫ e.hom := by
  sorry

end WeilConjectures
