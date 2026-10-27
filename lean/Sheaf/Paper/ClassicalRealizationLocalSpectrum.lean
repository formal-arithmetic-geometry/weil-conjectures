/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClassicalWeilFiltrationTransportData

/-! # Local spectra of a normalized classical realization

Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS Section 6.8.
(blueprint: lem-zl-classical-realization-local-spectrum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- A normalized return path exists, and every such path computes exactly the
common-stage local spectrum. This concerns one closed point and one classical object;
it asserts neither weight conditions nor any finite filtration realization.
Source: blueprint latest, real-mixed-by-curves, paragraph 1; Weil II (1.1.8)--(1.1.10);
BS 6.8.4(1),(4), 6.8.15
(blueprint: lem-zl-classical-realization-local-spectrum).

Proof:
For the two-fibre API currently stated with small Omega, first use an algebraic
closure in the scheme universe, its unique algebraic-closure equivalence to Omega,
and transport coefficient fields, tensor modules and normalized fibre isomorphisms
along that equivalence. The finite-level germ and tensor-unit formulas are unchanged.
This is coefficient universe transport, not a universe change of the geometric base.
1. At the closed point use the closed-point return equality. Iterating the orbit
recursion identifies its endpoint with the positive-power Frobenius composite.
Precomposition of finite-etale cover lifts by the point Frobenius gives an invertible
natural transformation to this endpoint; inverse point Frobenius supplies its inverse.
This produces the normalized beta. Two such beta agree on all cover objects and
all lifts, so their induced inverse-limit adic path maps agree.
2. Apply normalized_two_fibre_comparison at a finite Weil representative of R(F).
The normalized completed point comparison is natural in the representative and its
Weil maps. Its coefficient extension square identifies all further fields, hence
any presentation in the existential definition of SfPunctualEigenvalue gives the
same operator up to conjugacy. Use singleton finite diagram realization to obtain
a finite Weil representative in the reverse direction.
3. Apply classical_local_frobenius_iterate_comparison for the supplied R with period
the closed-point residue degree. Its point-transport, return and Weil-factor squares
identify the conjugate operator with zlClassicalLocal for the beta of step 1.
Induction on the literal orbit recursion identifies the two endpoint conventions.
The path independence of step 1 gives the same equation for every permitted beta.
4. The conjugating linear isomorphism sends each nonzero eigenvector to a nonzero
eigenvector with the same eigenvalue. Its inverse proves the converse. This works
without a nonzero-rank assumption; zero fibres have no nonzero eigenvectors. -/
theorem zl_classical_realization_local_spectrum
    (R : ZlClassicalRealization D l hl Ω Y₀) (F : ZlClassicalWeil D l Ω Y₀)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    let x := localClosedPoint D Y₀ y ι hι
    let d := localClosedPointDegree D Y₀ y
    (∃ β : FiniteEtale.fiber x ≅
        FiniteEtale.fiber (zlClassicalOrbitPoint D Y₀ x d),
      ∀ (P : (D.geometricFiber Y₀).left.FiniteEtale)
        (z : (FiniteEtale.fiber x).obj P),
        (β.hom.app P z).left =
          localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ z.left) ∧
    (∀ (β : FiniteEtale.fiber x ≅
        FiniteEtale.fiber (zlClassicalOrbitPoint D Y₀ x d)),
      (∀ (P : (D.geometricFiber Y₀).left.FiniteEtale)
        (z : (FiniteEtale.fiber x).obj P),
        (β.hom.app P z).left =
          localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ z.left) →
      ∀ α : Ω,
        SfPunctualEigenvalue D l hl Ω Y₀ ((R.weil D l hl Ω Y₀).obj F) y α ↔
          Module.End.HasEigenvalue (zlClassicalLocal D l Ω Y₀ F x d β).hom α) := by sorry

end WeilConjectures
