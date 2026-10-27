/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClassicalWeilFiltrationTransportData

/-! # Normalized fibres of a realized filtration diagram

Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS Section 6.8.
(blueprint: lem-zl-classical-filtration-diagram-fibres).
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

/-- Compatible all-period fibre comparisons for an already realized diagram.
This asserts no existence of a finite-stage diagram or heart exactness.
Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS 6.8.4(1),(4), 6.8.15
(blueprint: lem-zl-classical-filtration-diagram-fibres).

Proof:
For the two-fibre API currently stated with small Omega, first use an algebraic
closure in the scheme universe, its unique algebraic-closure equivalence to Omega,
and transport coefficient fields, tensor modules and normalized fibre isomorphisms
along that equivalence. The finite-level germ and tensor-unit formulas are unchanged.
This is coefficient universe transport, not a universe change of the geometric base.
1. For each finite-stage term and quotient, compose its normalized extended H^0
point-fibre identification with the fibre of its supplied Weil isomorphism a or b.
Then use the normalized comparison for the supplied R, on the corresponding
classical object. This is the same comparison at all positive return periods.
The normalized_two_fibre_comparison fixes coefficient extension and point sections
on finite-level germs and inverse-limit projections, so no new fibre path is chosen.
2. Apply classical_local_frobenius_iterate_comparison to R. Its factor squares
intertwine point transport, the semilinear return compositor and iterated Weil maps.
Identify the orbit-point recursion with the positive-power endpoints inductively.
The finite-etale reparametrization at the return, followed by that endpoint equality,
sends each cover lift z to the specified point Frobenius composite. This gives the
existential beta and the local_operator field for every term and quotient.
3. Naturality of normalized point pullback, H^0, ulift and scalar extension takes
ha and hb to their corresponding fibre squares. Cancel the intermediate normalized
isomorphisms. Naturality of the comparison for R yields exactly the two displayed
identities, including zero maps and arbitrary quotient ranks. If r=0 there are no
quotient or arrow squares; if Y is empty all the point assertions are vacuous. -/
theorem zl_classical_filtration_diagram_fibres
    (R : ZlClassicalRealization D l hl Ω Y₀)
    (r : ℕ) (F : ZlClassicalFiltration D l Ω Y₀ r)
    (E : Padic.FiniteCoefficientFields l Ω)
    (M : ZlFiniteFiltration D l hl Ω Y₀ r E)
    (a : ∀ j : Fin (r + 1), sfWeilStageObject D l hl Y₀ Ω E (M.terms j) ≅
      ((R.weil D l hl Ω Y₀).obj (F.terms j)).obj)
    (b : ∀ j : Fin r, sfWeilStageObject D l hl Y₀ Ω E (M.quotients j) ≅
      ((R.weil D l hl Ω Y₀).obj (F.quotients j)).obj)
    (ha : ∀ j : Fin r,
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
          (M.inclusion j).hom.f ≫ (a j.succ).hom.hom.f =
        (a j.castSucc).hom.hom.f ≫
          ((R.weil D l hl Ω Y₀).map (F.inclusion j)).hom.hom.f)
    (hb : ∀ j : Fin r,
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
          (M.quotient j).hom.f ≫ (b j).hom.hom.f =
        (a j.succ).hom.hom.f ≫
          ((R.weil D l hl Ω Y₀).map (F.quotient j)).hom.hom.f) :
    ∃ (c : ∀ j : Fin (r + 1),
        ZlClassicalFibreComparison D l hl Ω Y₀ E (M.terms j) (F.terms j))
      (d : ∀ j : Fin r,
        ZlClassicalFibreComparison D l hl Ω Y₀ E (M.quotients j) (F.quotients j)),
      (∀ (j : Fin r) (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
        zlFiniteFibreMap D l hl Ω Y₀ E (M.inclusion j) x ≫
            ((c j.succ).fibre x).hom =
          ((c j.castSucc).fibre x).hom ≫
            etaleAlgebraicFiberMap l Ω x (F.inclusion j).hom.f) ∧
      (∀ (j : Fin r) (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
        zlFiniteFibreMap D l hl Ω Y₀ E (M.quotient j) x ≫
            ((d j).fibre x).hom =
          ((c j.succ).fibre x).hom ≫
            etaleAlgebraicFiberMap l Ω x (F.quotient j).hom.f) := by sorry

end WeilConjectures
