/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClassicalWeilFiltrationTransportData

/-! # Exact finite-stage classical filtration diagrams

Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS Section 6.8.
(blueprint: lem-zl-classical-filtration-exact-diagram).
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

/-- A single exact finite-stage diagram for the prescribed filtration, before any
local-operator or weight comparison is asserted.
Source: blueprint latest, real-mixed-by-curves, paragraph 1; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-filtration-exact-diagram).

Proof:
For the two-fibre API currently stated with small Omega, first use an algebraic
closure in the scheme universe, its unique algebraic-closure equivalence to Omega,
and transport coefficient fields, tensor modules and normalized fibre isomorphisms
along that equivalence. The finite-level germ and tensor-unit formulas are unchanged.
This is coefficient universe transport, not a universe change of the geometric base.
1. Use classical_finite_weil_diagram_realization for vertices Fin(r+1) + Fin r and
arrows the prescribed inclusions and quotient maps. Its finite expression equations
include each zero composite. Their classical validity follows from fibre exactness.
The normalized stages, inverse Weil maps and equivariance are for the supplied R.
2. The normalized_two_fibre_comparison identifies the H^0 normalized point fibres
of each realized arrow with its actual classical adic fibre. Transport injectivity,
exactness and surjectivity along these natural isomorphisms using F.exact. Transport
the zero fibre condition using F.zero. No integral lattice exactness is required.
3. Apply simultaneous_exactness to the resulting finite quiver presentation and
short complexes. It supplies one coefficient field and exact finite-stage models,
including inverse Weil maps and the original common-stage Hom classes. The same
fibre criterion identifies the initial object with zero, in both hearts. Lift this
identification to the Weil heart; its unique maps are automatically equivariant.
4. Compose the diagram's Weil comparisons with the prescribed classical vertex
isomorphisms. Naturality gives the two displayed arrow equations. Project the heart
membership and short exactness fields to the raw finite heart. For r=0 the arrow
family is empty and only the zero vertex remains; empty Y and rank zero use the
zero lattice, with no choice of a nonzero vector or geometric point. -/
theorem zl_classical_filtration_exact_diagram
    (R : ZlClassicalRealization D l hl Ω Y₀)
    (r : ℕ) (F : ZlClassicalFiltration D l Ω Y₀ r) :
    ∃ (E : Padic.FiniteCoefficientFields l Ω)
      (M : ZlFiniteFiltration D l hl Ω Y₀ r E)
      (a : ∀ j : Fin (r + 1), sfWeilStageObject D l hl Y₀ Ω E (M.terms j) ≅
        ((R.weil D l hl Ω Y₀).obj (F.terms j)).obj)
      (b : ∀ j : Fin r, sfWeilStageObject D l hl Y₀ Ω E (M.quotients j) ≅
        ((R.weil D l hl Ω Y₀).obj (F.quotients j)).obj),
      (∀ j : Fin r,
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
            (M.inclusion j).hom.f ≫ (a j.succ).hom.hom.f =
          (a j.castSucc).hom.hom.f ≫
            ((R.weil D l hl Ω Y₀).map (F.inclusion j)).hom.hom.f) ∧
      (∀ j : Fin r,
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
            (M.quotient j).hom.f ≫ (b j).hom.hom.f =
          (a j.succ).hom.hom.f ≫
            ((R.weil D l hl Ω Y₀).map (F.quotient j)).hom.hom.f) ∧
      IsZero ((R.weil D l hl Ω Y₀).obj (F.terms 0)) ∧
      (∀ j : Fin r, ∃ h :
        (R.weil D l hl Ω Y₀).map (F.inclusion j) ≫
          (R.weil D l hl Ω Y₀).map (F.quotient j) = 0,
        (ShortComplex.mk _ _ h).ShortExact) := by sorry

end WeilConjectures
