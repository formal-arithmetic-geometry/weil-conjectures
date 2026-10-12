/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A chain map of towers induces the kernel and signed-cone comparison maps,
with explicit components. No homotopy or reverse map is required.

Proof: Put U_p = eP_p.hom ≫ Pi.map(u_p) ≫ ePJ_p.inv. Product projections,
hP, hPJ and the chain-map equation for u give d_P U = U d_PJ. Naturality
of each u_p with respect to n+1 → n gives s U = U sJ, using
towerTransitionEndomorphism_natural_backward. Therefore iota_p U_p kills
sJ_p. Lift it through the limiting kernel fork hLJ_p to obtain lU_p. These
components commute with differentials: compose both sides with iJ_q, use
the chain-map equations for iota and iJ and for U, and use that iJ_q is mono.
For each p define cU_(p+1) by eC_p.hom ≫ biprod.map(U_p,U_(p+1)) ≫ eCJ_p.inv.
Every integer degree is uniquely p+1. The signed cone differential equation
for cU reduces, after the two biproduct projections, to the differential and
transition commutation equations for U; the other differentials vanish by
complex shape. Finally compare eta cU and lU etaJ after eCJ_p.hom: both have
first component zero and second component iota_(p+1) U_(p+1). This proves
the square and the two displayed component formulas. The kernel universal
property and the cone isomorphisms also determine these maps uniquely.

Source: the agent-written naturality extension in the docstring of
roos_comparison_homotopy_retract (lem-weil-derived-limit-roos-complex);
Stacks Project, Derived Categories, Tag 070M provides the underlying Roos setup.
(blueprint: lem-weil-roos-comparison-maps). -/
theorem roos_comparison_maps
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (u : I ⟶ J)
    (P L C : CochainComplex A ℤ)
    (eP : ∀ p : ℤ, P.X p ≅ ∏ᶜ (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)))
    (hP : ∀ p q : ℤ, P.d p q ≫ (eP q).hom =
      (eP p).hom ≫ Limits.Pi.map (fun n ↦ (I.d p q).app (Opposite.op n)))
    (oneSubS : P ⟶ P)
    (hS : ∀ p : ℤ, oneSubS.f p = (eP p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (eP p).inv)
    (iota : L ⟶ P)
    (hKernel : ∀ p : ℤ, iota.f p ≫ oneSubS.f p = 0)
    (hL : ∀ p : ℤ, IsLimit (KernelFork.ofι (iota.f p) (hKernel p)))
    (eC : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (hC : ∀ p : ℤ, C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
      (eC p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ oneSubS.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)))
    (eta : L ⟶ C)
    (hEta : ∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom =
      biprod.lift 0 (iota.f (p + 1)))
    (PJ LJ CJ : CochainComplex A ℤ)
    (ePJ : ∀ p : ℤ, PJ.X p ≅ ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n)))
    (hPJ : ∀ p q : ℤ, PJ.d p q ≫ (ePJ q).hom =
      (ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n)))
    (sJ : PJ ⟶ PJ)
    (hSJ : ∀ p : ℤ, sJ.f p = (ePJ p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (ePJ p).inv)
    (iJ : LJ ⟶ PJ)
    (hKJ : ∀ p : ℤ, iJ.f p ≫ sJ.f p = 0)
    (hLJ : ∀ p : ℤ, IsLimit (KernelFork.ofι (iJ.f p) (hKJ p)))
    (eCJ : ∀ p : ℤ, CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1))
    (hCJ : ∀ p : ℤ, CJ.d (p + 1) (p + 1 + 1) ≫ (eCJ (p + 1)).hom =
      (eCJ p).hom ≫ biprod.lift
        (-(biprod.fst ≫ PJ.d p (p + 1)) - biprod.snd ≫ sJ.f (p + 1))
        (biprod.snd ≫ PJ.d (p + 1) (p + 1 + 1)))
    (etaJ : LJ ⟶ CJ)
    (hEtaJ : ∀ p : ℤ, etaJ.f (p + 1) ≫ (eCJ p).hom =
      biprod.lift 0 (iJ.f (p + 1)))
    : ∃ (lU : L ⟶ LJ) (cU : C ⟶ CJ),
      lU ≫ etaJ = eta ≫ cU ∧
      (∀ p : ℤ, lU.f p ≫ iJ.f p = iota.f p ≫ (eP p).hom ≫
        Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv) ∧
      (∀ p : ℤ, cU.f (p + 1) ≫ (eCJ p).hom = (eC p).hom ≫ biprod.map
        ((eP p).hom ≫ Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫
          (ePJ p).inv)
        ((eP (p + 1)).hom ≫
          Limits.Pi.map (fun n ↦ (u.f (p + 1)).app (Opposite.op n)) ≫
          (ePJ (p + 1)).inv)) := by
  sorry

end CategoryTheory
