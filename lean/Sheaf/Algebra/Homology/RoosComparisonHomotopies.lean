/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The maps induced by a homotopy retraction of towers form homotopy
retractions of the termwise kernels and signed cones. The four component
hypotheses specify induced maps, rather than arbitrary maps of these complexes.

Proof: For hr.hom p q form H_pq = eP_p.hom ≫ Pi.map((hr.hom p q).app) ≫
eP_q.inv; put zero in the degrees where q+1 ≠ p. Product projections and
the homotopy equation for hr yield U_p R_p - id = d H + H d. Each component
of hr is a natural transformation of towers, so s_p H_pq = H_pq s_q.
Consequently iota_p H_pq kills s_q and factors uniquely through iota_q by
hL_q; use this lift as the kernel homotopy component. Compose its homotopy
equation with iota_p. The factorization formulas, hlU and hlR reduce it to
the product homotopy equation; monicity of iota_p proves the equation in L.
On C in degree p+1 define the degree-minus-one component, under eC_p and
eC_(p-1), to be the diagonal map (-H_(p,p-1), H_(p+1,p)). Set all other
components zero. By hcU, hcR and Pi.map composition the composite cU cR
is the diagonal product of U R in these presentations. Multiplying the two
signed differential matrices gives the homotopy equation: the diagonal
entries are precisely U R - id, and the off-diagonal entry is
-s_(p+1) H_(p+1,p) + H_(p+1,p) s_p, which vanishes by naturality. All nonadjacent
components vanish by the cochain shape. Thus the two constructed families
satisfy the required Homotopy equations. No exactness of products, split
transition maps, or K-injectivity is used.

Source: the agent-written homotopy-invariance extension in the docstring of
roos_comparison_homotopy_retract (lem-weil-derived-limit-roos-complex);
Stacks Project, Derived Categories, Tag 070M provides the underlying Roos setup.
(blueprint: lem-weil-roos-comparison-homotopies). -/
theorem roos_comparison_homotopies
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (u : I ⟶ J) (r : J ⟶ I) (hr : Homotopy (u ≫ r) (𝟙 I))
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
    (lU : L ⟶ LJ) (cU : C ⟶ CJ) (lR : LJ ⟶ L) (cR : CJ ⟶ C)
    (hlU : ∀ p : ℤ, lU.f p ≫ iJ.f p = iota.f p ≫ (eP p).hom ≫
      Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv)
    (hcU : ∀ p : ℤ, cU.f (p + 1) ≫ (eCJ p).hom = (eC p).hom ≫ biprod.map
      ((eP p).hom ≫ Limits.Pi.map (fun n ↦ (u.f p).app (Opposite.op n)) ≫ (ePJ p).inv)
      ((eP (p + 1)).hom ≫
        Limits.Pi.map (fun n ↦ (u.f (p + 1)).app (Opposite.op n)) ≫ (ePJ (p + 1)).inv))
    (hlR : ∀ p : ℤ, lR.f p ≫ iota.f p = iJ.f p ≫ (ePJ p).hom ≫
      Limits.Pi.map (fun n ↦ (r.f p).app (Opposite.op n)) ≫ (eP p).inv)
    (hcR : ∀ p : ℤ, cR.f (p + 1) ≫ (eC p).hom = (eCJ p).hom ≫ biprod.map
      ((ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (r.f p).app (Opposite.op n)) ≫ (eP p).inv)
      ((ePJ (p + 1)).hom ≫
        Limits.Pi.map (fun n ↦ (r.f (p + 1)).app (Opposite.op n)) ≫ (eP (p + 1)).inv))
    : Nonempty (Homotopy (lU ≫ lR) (𝟙 L)) ∧
      Nonempty (Homotopy (cU ≫ cR) (𝟙 C)) := by
  sorry

end CategoryTheory
