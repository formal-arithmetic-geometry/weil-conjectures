/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.ShiftedKoszulAugmentation
public import Sheaf.AlgebraicGeometry.FiniteLocalizationPowerColimit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # The degreewise Koszul Hom power diagram

Source: Stacks Project, perfect.tex Tags 08CX and 0911.
(blueprint: lem-sc-koszul-hom-degree-power-diagram).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
  (M : CochainComplex (ModuleCat.{u} A) ℤ)

/-- Precomposition as a map of additive Hom complexes.
Source: Stacks, Tag 0A8H (blueprint: lem-sc-koszul-hom-degree-power-diagram). -/
def additiveHomPrecomp {L L' : CochainComplex (ModuleCat.{u} A) ℤ} (a : L' ⟶ L) :
    CochainComplex.HomComplex L M ⟶ CochainComplex.HomComplex L' M where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ (Cochain.ofHom a).comp z (zero_add n)
      map_zero' := Cochain.comp_zero _ _
      map_add' := fun x y ↦ Cochain.comp_add _ x y _ }
  comm' n m _ := by
    ext z
    exact δ_ofHom_comp a z m

/-- The shifted tail definitions agree, including their negative differential.
Source: Stacks, Tag 08CX (blueprint: lem-sc-koszul-hom-degree-power-diagram). -/
theorem shiftedKoszul_eq_openTail (e : ℕ) :
    shiftedKoszulComplex A r (fun i ↦ f i ^ (e + 1)) =
      (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat := by
  rfl

/-- The actual sequential system of additive Hom complexes, using the diagonal
exterior-power transition and precomposition.
Source: Stacks, Tag 0911 (blueprint: lem-sc-koszul-hom-degree-power-diagram). -/
noncomputable def koszulAdditiveHomPowerDiagram :
    ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  Functor.ofSequence
    (X := fun e ↦ CochainComplex.HomComplex
      (shiftedKoszulComplex A r (fun i ↦ f i ^ (e + 1))) M)
    (fun e ↦ additiveHomPrecomp A M
      (eqToHom (shiftedKoszul_eq_openTail A r f (e + 1)) ≫
        HomologicalComplex.extendMap
          (koszulOpenTransition A r f e (e + 1) (Nat.le_succ e))
          ComplexShape.embeddingDownNat ≫
        eqToHom (shiftedKoszul_eq_openTail A r f e).symm))

/-- In one total degree the Koszul Hom power diagram is the finite family of
multiplication systems indexed by strictly increasing tuples.

Source: Stacks Project, perfect.tex Tag 0911, degreewise basis calculation
(blueprint: lem-sc-koszul-hom-degree-power-diagram).

Proof: in degree n, a Hom cochain is a family of linear maps from I^j to
M^(j+n). Extension by zero kills j>0. Exterior powers of the free rank-r
module vanish in degrees greater than r, so only j=-p with 0<=p<r remain.
The increasing (p+1)-tuples index the exterior basis of I^(-p)=K_(p+1).
Evaluation on this basis identifies linear maps to M^(n-p) with the product
of copies of M^(n-p). The finite product over p agrees with its direct sum.
The transition is the exterior power of the diagonal e_i |-> f_i e_i;
it multiplies each basis wedge by the product of its f_i. Precomposition
therefore becomes multiplication by that same product in the corresponding
coordinate. This verifies naturality on successor arrows; all arrows are
composites of these. If r=0 all terms are zero; for r=1 the sole coordinate
is M^n and the map multiplies by f_0. Empty tuple families contribute zero.
-/
theorem koszulHomDegreePowerDiagram (n : ℤ) :
    Nonempty ((koszulAdditiveHomPowerDiagram A r f M ⋙
      HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) n) ≅
      finiteLocalizationPowerDiagram A (Fin r)
        (fun p ↦ {t : Fin (p.val + 1) → Fin r // StrictMono t})
        (fun p ↦ M.X (n - (p.val : ℤ)))
        (fun p t ↦ ∏ i : Fin (p.val + 1), f (t.1 i))) := by sorry

end AlgebraicGeometry
