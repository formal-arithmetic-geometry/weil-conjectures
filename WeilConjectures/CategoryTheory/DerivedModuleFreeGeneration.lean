/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.DerivedModuleCellularFiltration
import WeilConjectures.CategoryTheory.DerivedModuleFiltrationTelescope

/-! # Generation of a module derived category by shifts of the ring

Source: literature/stacks-project/more-algebra.tex, Remark 15.60.11 (Tag 09PB).

The property in the conclusion is the semantic description of the smallest full
subcategory containing the shifts of the free rank-one module and closed under
set-indexed coproducts, distinguished triangles, and retracts.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every object of the derived category of `R`-modules is generated from the shifts
of the free rank-one module `R[0]` (`singleFunctor 0`) by coproducts indexed in the
modules' universe, distinguished triangles (third vertex), and retracts. `R` is
commutative, as rings are in the source.
Source: More on Algebra, Remark 15.60.11 (Tag 09PB) -/
theorem derivedModuleFreeGeneration (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    ∀ (P : ObjectProperty (DerivedCategory (ModuleCat.{max u v} R))),
      (∀ (n : ℤ), P (((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} R) 0).obj (ModuleCat.of R (ULift.{v} R)))⟦n⟧)) →
      (∀ {I : Type (max u v)} (F : I → DerivedCategory (ModuleCat.{max u v} R))
        (S : DerivedCategory (ModuleCat.{max u v} R))
        (ι : ∀ i : I, F i ⟶ S), IsColimit (Cofan.mk S ι) →
        (∀ i : I, P (F i)) → P S) →
      (∀ (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{max u v} R))),
        T ∈ Pretriangulated.distinguishedTriangles →
        P T.obj₁ → P T.obj₂ → P T.obj₃) →
      (∀ {X Y : DerivedCategory (ModuleCat.{max u v} R)},
        Retract X Y → P Y → P X) →
      P K := by
  intro P hgen hcop htri hretract
  obtain ⟨L, F, ι, step, hKL, hzero, hmono, hcompat, hexhaustive, hcell⟩ :=
    derivedModuleCellularFiltration R K
  have hF : ∀ n, P (DerivedCategory.Q.obj (F n)) := by
    intro n
    induction n with
    | zero =>
      let E : Type (max u v) := PEmpty
      let emptyFamily : E → DerivedCategory (ModuleCat.{max u v} R) :=
        fun e => PEmpty.elim e
      let j : ∀ e : E, emptyFamily e ⟶ DerivedCategory.Q.obj (F 0) :=
        fun e => PEmpty.elim e
      have hc : IsColimit (Cofan.mk (DerivedCategory.Q.obj (F 0)) j) :=
        Cofan.IsColimit.mk _ (fun s => hzero.to_ s.pt)
          (fun _ e => PEmpty.elim e) (fun _ _ _ => hzero.eq_of_src _ _)
      exact hcop emptyFamily _ j hc (fun e => PEmpty.elim e)
    | succ n ih =>
      obtain ⟨I, degree, G, j, hc, a, b, c, ht⟩ := hcell n
      have hG : P G := hcop _ G j hc.some (fun i => hgen (degree i))
      exact htri (Pretriangulated.Triangle.mk a b c) ht hG ih
  obtain ⟨S, j, hc, a, b, c, ht⟩ :=
    derivedModuleFiltrationTelescope R L F ι step hmono hcompat hexhaustive
  have hS : P S := hcop _ S j hc.some (fun n => hF n.down)
  have hL : P (DerivedCategory.Q.obj L) :=
    htri (Pretriangulated.Triangle.mk a b c) ht hS hS
  exact hretract (Retract.ofIso hKL.some) hL

end CategoryTheory
