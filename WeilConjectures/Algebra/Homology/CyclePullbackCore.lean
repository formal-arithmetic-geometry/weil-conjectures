/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Abelian.Basic

import WeilConjectures.Algebra.Homology.CyclePullbackLaws
import WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison

/-!
# Structural cycle-pullback construction

This is the recursive construction step of the cycle-pullback argument.
The degreewise comparison records the defining kernel-pullback geometry,
without asserting the generalized-element lifting consequence.

## References

* Stacks Project, Derived Categories, Tag 05T7 (1)
* Stacks Project, Cohomology on Sites, Tag 06YS
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Without any epimorphism assumption, the descending construction identifies each term
at or below the bound with T of the pullback of F and the next cycles. The cover followed
by the pullback projections defines its augmentation and differential. -/
theorem exists_functorial_cyclePullback_core {A : Type u} [Category.{v} A] [Abelian A]
    (S : ObjectProperty A) (hzero : ∀ X : A, IsZero X → S X) (T : A ⥤ A)
    (π : T ⟶ 𝟭 A) (hT : ∀ X : A, S (T.obj X))
    (N : ℤ) :
    let P : ObjectProperty (CochainComplex A ℤ) :=
      fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
    ∃ Q : P.FullSubcategory ⥤ CochainComplex A ℤ, ∃ ε : Q ⟶ P.ι,
      ∀ F : P.FullSubcategory,
        (∀ i : ℤ, S ((Q.obj F).X i)) ∧
        (∀ i : ℤ, N < i → IsZero ((Q.obj F).X i)) ∧
        ∀ (i : ℤ), i ≤ N →
          let d := (Q.obj F).d (i + 1) (i + 1 + 1)
          let f := F.obj.d i (i + 1)
          let g := kernel.ι d ≫ (ε.app F).f (i + 1)
          ∃ (c : (Q.obj F).X i ≅ T.obj (pullback f g)),
            c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g = (ε.app F).f i ∧
            c.hom ≫ π.app (pullback f g) ≫ pullback.snd f g ≫ kernel.ι d =
              (Q.obj F).d i (i + 1) := by
  classical
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
  let X := CyclePullback.term T π P.ι N
  let d := CyclePullback.differential T π P.ι N
  let e := CyclePullback.augmentation T π P.ι N
  have laws := CyclePullback.tower_laws T π P.ι N
  let Q : P.FullSubcategory ⥤ CochainComplex A ℤ :=
    { obj := fun F ↦ CochainComplex.of (fun i ↦ (X i).obj F) (fun i ↦ (d i).app F)
        (fun i ↦ by
          exact congrArg (fun α ↦ α.app F) (laws i).1)
      map := fun φ ↦ CochainComplex.ofHom (fun i ↦ (X i).map φ) (fun i ↦ by
        simpa only [CochainComplex.of_d] using (d i).naturality φ)
      map_id := fun F ↦ by ext i; exact (X i).map_id F
      map_comp := fun φ ψ ↦ by ext i; exact (X i).map_comp φ ψ }
  let ε : Q ⟶ P.ι :=
    { app := fun F ↦ CochainComplex.ofHom (fun i ↦ (e i).app F) (fun i ↦ by
        dsimp only [Q, CochainComplex.ofHom]
        simpa only [CochainComplex.of_d, NatTrans.comp_app, CyclePullback.targetD,
          Functor.whiskerLeft_app, HomologicalComplex.dNatTrans_app] using
          congrArg (fun α ↦ α.app F) (laws i).2)
      naturality := fun F G φ ↦ by
        ext i
        exact (e i).naturality φ }
  refine ⟨Q, ε, ?_⟩
  intro F
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact CyclePullback.term_mem S hzero T π hT P.ι N i F
  · intro i hi
    exact CyclePullback.term_isZero T π P.ι N i hi F
  · intro i hi
    dsimp only [Q, ε, CochainComplex.ofHom]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact CyclePullback.tower_comparison T π P.ι N F i hi

end CochainComplex
