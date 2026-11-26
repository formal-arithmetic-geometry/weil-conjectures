/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import WeilConjectures.SixFunctors.ProEtale.InternalQuotientScalarAnnihilation

/-! # Strict finite augmentation maps, before any acyclicity assertion

## References

* [Stacks, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [local irreducible] IntegralConstantModel.pointComparison upperStarFromPoint

/-- The finite quotient augmentation exists on arbitrary complexes, with no K-flatness
or quasi-isomorphism assertion. Its components off Koszul degree zero vanish. -/
theorem koszul_finite_augmentation
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      (residue l E X).hom.app (op U) (a.val (op U)) = 0)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    ∃ v : ∀ n : ℕ,
        ((ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
          (complex l E X P)).obj (op n) ⟶ (quotients l E X P).obj (op n),
      (∀ n, ringedKoszulTensorUnitComponent (ring l E X) 1 (fun _ ↦ a)
          (complex l E X P) (op n) ≫ v n = (quotientUnits l E X P).app (op n)) ∧
      (∀ (n : ℕ) (p j : ℤ), j ≠ 0 →
        HomologicalComplex.ιMapBifunctor (complex l E X P)
            ((ringedKoszulDualTower (ring l E X) 1 (fun _ ↦ a)).obj (op n))
            (curriedTensor _) (.up ℤ) p j (p + j) rfl ≫ (v n).f (p + j) = 0) ∧
      (∀ n, ((ringedKoszulTensorTower (ring l E X) 1 (fun _ ↦ a)).obj
          (complex l E X P)).map (homOfLE (Nat.le_add_right n 1)).op ≫ v n =
        v (n + 1) ≫ (quotients l E X P).map
          (homOfLE (Nat.le_add_right n 1)).op) := by
  let N := complex l E X P
  let s := fun n ↦ (ringedSingletonKoszulPower (ring l E X) a N n).asHom
  let U := ringedKoszulRightUnitIso (ring l E X) N
  obtain ⟨e, he, hz, ht⟩ := ringedSingletonKoszulCone (ring l E X) a N
  have hs (n : ℕ) : s n ≫
      (U.hom ≫ (quotientUnits l E X P).app (op n)) = 0 :=
    quotient_scalar_annihilation l E X a ha P n
  let w (n : ℕ) : CochainComplex.mappingCone (s n) ⟶
      (quotients l E X P).obj (op n) :=
    CochainComplex.mappingCone.desc _ 0 (U.hom ≫ (quotientUnits l E X P).app (op n))
      (by simp [hs n])
  have hw (n : ℕ) (q : ℤ) : (w n).f q =
      (CochainComplex.mappingCone.snd (s n)).v q q (add_zero _) ≫
        (U.hom ≫ (quotientUnits l E X P).app (op n)).f q := by
    dsimp only [w]
    rw [CochainComplex.mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
    simp
  refine ⟨fun n ↦ (e n).hom ≫ w n, ?_, ?_, ?_⟩
  · intro n
    rw [← Category.assoc, he n]
    rw [Category.assoc, CochainComplex.mappingCone.inr_desc,
      Iso.inv_hom_id_assoc]
  · intro n p j hj
    have h := congrArg (fun f ↦ f ≫ U.hom.f (p + j) ≫
      ((quotientUnits l E X P).app (op n)).f (p + j)) (hz n p j hj)
    simpa only [HomologicalComplex.comp_f, hw, Category.assoc, zero_comp] using h
  · intro n
    apply HomologicalComplex.hom_ext
    intro q
    have h : (quotientUnits l E X P).app (op n) =
        (quotientUnits l E X P).app (op (n + 1)) ≫
          (quotients l E X P).map (homOfLE (Nat.le_add_right n 1)).op := by
      have hnat := (quotientUnits l E X P).naturality
        (homOfLE (Nat.le_add_right n 1)).op
      change (𝟙 (complex l E X P)) ≫ (quotientUnits l E X P).app (op n) = _ at hnat
      exact (Category.id_comp _).symm.trans hnat
    have hu : ((quotientUnits l E X P).app (op n)).f q =
        ((quotientUnits l E X P).app (op (n + 1))).f q ≫
          ((quotients l E X P).map (homOfLE (Nat.le_add_right n 1)).op).f q :=
      congrArg (fun f ↦ f.f q) h
    have h' := congrArg (fun f ↦ f ≫ U.hom.f q ≫
      ((quotientUnits l E X P).app (op n)).f q) (ht n q)
    simp only [HomologicalComplex.comp_f, hw, HomologicalComplex.comp_f, Category.assoc]
    calc
      _ = (e (n + 1)).hom.f q ≫
          (CochainComplex.mappingCone.snd (s (n + 1))).v q q (add_zero _) ≫
            U.hom.f q ≫ ((quotientUnits l E X P).app (op n)).f q := by
        simpa only [Category.assoc] using h'
      _ = _ := by rw [hu]

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
