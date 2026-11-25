/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport of a distributivity diagram

## References

* Stacks Project, Tag 03D2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- Transport of a distributivity diagram along a product-preserving functor, using only
binary products (Stacks, Tag 03D2). -/
theorem productComparison_distributivity
    {C D : Type*} [Category C] [Category D]
    [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {R X : C} {R' X' : D} (p : R' ≅ F.obj R) (q : X' ≅ F.obj X)
    (addV : X ⨯ X ⟶ X) (addU : X' ⨯ X' ⟶ X') (muV : R ⨯ X ⟶ X)
    (hadd : F.map addV = prodComparison F X X ≫
      prod.map q.inv q.inv ≫ addU ≫ q.hom)
    (hdist : prod.map (𝟙 R) addV ≫ muV =
      prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ muV)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ muV) ≫ addV) :
    let mu := prod.map p.hom q.hom ≫ inv (prodComparison F R X) ≫ F.map muV ≫ q.inv
    prod.map (𝟙 R') addU ≫ mu =
      prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu) ≫ addU := by
  dsimp only
  let q2 := prodComparison F X X ≫ prod.map q.inv q.inv
  let qRX := prodComparison F R X ≫ prod.map p.inv q.inv
  let q3 := prodComparison F R (X ⨯ X) ≫ prod.map p.inv q2
  let mu := prod.map p.hom q.hom ≫ inv (prodComparison F R X) ≫ F.map muV ≫ q.inv
  have hmu : qRX ≫ mu = F.map muV ≫ q.inv := by
    simp [qRX, mu, Category.assoc]
  have ha : q2 ≫ addU = F.map addV ≫ q.inv := by
    rw [hadd]
    simp [q2, Category.assoc]
  have hq2f : q2 ≫ prod.fst = F.map prod.fst ≫ q.inv := by
    simp [q2, Category.assoc]
  have hq2s : q2 ≫ prod.snd = F.map prod.snd ≫ q.inv := by
    simp [q2, Category.assoc]
  have hqRf : qRX ≫ prod.fst = F.map prod.fst ≫ p.inv := by
    simp [qRX, Category.assoc]
  have hqRs : qRX ≫ prod.snd = F.map prod.snd ≫ q.inv := by
    simp [qRX, Category.assoc]
  have hq3f : q3 ≫ prod.fst = F.map prod.fst ≫ p.inv := by
    simp [q3, Category.assoc]
  have hq3s : q3 ≫ prod.snd = F.map prod.snd ≫ q2 := by
    simp [q3, Category.assoc]
  have haddmap : q3 ≫ prod.map (𝟙 R') addU = F.map (prod.map (𝟙 R) addV) ≫ qRX := by
    apply prod.hom_ext
    · rw [Category.assoc]
      simp only [prod.map_fst, Category.comp_id, hq3f,
        Category.assoc, hqRf]
      rw [← Category.assoc, ← F.map_comp]
      simp
    · rw [Category.assoc, prod.map_snd, ← Category.assoc, hq3s, Category.assoc, ha,
        Category.assoc, hqRs]
      simp only [← Category.assoc, ← F.map_comp, prod.map_snd]
  have hfirst : q3 ≫ prod.lift prod.fst (prod.snd ≫ prod.fst) =
      F.map (prod.lift prod.fst (prod.snd ≫ prod.fst)) ≫ qRX := by
    apply prod.hom_ext
    · rw [Category.assoc]
      simp only [prod.lift_fst, hq3f,
        Category.assoc, hqRf]
      rw [← Category.assoc, ← F.map_comp]
      simp
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, hq3s, Category.assoc, hq2f,
        Category.assoc, hqRs]
      simp only [← Category.assoc, ← F.map_comp, prod.lift_snd]
  have hsecond : q3 ≫ prod.lift prod.fst (prod.snd ≫ prod.snd) =
      F.map (prod.lift prod.fst (prod.snd ≫ prod.snd)) ≫ qRX := by
    apply prod.hom_ext
    · rw [Category.assoc]
      simp only [prod.lift_fst, hq3f,
        Category.assoc, hqRf]
      rw [← Category.assoc, ← F.map_comp]
      simp
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, hq3s, Category.assoc, hq2s,
        Category.assoc, hqRs]
      simp only [← Category.assoc, ← F.map_comp, prod.lift_snd]
  have hpair : q3 ≫ prod.lift
      (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu) =
      F.map (prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ muV)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ muV)) ≫ q2 := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, ← Category.assoc, hfirst,
        Category.assoc, hmu, Category.assoc, hq2f]
      simp only [← Category.assoc, ← F.map_comp, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, hsecond,
        Category.assoc, hmu, Category.assoc, hq2s]
      simp only [← Category.assoc, ← F.map_comp, prod.lift_snd]
  let : IsIso q2 := by dsimp [q2]; infer_instance
  let : IsIso q3 := by dsimp [q3]; infer_instance
  apply (cancel_epi q3).1
  change q3 ≫ (prod.map (𝟙 R') addU ≫ mu) =
    q3 ≫ (prod.lift
      (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ mu)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ mu) ≫ addU)
  calc
    _ = F.map (prod.map (𝟙 R) addV ≫ muV) ≫ q.inv := by
      rw [← Category.assoc, haddmap, Category.assoc, hmu,
        ← Category.assoc, ← F.map_comp]
    _ = F.map (prod.lift
        (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ muV)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ muV) ≫ addV) ≫ q.inv := by rw [hdist]
    _ = _ := by
      rw [← Category.assoc q3, hpair, Category.assoc, ha,
        ← Category.assoc, ← F.map_comp]



end CategoryTheory.Limits
