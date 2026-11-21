/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ConeHorizontalProjection

/-!
# Naturality of the extended column projection

## References

* Stacks Project, Tag 012X (first horizontal filtration)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- Naturality before extension by zero. -/
@[reassoc]
private theorem totalProjection_naturality
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p m : ℕ) :
    (total.map f (ComplexShape.up ℕ)).f m ≫ horizontalTotalProjection B p m =
      horizontalTotalProjection A p m ≫ (f.f p).f (m - p) := by
  apply total.hom_ext
  intro h j hj
  simp only [horizontalTotalProjection, ιTotal_map_assoc,
    ι_totalDesc, ι_totalDesc_assoc]
  by_cases hh : h = p
  · subst h
    have hj' : j = m - p := by change p + j = m at hj; omega
    subst j
    simp [XXIsoOfEq]
  · simp [hh]

/-- Naturality after extension by zero, in the original target degree. -/
private theorem extendedProjection_naturality
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (m : ℤ) :
    (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat).f m ≫ horizontalExtendedProjection B p m =
    horizontalExtendedProjection A p m ≫
      (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat).f
        (m - (p : ℤ)) := by
  by_cases hm : (p : ℤ) ≤ m
  · have hn : 0 ≤ m := by omega
    have hp : ((m.toNat - p : ℕ) : ℤ) = m - (p : ℤ) := by omega
    rw [HomologicalComplex.extendMap_f _ _ (Int.toNat_of_nonneg hn),
      HomologicalComplex.extendMap_f _ _ hp]
    simp only [horizontalExtendedProjection, dite_eq_left hm, Category.assoc,
      Iso.inv_hom_id_assoc]
    erw [totalProjection_naturality_assoc]
  · simp [horizontalExtendedProjection, hm]

/-- Projection onto a column commutes with a bicomplex morphism, after extension by zero. -/
@[reassoc]
theorem horizontalProjection_naturality
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (m i : ℤ) (hi : m - (p : ℤ) = i) :
    (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat).f m ≫
    (horizontalExtendedProjection B p m ≫
      (((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show m - (p : ℤ) = i by omega)).hom) =
    (horizontalExtendedProjection A p m ≫
      (((A.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show m - (p : ℤ) = i by omega)).hom) ≫
      (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat).f i := by
  simp only [Category.assoc, ← HomologicalComplex.XIsoOfEq_hom_naturality]
  rw [← Category.assoc, extendedProjection_naturality]
  simp only [Category.assoc]


end HomologicalComplex₂
