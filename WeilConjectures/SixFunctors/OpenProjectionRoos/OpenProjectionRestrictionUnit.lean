/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Roos comparisons through the unit of an exact adjunction

For an exact adjunction `J ⊣ G` and Roos comparisons for `J` and `G`, the composite
comparison `G (J (Roos T)) ≅ Roos (G (J T))` is the Roos map of the termwise unit.
We deduce the corresponding formula for the inverse of the derived unit.

## References

* Stacks Project, Tags 0941 and 015F
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b c d wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.OpenProjectionRoos

section Unit
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B]

/-- The isomorphism of functors on cochain complexes induced by `𝟭 A ≅ J ⋙ G`. -/
def complexUnitIso {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive] (μ : 𝟭 A ≅ J ⋙ G) :
    𝟭 (CochainComplex A ℤ) ≅
      J.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexIdIso A (.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex μ (.up ℤ)

/-- The isomorphism of strict towers induced by `𝟭 A ≅ J ⋙ G`. -/
def towerUnitIso {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive] (μ : 𝟭 A ≅ J ⋙ G)
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    T ≅ (onTowers G).obj ((onTowers J).obj T) :=
  Functor.isoWhiskerLeft T (complexUnitIso μ)

@[simp]
theorem towerUnitIso_hom_app_f {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    (μ : 𝟭 A ≅ J ⋙ G) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕᵒᵖ) (i : ℤ) :
    ((towerUnitIso μ T).hom.app n).f i = μ.hom.app ((T.obj n).X i) := by
  simp [towerUnitIso, complexUnitIso]

@[simp]
theorem towerUnitIso_inv_app_f {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    (μ : 𝟭 A ≅ J ⋙ G) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕᵒᵖ) (i : ℤ) :
    ((towerUnitIso μ T).inv.app n).f i = μ.inv.app ((T.obj n).X i) := by
  simp [towerUnitIso, complexUnitIso]

end Unit

section Chain
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

/-- A morphism into a degree of a countable product of complexes is determined by its
projections. -/
theorem product_degree_ext (K : ℕ → CochainComplex A ℤ) (p : ℤ) {D : A}
    (f g : D ⟶ (∏ᶜ K).X p)
    (h : ∀ n, f ≫ (Pi.π K n).f p = g ≫ (Pi.π K n).f p) : f = g := by
  apply (cancel_mono (piComparison (HomologicalComplex.eval A (.up ℤ) p) K)).mp
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map] using h n

/-- The Roos map composed with the product coordinate. -/
theorem integralOperationsRoosMap_fst {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : V ⟶ W) :
    integralOperationsRoosMap α ≫ CochainComplex.mappingCocone.fst (boundary W) =
      CochainComplex.mappingCocone.fst (boundary V) ≫
        Limits.Pi.map (fun n : ℕ ↦ α.app (op n)) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact integralOperationsRoosFunctor_map_fst α i

/-- The composite of two Roos comparisons through an adjunction unit is the Roos map
of the termwise unit. -/
theorem roosComparison_unit {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    (adj : J ⊣ G) (μ : 𝟭 A ≅ J ⋙ G) (hμ : μ.hom = adj.unit)
    (rJ : RoosComparison J) (rG : RoosComparison G) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app (integralOperationsRoos T) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (rJ.iso.hom.app T) ≫
        rG.iso.hom.app ((onTowers J).obj T) =
      integralOperationsRoosMap (towerUnitIso μ T).hom := by
  apply CochainComplex.mappingCocone.hom_ext
  · refine Pi.hom_ext _ _ (fun n ↦ ?_)
    simp only [Category.assoc]
    erw [reassoc_of% integralOperationsRoosMap_fst, Limits.Pi.map_π,
      reassoc_of% (rG.first ((onTowers J).obj T)), rG.projections, ← Functor.map_comp,
      ← Functor.map_comp, reassoc_of% (rJ.first T), rJ.projections, ← Functor.map_comp]
    apply HomologicalComplex.hom_ext
    intro i
    simp [hμ, Adjunction.mapHomologicalComplex]
  · intro i
    apply product_degree_ext
    intro n
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [reassoc_of% (integralOperationsRoosFunctor_map_snd (towerUnitIso μ T).hom i)]
    erw [reassoc_of% (rG.shifted ((onTowers J).obj T) i (i - 1) (by omega))]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, rG.projections,
      Limits.Pi.map_π]
    simp only [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp]
    erw [reassoc_of% (rJ.shifted T i (i - 1) (by omega))]
    rw [← HomologicalComplex.comp_f, rJ.projections]
    simp [hμ, Adjunction.mapHomologicalComplex]

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

omit [HasCountableProducts A] [HasCountableProducts B] in
/-- The unit of the localized exact adjunction on a localized complex. -/
theorem mapExactDerivedCategory_unit_app_Q {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : J ⊣ G)
    (K : CochainComplex A ℤ) :
    adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app _ ≫
        G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K) := by
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
  rfl

/-- The inverse of the derived unit on a Roos complex, through Roos comparisons for an exact
adjunction and a strict tower isomorphism `z`. -/
theorem roosComparison_derived_unit_inv {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : J ⊣ G)
    (μ : 𝟭 A ≅ J ⋙ G) (hμ : μ.hom = adj.unit)
    (unit : 𝟭 (DerivedCategory.{wA} A) ≅ J.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (hunit : unit.hom = adj.mapExactDerivedCategory.unit)
    (rJ : RoosComparison J) (rG : RoosComparison G) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (S : ℕᵒᵖ ⥤ CochainComplex B ℤ) (z : S ≅ (onTowers J).obj T) :
    unit.inv.app (DerivedCategory.Q.obj (integralOperationsRoos T)) =
      G.mapDerivedCategory.map (rJ.derived J T).hom ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map (integralOperationsRoosMap z.inv)) ≫
        (rG.derived G S).hom ≫
        DerivedCategory.Q.map
          (integralOperationsRoosMap ((onTowers G).map z.hom ≫ (towerUnitIso μ T).inv)) := by
  refine Iso.inv_ext (f := unit.app _) ?_
  rw [Iso.app_hom, hunit, mapExactDerivedCategory_unit_app_Q]
  simp only [RoosComparison.derived, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc G.mapDerivedCategory (J.mapDerivedCategoryFactors.inv.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc G.mapDerivedCategory, ← Functor.map_comp,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc, Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  erw [← DerivedCategory.Q.map_id]
  congr 1
  have hnat := rG.iso.hom.naturality z.inv
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [reassoc_of% hnat, ← integralOperationsRoosMap_comp,
    ← Category.assoc ((onTowers G).map z.inv),
    ← CategoryTheory.Functor.map_comp, z.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% (roosComparison_unit adj μ hμ rJ rG T),
    ← integralOperationsRoosMap_comp, Iso.hom_inv_id, integralOperationsRoosMap_id]

omit [HasCountableProducts B] [HasDerivedCategory.{wB} B] in
/-- The localized Roos maps of an isomorphism of towers are mutually inverse. -/
theorem derivedQ_map_integralOperationsRoosMap_hom_inv {V W : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (f : V ≅ W) :
    DerivedCategory.Q.map (integralOperationsRoosMap f.hom) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap f.inv) = 𝟙 _ := by
  rw [← DerivedCategory.Q.map_comp, ← integralOperationsRoosMap_comp, f.hom_inv_id,
    integralOperationsRoosMap_id, CategoryTheory.Functor.map_id]

end Chain

/-- Transport of an equation `gK ≫ sh a ≫ sh b ≫ e = c ≫ d ≫ u` along the inverse of a unit
`𝟭 ≅ sh ⋙ st`, when that inverse is computed through `e` and an inverse `v` of `u`. -/
theorem unit_inv_comp_eq {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    (sh : C ⥤ D) (st : D ⥤ C) (η : 𝟭 C ≅ sh ⋙ st)
    {P P' S R' : D} {I I' R W : C} (gK : P ⟶ sh.obj I) (a : I ⟶ I') (b : I' ⟶ R)
    (e : sh.obj R ⟶ R') (c' : P ⟶ P') (d' : P' ⟶ S) (u : S ⟶ R') (v : R' ⟶ S)
    (r : st.obj S ⟶ W) (w : W ⟶ R) (t : st.obj P ⟶ I)
    (ht : t = st.map gK ≫ η.inv.app I)
    (h₁ : gK ≫ sh.map a ≫ sh.map b ≫ e = c' ≫ d' ≫ u)
    (h₂ : η.inv.app R = st.map e ≫ st.map v ≫ r ≫ w) (h₃ : u ≫ v = 𝟙 S) :
    t ≫ a ≫ b = st.map (c' ≫ d') ≫ r ≫ w := by
  have hn := η.inv.naturality (a ≫ b)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have key : gK ≫ sh.map (a ≫ b) ≫ e ≫ v = c' ≫ d' := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₁, h₃, Category.comp_id]
  rw [ht, Category.assoc, ← hn, h₂, ← key]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end WeilConjectures.OpenProjectionRoos
