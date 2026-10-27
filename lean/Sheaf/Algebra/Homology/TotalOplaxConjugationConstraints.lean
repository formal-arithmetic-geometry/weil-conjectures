module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Homology.TotalOplaxConjugationSummands

/-! # Constraints of the conjugated total tensor comparison

Source: Stacks Project, Tag 0FPQ, lemma-symmetric-monoidal-cat-complexes;
agent extraction of the functor-square constraint calculation
(blueprint: lem-pd-total-oplax-conjugation-constraints).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

namespace CategoryTheory.TotalOplaxConjugation

section TensorExistence

variable {C : Type u₀} [Category.{v₀} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Integer-graded tensor products exist by the available coproducts.

This proved instance shortcut avoids repeating the coproduct-existence search.
-/
theorem tensorExists (X Y : GradedObject ℤ C) : X.HasTensor Y := inferInstance

/-- The left iterated integer-graded tensor has the required coproduct comparison.

This proved instance shortcut avoids repeating the coproduct-existence search.
-/
theorem tensorGoodLeft (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance

/-- The right iterated integer-graded tensor has the required coproduct comparison.

This proved instance shortcut avoids repeating the coproduct-existence search.
-/
theorem tensorGoodRight (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance

/-- Four integer-graded tensor factors admit the coproduct extensionality instance.

This proved instance shortcut avoids repeating the coproduct-existence search.
-/
theorem tensorFour (W X Y Z : GradedObject ℤ C) :
    GradedObject.HasTensor₄ObjExt W X Y Z := inferInstance

end TensorExistence

section General

attribute [local instance 2000] tensorExists tensorGoodLeft tensorGoodRight tensorFour


variable {C : Type u₀} [Category.{v₀} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {D : Type u₁} [Category.{v₁} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [HasColimitsOfSize.{0, 0} D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (G : C ⥤ D) [G.Additive] [G.Monoidal]
  [hG : ∀ (I : Type) [Countable I], PreservesColimitsOfShape (Discrete I) G]

@[reassoc]
private theorem total_inverse_restriction (P Q : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    G.map (ιTensorObj P Q p q n h) ≫ (G.mapCochainComplexμIso P Q).inv.f n =
      Functor.OplaxMonoidal.δ G (P.X p) (Q.X q) ≫
        ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj P)
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  rw [Functor.mapCochainComplexμIso_inv]
  exact map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ) P Q p q n h

private theorem unit_inverse_zero :
    G.mapCochainComplexεIso.inv.f 0 =
      G.map (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
        Functor.OplaxMonoidal.η G ≫ (singleObjXSelf (.up ℤ) 0 (𝟙_ D)).inv := by
  apply (cancel_epi (G.mapCochainComplexεIso.hom.f 0)).1
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    Functor.mapCochainComplexεIso_hom_f_zero]
  simp only [Category.assoc, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id,
    Category.id_comp, Functor.Monoidal.ε_η_assoc, Iso.hom_inv_id]

omit [G.Monoidal] in
private theorem double_detection (P Q : CochainComplex C ℤ) (n : ℤ) (Z : D)
    (f g : G.obj ((P ⊗ Q).X n) ⟶ Z)
    (hfg : ∀ (p q : ℤ) (h : p + q = n),
      G.map (ιTensorObj P Q p q n h) ≫ f = G.map (ιTensorObj P Q p q n h) ≫ g) :
    f = g := by
  exact mapBifunctor.hom_ext_of_map G hfg

omit [G.Monoidal] in
private theorem left_detection (P Q H : CochainComplex C ℤ) (n : ℤ) (Z : D)
    (f g : G.obj (((P ⊗ Q) ⊗ H).X n) ⟶ Z)
    (hfg : ∀ (p q r : ℤ) (h : p + q + r = n),
      G.map (mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C)
        P Q H (.up ℤ) (.up ℤ) p q r n h) ≫ f =
      G.map (mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C)
        P Q H (.up ℤ) (.up ℤ) p q r n h) ≫ g) : f = g := by
  apply mapBifunctor.hom_ext_of_map G
  intro s r hsr
  apply mapBifunctor.hom_ext_of_map (tensorRight (H.X r) ⋙ G)
  intro p q hpq
  change G.map (ιTensorObj P Q p q s hpq ▷ H.X r) ≫ _ =
    G.map (ιTensorObj P Q p q s hpq ▷ H.X r) ≫ _
  have hh := hfg p q r (by dsimp at hpq hsr; omega)
  erw [CochainComplex.Monoidal.ι₁₂_eq P Q H p q r s n hpq hsr] at hh
  simpa only [G.map_comp, Category.assoc] using hh

omit [G.Monoidal] in
private theorem right_detection (P Q H : CochainComplex C ℤ) (n : ℤ) (Z : D)
    (f g : G.obj ((P ⊗ (Q ⊗ H)).X n) ⟶ Z)
    (hfg : ∀ (p q r : ℤ) (h : p + q + r = n),
      G.map (mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C)
        P Q H (.up ℤ) (.up ℤ) (.up ℤ) p q r n h) ≫ f =
      G.map (mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C)
        P Q H (.up ℤ) (.up ℤ) (.up ℤ) p q r n h) ≫ g) : f = g := by
  apply mapBifunctor.hom_ext_of_map G
  intro p s hps
  apply mapBifunctor.hom_ext_of_map (tensorLeft (P.X p) ⋙ G)
  intro q r hqr
  change G.map (P.X p ◁ ιTensorObj Q H q r s hqr) ≫ _ =
    G.map (P.X p ◁ ιTensorObj Q H q r s hqr) ≫ _
  have hh := hfg p q r (by dsimp at hqr hps; omega)
  erw [CochainComplex.Monoidal.ι₂₃_eq P Q H p q r s n hqr hps] at hh
  simpa only [G.map_comp, Category.assoc] using hh

private theorem left_unit_restriction (P : CochainComplex C ℤ) (n : ℤ) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ▷ P.X n ≫
        ιTensorObj (𝟙_ (CochainComplex C ℤ)) P 0 n n (zero_add n) ≫
          (λ_ P).hom.f n = (λ_ (P.X n)).hom := by
  apply (cancel_epi (λ_ (P.X n)).inv).1
  erw [← reassoc_of% (leftUnitor'_inv P n)]
  change (λ_ P).inv.f n ≫ (λ_ P).hom.f n = _
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  exact (Iso.inv_hom_id _).symm

private theorem right_unit_restriction (P : CochainComplex C ℤ) (n : ℤ) :
    P.X n ◁ (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫
        ιTensorObj P (𝟙_ (CochainComplex C ℤ)) n 0 n (add_zero n) ≫
          (ρ_ P).hom.f n = (ρ_ (P.X n)).hom := by
  apply (cancel_epi (ρ_ (P.X n)).inv).1
  erw [← reassoc_of% (rightUnitor'_inv P n)]
  change (ρ_ P).inv.f n ≫ (ρ_ P).hom.f n = _
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  exact (Iso.inv_hom_id _).symm

end General

section Ordinary

variable {A₀ : Type u₀} [Category.{v₀} A₀] [MonoidalCategory A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] [MonoidalCategory A₁]
  {B₀ : Type u₂} [Category.{v₂} B₀] [MonoidalCategory B₀]
  {B₁ : Type u₃} [Category.{v₃} B₁] [MonoidalCategory B₁]
  (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (Fi : A₀ ⥤ A₁) (Fs : B₀ ⥤ B₁)
  [E₀.Monoidal] [E₁.Monoidal] [Fi.Monoidal]
  (a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs)

/-- The specified ordinary conjugation, read from right to left in the source.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def tensorComparison (M N : A₀) :
    Fs.obj (E₀.obj M ⊗ E₀.obj N) ≅ Fs.obj (E₀.obj M) ⊗ Fs.obj (E₀.obj N) :=
  Fs.mapIso (Functor.Monoidal.μIso E₀ M N) ≪≫ (a.app (M ⊗ N)).symm ≪≫
    E₁.mapIso (Functor.Monoidal.μIso Fi M N).symm ≪≫
    (Functor.Monoidal.μIso E₁ (Fi.obj M) (Fi.obj N)).symm ≪≫
    tensorIso (a.app M) (a.app N)

/-- The specified ordinary oplax unit conjugation.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def unitComparison : Fs.obj (𝟙_ B₀) ≅ 𝟙_ B₁ :=
  Fs.mapIso (Functor.Monoidal.εIso E₀) ≪≫ (a.app (𝟙_ A₀)).symm ≪≫
    E₁.mapIso (Functor.Monoidal.εIso Fi).symm ≪≫ (Functor.Monoidal.εIso E₁).symm

/-- The ordinary comparison after reinserting the source equivalence's tensorator.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def hatTensor (M N : A₀) :
    Fs.obj (E₀.obj (M ⊗ N)) ≅ Fs.obj (E₀.obj M) ⊗ Fs.obj (E₀.obj N) :=
  Fs.mapIso (Functor.Monoidal.μIso E₀ M N).symm ≪≫ tensorComparison E₀ E₁ Fi Fs a M N

/-- The ordinary unit after reinserting the source equivalence's unit comparison.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def hatUnit : Fs.obj (E₀.obj (𝟙_ A₀)) ≅ 𝟙_ B₁ :=
  Fs.mapIso (Functor.Monoidal.εIso E₀).symm ≪≫ unitComparison E₀ E₁ Fi Fs a


private theorem hatTensor_naturality (M N M' N' : A₀) (u : M ⟶ M') (v : N ⟶ N') :
    (E₀ ⋙ Fs).map (u ⊗ₘ v) ≫ (hatTensor E₀ E₁ Fi Fs a M' N').hom =
      (hatTensor E₀ E₁ Fi Fs a M N).hom ≫
        ((E₀ ⋙ Fs).map u ⊗ₘ (E₀ ⋙ Fs).map v) := by
  simp only [hatTensor, tensorComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μIso_inv, tensorIso_hom, Category.assoc,
    ← Functor.map_comp_assoc, Functor.Monoidal.δ_μ, Functor.map_id, Category.id_comp]
  dsimp only [Functor.comp_map]
  rw [reassoc_of% (a.inv.naturality (u ⊗ₘ v))]
  rw [← E₁.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural,
    E₁.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_assoc]
  simp only [tensorHom_comp_tensorHom]
  have hu := a.hom.naturality u
  have hv := a.hom.naturality v
  dsimp only [Functor.comp_map] at hu hv
  rw [hu, hv]

end Ordinary

section Complexes

attribute [local instance 2000] tensorExists tensorGoodLeft tensorGoodRight tensorFour

variable {A₀ : Type u₀} [Category.{v₀} A₀] [Abelian A₀] [MonoidalCategory A₀]
  [MonoidalPreadditive A₀] [HasColimitsOfSize.{0, 0} A₀]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₀).obj X)]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₀).flip.obj X)]
  {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [MonoidalCategory A₁]
  [MonoidalPreadditive A₁] [HasColimitsOfSize.{0, 0} A₁]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₁).obj X)]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₁).flip.obj X)]
  {B₀ : Type u₂} [Category.{v₂} B₀] [Abelian B₀] [MonoidalCategory B₀]
  [MonoidalPreadditive B₀] [HasColimitsOfSize.{0, 0} B₀]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₀).obj X)]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₀).flip.obj X)]
  {B₁ : Type u₃} [Category.{v₃} B₁] [Abelian B₁] [MonoidalCategory B₁]
  [MonoidalPreadditive B₁] [HasColimitsOfSize.{0, 0} B₁]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₁).obj X)]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₁).flip.obj X)]
  (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (Fi : A₀ ⥤ A₁) (Fs : B₀ ⥤ B₁)
  [E₀.IsEquivalence] [E₁.IsEquivalence]
  [E₀.Additive] [E₁.Additive] [Fi.Additive] [Fs.Additive]
  [E₀.Monoidal] [E₁.Monoidal] [Fi.Monoidal] [hFsMonoidal : Fs.Monoidal]
  [hFi : ∀ (I : Type) [Countable I], PreservesColimitsOfShape (Discrete I) Fi]
  [hFs : ∀ (I : Type) [Countable I], PreservesColimitsOfShape (Discrete I) Fs]
  (a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs)

/-- Termwise extension of the given arbitrary natural isomorphism; no monoidality is used.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def complexSquare :
    Fi.mapHomologicalComplex (.up ℤ) ⋙ E₁.mapHomologicalComplex (.up ℤ) ≅
      E₀.mapHomologicalComplex (.up ℤ) ⋙ Fs.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex a (.up ℤ)

/-- The chain isomorphism A, using the canonical preserved-coproduct total comparisons.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def totalTensor (P Q : CochainComplex A₀ ℤ) :=
  tensorComparison (E₀.mapHomologicalComplex (.up ℤ))
    (E₁.mapHomologicalComplex (.up ℤ)) (Fi.mapHomologicalComplex (.up ℤ))
    (Fs.mapHomologicalComplex (.up ℤ)) (complexSquare E₀ E₁ Fi Fs a) P Q

/-- The chain isomorphism J with its canonical degree-zero unit comparisons.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def totalUnit :=
  unitComparison (E₀.mapHomologicalComplex (.up ℤ))
    (E₁.mapHomologicalComplex (.up ℤ)) (Fi.mapHomologicalComplex (.up ℤ))
    (Fs.mapHomologicalComplex (.up ℤ)) (complexSquare E₀ E₁ Fi Fs a)

/-- The total comparison A-hat, including the source equivalence comparison.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def totalHatTensor (P Q : CochainComplex A₀ ℤ) :=
  hatTensor (E₀.mapHomologicalComplex (.up ℤ))
    (E₁.mapHomologicalComplex (.up ℤ)) (Fi.mapHomologicalComplex (.up ℤ))
    (Fs.mapHomologicalComplex (.up ℤ)) (complexSquare E₀ E₁ Fi Fs a) P Q

/-- The total unit J-hat, including the source equivalence comparison.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def totalHatUnit :=
  hatUnit (E₀.mapHomologicalComplex (.up ℤ))
    (E₁.mapHomologicalComplex (.up ℤ)) (Fi.mapHomologicalComplex (.up ℤ))
    (Fs.mapHomologicalComplex (.up ℤ)) (complexSquare E₀ E₁ Fi Fs a)

/-- The image complex under G = Fs E₀.
Source: Tag 0FPQ, functor-square extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable abbrev image (P : CochainComplex A₀ ℤ) :=
  (Fs.mapHomologicalComplex (.up ℤ)).obj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)

/-- Left-nested triple inclusion, without reassociation or permutation.
Source: Tag 0FPQ, total associator
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def leftInclusion (P Q H : CochainComplex A₀ ℤ)
    (p q r n : ℤ) (h : p + q + r = n) :
    (P.X p ⊗ Q.X q) ⊗ H.X r ⟶ ((P ⊗ Q) ⊗ H).X n :=
  mapBifunctor₁₂.ι (curriedTensor A₀) (curriedTensor A₀) P Q H (.up ℤ) (.up ℤ) p q r n h

/-- Right-nested triple inclusion with the same degree relation.
Source: Tag 0FPQ, total associator
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def rightInclusion (P Q H : CochainComplex A₀ ℤ)
    (p q r n : ℤ) (h : p + q + r = n) :
    P.X p ⊗ (Q.X q ⊗ H.X r) ⟶ (P ⊗ (Q ⊗ H)).X n :=
  mapBifunctor₂₃.ι (curriedTensor A₀) (curriedTensor A₀) P Q H
    (.up ℤ) (.up ℤ) (.up ℤ) p q r n h

/-- Inclusion of the nonzero left-unit summand, normalized by the degree-zero unit iso.
Source: Tag 0FPQ, degree-zero unit
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def leftUnitInclusion (P : CochainComplex A₀ ℤ) (n : ℤ) :
    𝟙_ A₀ ⊗ P.X n ⟶ ((𝟙_ (CochainComplex A₀ ℤ)) ⊗ P).X n :=
  (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv ▷ P.X n ≫
    ιTensorObj (𝟙_ (CochainComplex A₀ ℤ)) P 0 n n (zero_add n)

/-- Inclusion of the nonzero right-unit summand, normalized by the degree-zero unit iso.
Source: Tag 0FPQ, degree-zero unit
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
noncomputable def rightUnitInclusion (P : CochainComplex A₀ ℤ) (n : ℤ) :
    P.X n ⊗ 𝟙_ A₀ ⟶ (P ⊗ (𝟙_ (CochainComplex A₀ ℤ))).X n :=
  P.X n ◁ (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv ≫
    ιTensorObj P (𝟙_ (CochainComplex A₀ ℤ)) n 0 n (add_zero n)

include hFi hFs

/-- Inverse, signed-chain-map, two inverse equations, and all components of J.
Source: Tag 0FPQ, inverse and unit extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def InverseAndUnit : Prop :=
  (∀ (P Q : CochainComplex A₀ ℤ) (p q n : ℤ) (h : p + q = n),
    ιTensorObj (image E₀ Fs P) (image E₀ Fs Q) p q n h ≫
        (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv.f n =
      (tensorComparison E₀ E₁ Fi Fs a (P.X p) (Q.X q)).inv ≫
        Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
          ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)) ∧
  (∀ (P Q : CochainComplex A₀ ℤ),
    (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom ≫
        (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv = 𝟙 _ ∧
    (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv ≫
        (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom = 𝟙 _ ∧
    ∀ n m : ℤ,
      (image E₀ Fs P ⊗ image E₀ Fs Q).d n m ≫
          (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv.f m =
        (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv.f n ≫
          ((Fs.mapHomologicalComplex (.up ℤ)).obj
            (((E₀.mapHomologicalComplex (.up ℤ)).obj P) ⊗
              ((E₀.mapHomologicalComplex (.up ℤ)).obj Q))).d n m) ∧
  (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 =
    Fs.map (singleObjXSelf (.up ℤ) 0 (𝟙_ B₀)).hom ≫
      (unitComparison E₀ E₁ Fi Fs a).hom ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ B₁)).inv ∧
  (∀ (n : ℤ) (_hn : n ≠ 0),
    IsZero (Fs.obj ((𝟙_ (CochainComplex B₀ ℤ)).X n)) ∧
    IsZero ((𝟙_ (CochainComplex B₁ ℤ)).X n) ∧
    ∀ f : Fs.obj ((𝟙_ (CochainComplex B₀ ℤ)).X n) ⟶
        (𝟙_ (CochainComplex B₁ ℤ)).X n,
      f = (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f n)

/-- The two full associator paths restrict to the corresponding ordinary paths.
Source: Tag 0FPQ, triple-summand extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def AssociatorPaths : Prop :=
  ∀ (P Q H : CochainComplex A₀ ℤ) (p q r n : ℤ) (h : p + q + r = n),
    (E₀ ⋙ Fs).map (leftInclusion P Q H p q r n h) ≫
        ((Fs.mapHomologicalComplex (.up ℤ)).map
          ((E₀.mapHomologicalComplex (.up ℤ)).map (α_ P Q H).hom) ≫
        (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P (Q ⊗ H)).hom ≫
        (image E₀ Fs P ◁ (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a Q H).hom)).f n =
      (E₀ ⋙ Fs).map (α_ (P.X p) (Q.X q) (H.X r)).hom ≫
        (hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q ⊗ H.X r)).hom ≫
        ((E₀ ⋙ Fs).obj (P.X p) ◁
          (hatTensor E₀ E₁ Fi Fs a (Q.X q) (H.X r)).hom) ≫
        rightInclusion (image E₀ Fs P) (image E₀ Fs Q) (image E₀ Fs H) p q r n h ∧
    (E₀ ⋙ Fs).map (leftInclusion P Q H p q r n h) ≫
        ((totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a (P ⊗ Q) H).hom ≫
        ((totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom ▷ image E₀ Fs H) ≫
        (α_ (image E₀ Fs P) (image E₀ Fs Q) (image E₀ Fs H)).hom).f n =
      (hatTensor E₀ E₁ Fi Fs a (P.X p ⊗ Q.X q) (H.X r)).hom ≫
        ((hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ▷
          (E₀ ⋙ Fs).obj (H.X r)) ≫
        (α_ ((E₀ ⋙ Fs).obj (P.X p)) ((E₀ ⋙ Fs).obj (Q.X q))
          ((E₀ ⋙ Fs).obj (H.X r))).hom ≫
        rightInclusion (image E₀ Fs P) (image E₀ Fs Q) (image E₀ Fs H) p q r n h

/-- Every intermediate total comparison has its ordinary double-summand restriction.
This includes comparisons with an inner total as either argument; the following
naturality equation specifies restrictions along its inner injections as well.
Source: Tag 0FPQ, intermediate comparison extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def IntermediateComparisons : Prop :=
  (∀ (P Q : CochainComplex A₀ ℤ) (p q n : ℤ) (h : p + q = n),
    (E₀ ⋙ Fs).map (ιTensorObj P Q p q n h) ≫
        (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f n =
      (hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ≫
        ιTensorObj (image E₀ Fs P) (image E₀ Fs Q) p q n h) ∧
  (∀ (M N M' N' : A₀) (u : M ⟶ M') (v : N ⟶ N'),
    (E₀ ⋙ Fs).map (u ⊗ₘ v) ≫ (hatTensor E₀ E₁ Fi Fs a M' N').hom =
      (hatTensor E₀ E₁ Fi Fs a M N).hom ≫
        ((E₀ ⋙ Fs).map u ⊗ₘ (E₀ ⋙ Fs).map v))

/-- Each of the four unitor paths on its nonzero summand, with the specified unit e.
Source: Tag 0FPQ, unit-path extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def UnitPaths : Prop :=
  ∀ (P : CochainComplex A₀ ℤ) (n : ℤ),
    (E₀ ⋙ Fs).map (leftUnitInclusion P n) ≫
        ((Fs.mapHomologicalComplex (.up ℤ)).map
          ((E₀.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom)).f n =
      (E₀ ⋙ Fs).map (λ_ (P.X n)).hom ∧
    (E₀ ⋙ Fs).map (leftUnitInclusion P n) ≫
        ((totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a (𝟙_ (CochainComplex A₀ ℤ)) P).hom ≫
        ((totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom ▷ image E₀ Fs P) ≫
        (λ_ (image E₀ Fs P)).hom).f n =
      (hatTensor E₀ E₁ Fi Fs a (𝟙_ A₀) (P.X n)).hom ≫
        ((hatUnit E₀ E₁ Fi Fs a).hom ▷ (E₀ ⋙ Fs).obj (P.X n)) ≫
        (λ_ ((E₀ ⋙ Fs).obj (P.X n))).hom ∧
    (E₀ ⋙ Fs).map (rightUnitInclusion P n) ≫
        ((Fs.mapHomologicalComplex (.up ℤ)).map
          ((E₀.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom)).f n =
      (E₀ ⋙ Fs).map (ρ_ (P.X n)).hom ∧
    (E₀ ⋙ Fs).map (rightUnitInclusion P n) ≫
        ((totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P (𝟙_ (CochainComplex A₀ ℤ))).hom ≫
        (image E₀ Fs P ◁ (totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom) ≫
        (ρ_ (image E₀ Fs P)).hom).f n =
      (hatTensor E₀ E₁ Fi Fs a (P.X n) (𝟙_ A₀)).hom ≫
        ((E₀ ⋙ Fs).obj (P.X n) ◁ (hatUnit E₀ E₁ Fi Fs a).hom) ≫
        (ρ_ ((E₀ ⋙ Fs).obj (P.X n))).hom

/-- Off-zero unit summands vanish along every map, hence along each specified path.
Source: Tag 0FPQ, degree-zero unit
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def ZeroUnitSummands : Prop :=
  ∀ (P : CochainComplex A₀ ℤ) (p q n : ℤ) (h : p + q = n) (Z : B₁),
    (p ≠ 0 → ∀ f : (E₀ ⋙ Fs).obj ((𝟙_ (CochainComplex A₀ ℤ) ⊗ P).X n) ⟶ Z,
      (E₀ ⋙ Fs).map (ιTensorObj (𝟙_ (CochainComplex A₀ ℤ)) P p q n h) ≫ f = 0) ∧
    (q ≠ 0 → ∀ f : (E₀ ⋙ Fs).obj ((P ⊗ 𝟙_ (CochainComplex A₀ ℤ)).X n) ⟶ Z,
      (E₀ ⋙ Fs).map (ιTensorObj P (𝟙_ (CochainComplex A₀ ℤ)) p q n h) ≫ f = 0)

/-- Detection by all double and nested triple summands, also for infinite totals.
Source: Tag 0FPQ, coproduct universal property in the constraint extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def SummandDetection : Prop :=
  (∀ (P Q : CochainComplex B₀ ℤ) (n : ℤ) (Z : B₁)
      (f g : Fs.obj ((P ⊗ Q).X n) ⟶ Z),
    (∀ (p q : ℤ) (h : p + q = n),
      Fs.map (ιTensorObj P Q p q n h) ≫ f =
        Fs.map (ιTensorObj P Q p q n h) ≫ g) → f = g) ∧
  (∀ (P Q : CochainComplex A₀ ℤ) (n : ℤ) (Z : B₁)
      (f g : (E₀ ⋙ Fs).obj ((P ⊗ Q).X n) ⟶ Z),
    (∀ (p q : ℤ) (h : p + q = n),
      (E₀ ⋙ Fs).map (ιTensorObj P Q p q n h) ≫ f =
        (E₀ ⋙ Fs).map (ιTensorObj P Q p q n h) ≫ g) → f = g) ∧
  (∀ (P Q H : CochainComplex A₀ ℤ) (n : ℤ) (Z : B₁)
      (f g : (E₀ ⋙ Fs).obj (((P ⊗ Q) ⊗ H).X n) ⟶ Z),
    (∀ (p q r : ℤ) (h : p + q + r = n),
      (E₀ ⋙ Fs).map (leftInclusion P Q H p q r n h) ≫ f =
        (E₀ ⋙ Fs).map (leftInclusion P Q H p q r n h) ≫ g) → f = g) ∧
  (∀ (P Q H : CochainComplex A₀ ℤ) (n : ℤ) (Z : B₁)
      (f g : (E₀ ⋙ Fs).obj ((P ⊗ (Q ⊗ H)).X n) ⟶ Z),
    (∀ (p q r : ℤ) (h : p + q + r = n),
      (E₀ ⋙ Fs).map (rightInclusion P Q H p q r n h) ≫ f =
        (E₀ ⋙ Fs).map (rightInclusion P Q H p q r n h) ≫ g) → f = g)

/-- Unit intermediate comparison and recovery of A and J from the hatted maps.
These equalities specify the extra E₀ factors at each step of the transported paths.
Source: Tag 0FPQ, path transport extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def Recovery : Prop :=
  (∀ (P Q : CochainComplex A₀ ℤ),
    totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q =
      (Fs.mapHomologicalComplex (.up ℤ)).mapIso (E₀.mapCochainComplexμIso P Q) ≪≫
        totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q) ∧
  totalUnit E₀ E₁ Fi Fs (hFi := hFi) a =
    (Fs.mapHomologicalComplex (.up ℤ)).mapIso E₀.mapCochainComplexεIso ≪≫
      totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a ∧
  (totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 =
    (E₀ ⋙ Fs).map (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).hom ≫
      (hatUnit E₀ E₁ Fi Fs a).hom ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ B₁)).inv

/-- Ordinary constraint-path equality implies equality of the specified chain paths.
Source: Tag 0FPQ, detection on infinite sums in the constraint extraction
(blueprint: lem-pd-total-oplax-conjugation-constraints). -/
def LiftConstraintEquality : Prop :=
  (∀ (P Q H : CochainComplex A₀ ℤ),
    (∀ p q r : ℤ,
      (E₀ ⋙ Fs).map (α_ (P.X p) (Q.X q) (H.X r)).hom ≫
        (hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q ⊗ H.X r)).hom ≫
        ((E₀ ⋙ Fs).obj (P.X p) ◁
          (hatTensor E₀ E₁ Fi Fs a (Q.X q) (H.X r)).hom) =
      (hatTensor E₀ E₁ Fi Fs a (P.X p ⊗ Q.X q) (H.X r)).hom ≫
        ((hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ▷
          (E₀ ⋙ Fs).obj (H.X r)) ≫
        (α_ ((E₀ ⋙ Fs).obj (P.X p)) ((E₀ ⋙ Fs).obj (Q.X q))
          ((E₀ ⋙ Fs).obj (H.X r))).hom) →
    (Fs.mapHomologicalComplex (.up ℤ)).map
        ((E₀.mapHomologicalComplex (.up ℤ)).map (α_ P Q H).hom) ≫
        (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P (Q ⊗ H)).hom ≫
        (image E₀ Fs P ◁ (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a Q H).hom) =
      (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a (P ⊗ Q) H).hom ≫
        ((totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom ▷ image E₀ Fs H) ≫
        (α_ (image E₀ Fs P) (image E₀ Fs Q) (image E₀ Fs H)).hom) ∧
  (∀ (P : CochainComplex A₀ ℤ),
    (∀ n : ℤ, (E₀ ⋙ Fs).map (λ_ (P.X n)).hom =
      (hatTensor E₀ E₁ Fi Fs a (𝟙_ A₀) (P.X n)).hom ≫
        ((hatUnit E₀ E₁ Fi Fs a).hom ▷ (E₀ ⋙ Fs).obj (P.X n)) ≫
        (λ_ ((E₀ ⋙ Fs).obj (P.X n))).hom) →
    (Fs.mapHomologicalComplex (.up ℤ)).map
        ((E₀.mapHomologicalComplex (.up ℤ)).map (λ_ P).hom) =
      (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a (𝟙_ (CochainComplex A₀ ℤ)) P).hom ≫
        ((totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom ▷ image E₀ Fs P) ≫
        (λ_ (image E₀ Fs P)).hom) ∧
  (∀ (P : CochainComplex A₀ ℤ),
    (∀ n : ℤ, (E₀ ⋙ Fs).map (ρ_ (P.X n)).hom =
      (hatTensor E₀ E₁ Fi Fs a (P.X n) (𝟙_ A₀)).hom ≫
        ((E₀ ⋙ Fs).obj (P.X n) ◁ (hatUnit E₀ E₁ Fi Fs a).hom) ≫
        (ρ_ ((E₀ ⋙ Fs).obj (P.X n))).hom) →
    (Fs.mapHomologicalComplex (.up ℤ)).map
        ((E₀.mapHomologicalComplex (.up ℤ)).map (ρ_ P).hom) =
      (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P (𝟙_ (CochainComplex A₀ ℤ))).hom ≫
        (image E₀ Fs P ◁ (totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom) ≫
        (ρ_ (image E₀ Fs P)).hom)

include hFsMonoidal

attribute [local instance 2000] tensorExists tensorGoodLeft tensorGoodRight tensorFour


private theorem forward (P Q : CochainComplex A₀ ℤ) (p q n : ℤ) (h : p + q = n) :
    Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
        ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ≫
      (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f n =
    (tensorComparison E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ≫
      ιTensorObj (image E₀ Fs P) (image E₀ Fs Q) p q n h := by
  exact Functor.total_oplax_conjugation_summands E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a P Q p q n h

private theorem inverse_summand (P Q : CochainComplex A₀ ℤ)
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (image E₀ Fs P) (image E₀ Fs Q) p q n h ≫
        (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv.f n =
      (tensorComparison E₀ E₁ Fi Fs a (P.X p) (Q.X q)).inv ≫
        Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
          ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) := by
  apply (cancel_epi (tensorComparison E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom).1
  rw [← Category.assoc, ← forward E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a P Q p q n h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  exact Category.comp_id _

private theorem hat_forward (P Q : CochainComplex A₀ ℤ)
    (p q n : ℤ) (h : p + q = n) :
    (E₀ ⋙ Fs).map (ιTensorObj P Q p q n h) ≫
        (totalHatTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f n =
      (hatTensor E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ≫
        ιTensorObj (image E₀ Fs P) (image E₀ Fs Q) p q n h := by
  change Fs.map (E₀.map (ιTensorObj P Q p q n h)) ≫
    (Fs.map ((E₀.mapCochainComplexμIso P Q).inv.f n) ≫
      (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f n) = _
  rw [← Fs.map_comp_assoc,
    total_inverse_restriction E₀ (hG := fun I _ ↦ inferInstance),
    Fs.map_comp, Category.assoc,
    forward E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a P Q p q n h]
  simp only [hatTensor, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, Category.assoc]

private theorem unit_zero :
    (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 =
      Fs.map (singleObjXSelf (.up ℤ) 0 (𝟙_ B₀)).hom ≫
        (unitComparison E₀ E₁ Fi Fs a).hom ≫
          (singleObjXSelf (.up ℤ) 0 (𝟙_ B₁)).inv := by
  change Fs.map (E₀.mapCochainComplexεIso.hom.f 0) ≫
      a.inv.app ((𝟙_ (CochainComplex A₀ ℤ)).X 0) ≫
        E₁.map (Fi.mapCochainComplexεIso.inv.f 0) ≫ E₁.mapCochainComplexεIso.inv.f 0 = _
  rw [Functor.mapCochainComplexεIso_hom_f_zero, unit_inverse_zero Fi (hG := hFi),
    unit_inverse_zero E₁ (hG := fun I _ ↦ inferInstance)]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (a.inv.naturality (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv)]
  simp only [← E₁.map_comp_assoc, ← Fi.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp, unitComparison, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Functor.Monoidal.εIso_hom,
    Functor.Monoidal.εIso_inv, Iso.app_inv, Category.assoc]

private theorem hat_unit_zero :
    (totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 =
      (E₀ ⋙ Fs).map (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).hom ≫
        (hatUnit E₀ E₁ Fi Fs a).hom ≫
          (singleObjXSelf (.up ℤ) 0 (𝟙_ B₁)).inv := by
  change Fs.map (E₀.mapCochainComplexεIso.inv.f 0) ≫
    (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 = _
  rw [unit_inverse_zero E₀ (hG := fun I _ ↦ inferInstance),
    unit_zero E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  simp only [hatUnit, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.Monoidal.εIso_inv, Functor.comp_map, Category.assoc]

private theorem hat_unit_normalized :
    (E₀ ⋙ Fs).map (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv ≫
        (totalHatUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom.f 0 =
      (hatUnit E₀ E₁ Fi Fs a).hom ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ B₁)).inv := by
  rw [hat_unit_zero E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a]
  exact Iso.map_inv_hom_id_assoc _ _ _

private theorem inverse_and_unit : InverseAndUnit E₀ E₁ Fi Fs (hFi := hFi) a := by
  refine ⟨inverse_summand E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a, ?_,
    unit_zero E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a, ?_⟩
  · intro P Q
    exact ⟨Iso.hom_inv_id _, Iso.inv_hom_id _,
      fun n m ↦ ((totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).inv.comm n m).symm⟩
  · intro n hn
    have hs := Fs.map_isZero (isZero_single_obj_X (.up ℤ) 0 (𝟙_ B₀) n hn)
    exact ⟨hs, isZero_single_obj_X (.up ℤ) 0 (𝟙_ B₁) n hn,
      fun f ↦ hs.eq_of_src f _⟩

omit hFi hFs hFsMonoidal in
private theorem zero_unit_summands : ZeroUnitSummands E₀ Fs := by
  intro P p q n h Z
  constructor
  · intro hp f
    apply IsZero.eq_of_src
    exact (E₀ ⋙ Fs).map_isZero
      ((tensorRight (P.X q)).map_isZero (isZero_single_obj_X (.up ℤ) 0 (𝟙_ A₀) p hp))
  · intro hq f
    apply IsZero.eq_of_src
    exact (E₀ ⋙ Fs).map_isZero
      ((tensorLeft (P.X p)).map_isZero (isZero_single_obj_X (.up ℤ) 0 (𝟙_ A₀) q hq))

omit hFi hFsMonoidal in
private theorem summand_detection : SummandDetection E₀ Fs := by
  have hg : ∀ (I : Type) [Countable I],
      PreservesColimitsOfShape (Discrete I) (E₀ ⋙ Fs) := fun I _ ↦ inferInstance
  exact ⟨double_detection Fs (hG := hFs), double_detection (E₀ ⋙ Fs) (hG := hg),
    left_detection (E₀ ⋙ Fs) (hG := hg), right_detection (E₀ ⋙ Fs) (hG := hg)⟩

private theorem recovery : Recovery E₀ E₁ Fi Fs (hFi := hFi) a := by
  refine ⟨?_, ?_, hat_unit_zero E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a⟩
  · intro P Q
    apply Iso.ext
    change (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom =
      (Fs.mapHomologicalComplex (.up ℤ)).map (E₀.mapCochainComplexμIso P Q).hom ≫
        (Fs.mapHomologicalComplex (.up ℤ)).map (E₀.mapCochainComplexμIso P Q).inv ≫
          (totalTensor E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  · apply Iso.ext
    change (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom =
      (Fs.mapHomologicalComplex (.up ℤ)).map E₀.mapCochainComplexεIso.hom ≫
        (Fs.mapHomologicalComplex (.up ℤ)).map E₀.mapCochainComplexεIso.inv ≫
          (totalUnit E₀ E₁ Fi Fs (hFi := hFi) a).hom
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]

private theorem intermediate_comparisons :
    IntermediateComparisons E₀ E₁ Fi Fs (hFi := hFi) a := by
  exact ⟨hat_forward E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a,
    hatTensor_naturality E₀ E₁ Fi Fs a⟩

private theorem associator_paths : AssociatorPaths E₀ E₁ Fi Fs (hFi := hFi) a := by
  intro P Q H p q r n h
  have h' : p + (q + r) = n := by omega
  have hf := hat_forward E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a
  have hn := hatTensor_naturality E₀ E₁ Fi Fs a
  constructor
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    change (E₀ ⋙ Fs).map (leftInclusion P Q H p q r n h) ≫
      (E₀ ⋙ Fs).map ((α_ P Q H).hom.f n) ≫ _ = _
    rw [← Functor.map_comp_assoc]
    rw [show leftInclusion P Q H p q r n h ≫ (α_ P Q H).hom.f n =
      (α_ (P.X p) (Q.X q) (H.X r)).hom ≫ rightInclusion P Q H p q r n h from
        CochainComplex.Monoidal.ι₁₂_associator_hom P Q H p q r n h]
    rw [Functor.map_comp, Category.assoc]
    simp only [rightInclusion, CochainComplex.Monoidal.ι₂₃_eq P Q H p q r (q + r) n
      rfl h', Functor.map_comp, Category.assoc]
    erw [reassoc_of% (hf P (Q ⊗ H) p (q + r) n h')]
    have hn' := hn (P.X p) (Q.X q ⊗ H.X r) (P.X p) ((Q ⊗ H).X (q + r))
      (𝟙 _) (ιTensorObj Q H q r (q + r) rfl)
    simp only [id_tensorHom, Functor.map_id] at hn'
    erw [reassoc_of% hn']
    simp only [id_tensorHom]
    erw [CochainComplex.ιTensorObj_whiskerLeft_f]
    erw [← whiskerLeft_comp_assoc]
    erw [hf Q H q r (q + r) rfl]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q r (q + r) n rfl h']
    rfl
  · simp only [HomologicalComplex.comp_f]
    simp only [leftInclusion, CochainComplex.Monoidal.ι₁₂_eq P Q H p q r (p + q) n
      rfl h, Functor.map_comp, Category.assoc]
    erw [reassoc_of% (hf (P ⊗ Q) H (p + q) r n h)]
    have hn' := hn (P.X p ⊗ Q.X q) (H.X r) ((P ⊗ Q).X (p + q)) (H.X r)
      (ιTensorObj P Q p q (p + q) rfl) (𝟙 _)
    simp only [tensorHom_id, Functor.map_id] at hn'
    erw [reassoc_of% hn']
    simp only [tensorHom_id]
    erw [CochainComplex.Monoidal.ι_whiskerRight_assoc]
    erw [← comp_whiskerRight_assoc]
    erw [hf P Q p q (p + q) rfl]
    simp only [comp_whiskerRight, Category.assoc]
    erw [← reassoc_of% (CochainComplex.Monoidal.ι₁₂_eq
      (image E₀ Fs P) (image E₀ Fs Q) (image E₀ Fs H) p q r (p + q) n rfl h)]
    erw [CochainComplex.Monoidal.ι₁₂_associator_hom]
    rfl

private theorem unit_paths : UnitPaths E₀ E₁ Fi Fs (hFi := hFi) a := by
  intro P n
  have hf := hat_forward E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a
  have hn := hatTensor_naturality E₀ E₁ Fi Fs a
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (E₀ ⋙ Fs).map (leftUnitInclusion P n) ≫ (E₀ ⋙ Fs).map ((λ_ P).hom.f n) = _
    rw [← Functor.map_comp]
    simpa only [leftUnitInclusion, Category.assoc] using
      congrArg (E₀ ⋙ Fs).map (left_unit_restriction P n)
  · simp only [leftUnitInclusion, HomologicalComplex.comp_f, Functor.map_comp,
      Category.assoc]
    erw [reassoc_of% (hf (𝟙_ (CochainComplex A₀ ℤ)) P 0 n n (zero_add n))]
    have hn' := hn (𝟙_ A₀) (P.X n) ((𝟙_ (CochainComplex A₀ ℤ)).X 0) (P.X n)
      (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv (𝟙 _)
    simp only [tensorHom_id, Functor.map_id] at hn'
    erw [reassoc_of% hn']
    simp only [tensorHom_id]
    erw [CochainComplex.Monoidal.ι_whiskerRight_assoc]
    erw [← comp_whiskerRight_assoc]
    erw [hat_unit_normalized E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a]
    simp only [comp_whiskerRight, Category.assoc]
    erw [left_unit_restriction (image E₀ Fs P) n]
    rfl
  · change (E₀ ⋙ Fs).map (rightUnitInclusion P n) ≫ (E₀ ⋙ Fs).map ((ρ_ P).hom.f n) = _
    rw [← Functor.map_comp]
    simpa only [rightUnitInclusion, Category.assoc] using
      congrArg (E₀ ⋙ Fs).map (right_unit_restriction P n)
  · simp only [rightUnitInclusion, HomologicalComplex.comp_f, Functor.map_comp,
      Category.assoc]
    erw [reassoc_of% (hf P (𝟙_ (CochainComplex A₀ ℤ)) n 0 n (add_zero n))]
    have hn' := hn (P.X n) (𝟙_ A₀) (P.X n) ((𝟙_ (CochainComplex A₀ ℤ)).X 0)
      (𝟙 _) (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv
    simp only [id_tensorHom, Functor.map_id] at hn'
    erw [reassoc_of% hn']
    simp only [id_tensorHom]
    erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc]
    erw [← whiskerLeft_comp_assoc]
    erw [hat_unit_normalized E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [right_unit_restriction (image E₀ Fs P) n]
    rfl

private theorem lift_equality
    (ha : AssociatorPaths E₀ E₁ Fi Fs (hFi := hFi) a)
    (hu : UnitPaths E₀ E₁ Fi Fs (hFi := hFi) a)
    (hz : ZeroUnitSummands E₀ Fs) (hd : SummandDetection E₀ Fs) :
    LiftConstraintEquality E₀ E₁ Fi Fs (hFi := hFi) a := by
  refine ⟨?_, ?_, ?_⟩
  · intro P Q H he
    ext n : 1
    apply hd.2.2.1 P Q H n
    intro p q r h
    rw [(ha P Q H p q r n h).1, (ha P Q H p q r n h).2]
    exact (reassoc_of% (he p q r)) _
  · intro P he
    ext n : 1
    apply hd.2.1 (𝟙_ (CochainComplex A₀ ℤ)) P n
    intro p q h
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by simpa using h
      subst q
      apply (cancel_epi ((E₀ ⋙ Fs).map
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv ▷ P.X n))).1
      simpa only [← Functor.map_comp_assoc, leftUnitInclusion, Category.assoc] using
        (hu P n).1.trans ((he n).trans (hu P n).2.1.symm)
    · rw [(hz P p q n h _).1 hp, (hz P p q n h _).1 hp]
  · intro P he
    ext n : 1
    apply hd.2.1 P (𝟙_ (CochainComplex A₀ ℤ)) n
    intro p q h
    by_cases hq : q = 0
    · subst q
      have hp : p = n := by simpa using h
      subst p
      apply (cancel_epi ((E₀ ⋙ Fs).map
        (P.X n ◁ (singleObjXSelf (.up ℤ) 0 (𝟙_ A₀)).inv))).1
      simpa only [← Functor.map_comp_assoc, rightUnitInclusion, Category.assoc] using
        (hu P n).2.2.1.trans ((he n).trans (hu P n).2.2.2.symm)
    · rw [(hz P p q n h _).2 hq, (hz P p q n h _).2 hq]

-- The smallest-universe instances above are restrictions of these full hypotheses.
-- They are explicit to avoid choosing new colimit data inside a statement.
variable
  [allA₀ : HasColimitsOfSize.{w, w} A₀]
  [allA₁ : HasColimitsOfSize.{w, w} A₁]
  [allB₀ : HasColimitsOfSize.{w, w} B₀]
  [allB₁ : HasColimitsOfSize.{w, w} B₁]
  [leftA₀ : ∀ X : A₀, PreservesColimitsOfSize.{w, w} ((curriedTensor A₀).obj X)]
  [rightA₀ : ∀ X : A₀, PreservesColimitsOfSize.{w, w} ((curriedTensor A₀).flip.obj X)]
  [leftA₁ : ∀ X : A₁, PreservesColimitsOfSize.{w, w} ((curriedTensor A₁).obj X)]
  [rightA₁ : ∀ X : A₁, PreservesColimitsOfSize.{w, w} ((curriedTensor A₁).flip.obj X)]
  [leftB₀ : ∀ X : B₀, PreservesColimitsOfSize.{w, w} ((curriedTensor B₀).obj X)]
  [rightB₀ : ∀ X : B₀, PreservesColimitsOfSize.{w, w} ((curriedTensor B₀).flip.obj X)]
  [leftB₁ : ∀ X : B₁, PreservesColimitsOfSize.{w, w} ((curriedTensor B₁).obj X)]
  [rightB₁ : ∀ X : B₁, PreservesColimitsOfSize.{w, w} ((curriedTensor B₁).flip.obj X)]

include allA₀ allA₁ allB₀ allB₁ leftA₀ rightA₀ leftA₁ rightA₁ leftB₀ rightB₀ leftB₁ rightB₁
  hFsMonoidal

/-- All inverse and constraint restrictions of the specified total conjugation.
Source: Stacks Project, Tag 0FPQ, lemma-symmetric-monoidal-cat-complexes,
agent extraction of inverse and constraint path transport through a functor square
(blueprint: lem-pd-total-oplax-conjugation-constraints).

Proof:
1. Apply lem-sfb-termwise-strong-monoidal to all four functors. The equivalences
preserve colimits by lem-weil-pbc-left-adjoint-preserves-colimits. Termwise a is
invertible by naturality for the differential. The forward restriction is supplied
by lem-pd-total-oplax-conjugation-summands.
2. Cancel A and the ordinary tensor comparison in that forward restriction. This
computes the actual inverse of A, its chain equation and both inverse identities.
3. The canonical unit comparisons compute J in degree zero as the displayed
ordinary composite. Additivity preserves zero objects, giving uniqueness elsewhere.
4. Cancel adjacent E₀ comparisons in A-hat and J-hat. The forward summand equation
then gives the intermediate comparison formula. Naturality holds factor by factor.
5. The associator from lem-sfb-total-tensor-homotopy carries the left triple
injection to the right injection preceded by the ordinary associator. Tensoring
chain maps acts on injections by the degreewise tensor of maps, as in
 def-sfb-preserves-kflat-quasi-iso.
6. For the first path use this associator formula, then the outer comparison's
summand formula and naturality with the inner injection, then the inner comparison.
7. For the second path expand the outer comparison using naturality with the
left inner injection, then the inner comparison, then the target associator.
8. For the unit paths only (0,n) and (n,0) survive. The preceding unit calculation
and the induced unitor formulas give precisely the four ordinary unit paths.
Other summands are zero since tensoring preserves the empty coproduct.
9. Expanding A-hat and J-hat cancels a with its inverse at inner totals; naturality
moves it past the constraints. Reinsert Fs(T_E₀) and Fs(j_E₀) to recover A and J.
No monoidal equation for a is used.
10. The coproduct universal property in def-weil-pbc-category-colimit detects
maps on every double summand. Apply it to the inner and outer coproducts for
triple summands; tensoring, E₀ and Fs preserve those coproducts. Degreewise
extensionality then detects the whole chain map and lifts ordinary path equality.
-/
theorem constraints :
    InverseAndUnit E₀ E₁ Fi Fs (hFi := hFi) a ∧
    IntermediateComparisons E₀ E₁ Fi Fs (hFi := hFi) a ∧
    AssociatorPaths E₀ E₁ Fi Fs (hFi := hFi) a ∧
    UnitPaths E₀ E₁ Fi Fs (hFi := hFi) a ∧
    ZeroUnitSummands E₀ Fs ∧
    SummandDetection E₀ Fs ∧
    Recovery E₀ E₁ Fi Fs (hFi := hFi) a ∧
    LiftConstraintEquality E₀ E₁ Fi Fs (hFi := hFi) a := by
  have ha := associator_paths E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a
  have hu := unit_paths E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a
  have hz := zero_unit_summands E₀ Fs
  have hd := summand_detection E₀ Fs (hFs := hFs)
  exact ⟨inverse_and_unit E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a,
    intermediate_comparisons E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a, ha, hu, hz, hd,
    recovery E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a,
    lift_equality E₀ E₁ Fi Fs (hFi := hFi) (hFs := hFs) a ha hu hz hd⟩

end Complexes
end CategoryTheory.TotalOplaxConjugation
