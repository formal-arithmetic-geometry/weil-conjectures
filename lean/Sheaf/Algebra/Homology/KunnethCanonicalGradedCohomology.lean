/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
public import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.Algebra.Homology.KunnethCanonicalTensorData
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Cohomology of a canonically graded convolution
Source: Stacks Project, More on Algebra, Tag 0H7Z.
(blueprint: lem-kun-canonical-graded-cohomology).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u w v v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace DerivedCategory
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

section Support
variable {R}

private def finiteSupportSigmaIso {J : Type} (X : J → ModuleCat.{u} R) (s : Finset J)
    (hz : ∀ j, j ∉ s → IsZero (X j)) : (∐ fun j : ↥s ↦ X j.val) ≅ ∐ X := by
  classical
  refine
    { hom := Limits.Sigma.desc (fun j ↦ Limits.Sigma.ι X j.val)
      inv := Limits.Sigma.desc (fun j ↦ if h : j ∈ s then
        Limits.Sigma.ι (fun j : ↥s ↦ X j.val) ⟨j, h⟩ else 0)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Limits.Sigma.hom_ext
    intro j
    simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, dif_pos j.property, Category.comp_id]
  · apply Limits.Sigma.hom_ext
    intro j
    by_cases hj : j ∈ s
    · simp only [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, dif_pos hj, Category.comp_id]
    · exact (hz j hj).eq_of_src _ _

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem finiteSupportSigmaIso_naturality {J : Type}
    (X Y : J → ModuleCat.{u} R) (f : ∀ j, X j ⟶ Y j) (s : Finset J)
    (hX : ∀ j, j ∉ s → IsZero (X j)) (hY : ∀ j, j ∉ s → IsZero (Y j)) :
    Limits.Sigma.map (fun j : ↥s ↦ f j.val) ≫ (finiteSupportSigmaIso Y s hY).hom =
      (finiteSupportSigmaIso X s hX).hom ≫ Limits.Sigma.map f := by
  apply Limits.Sigma.hom_ext
  intro j
  simp [finiteSupportSigmaIso]

variable {C : Type v} [Category.{v'} C] [Preadditive C] [HasZeroObject C]
  [HasFiniteBiproducts C]

private def supportedBiproductIso (H : C ⥤ ModuleCat.{u} R) [H.Additive]
    (X : ℤ → C) (s : Finset ℤ) (hz : ∀ i, i ∉ s → IsZero (X i)) :
    H.obj (⨁ fun i : ↥s ↦ X i.val) ≅ ∐ fun i ↦ H.obj (X i) :=
  H.mapBiproduct (fun i : ↥s ↦ X i.val) ≪≫
    biproduct.isoCoproduct (fun i : ↥s ↦ H.obj (X i.val)) ≪≫
      finiteSupportSigmaIso (fun i ↦ H.obj (X i)) s
        (fun i hi ↦ H.map_isZero (hz i hi))

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasZeroObject C] in
private theorem supportedBiproductIso_inv (H : C ⥤ ModuleCat.{u} R) [H.Additive]
    (X : ℤ → C) (s : Finset ℤ) (hz : ∀ i, i ∉ s → IsZero (X i))
    (i : ℤ) (hi : i ∈ s) :
    Limits.Sigma.ι (fun i ↦ H.obj (X i)) i ≫ (supportedBiproductIso H X s hz).inv =
      H.map (biproduct.ι (fun i : ↥s ↦ X i.val) ⟨i, hi⟩) := by
  simp [supportedBiproductIso, finiteSupportSigmaIso, Category.assoc, hi,
    biproduct.isoCoproduct_inv]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasZeroObject C] in
private theorem supportedBiproductIso_extension (H : C ⥤ ModuleCat.{u} R) [H.Additive]
    (X : ℤ → C) (s t : Finset ℤ) (hst : s ⊆ t)
    (hs : ∀ i, i ∉ s → IsZero (X i)) (ht : ∀ i, i ∉ t → IsZero (X i))
    (inc : (⨁ fun i : ↥s ↦ X i.val) ⟶ ⨁ fun i : ↥t ↦ X i.val)
    (hinc : ∀ i : ↥s, biproduct.ι _ i ≫ inc =
      biproduct.ι (fun i : ↥t ↦ X i.val) ⟨i.val, hst i.property⟩) :
    (supportedBiproductIso H X s hs).inv ≫ H.map inc =
      (supportedBiproductIso H X t ht).inv := by
  apply Limits.Sigma.hom_ext
  intro i
  by_cases hi : i ∈ s
  · rw [← Category.assoc, supportedBiproductIso_inv H X s hs i hi,
      ← H.map_comp, hinc ⟨i, hi⟩,
      supportedBiproductIso_inv H X t ht i (hst hi)]
  · exact (H.map_isZero (hs i hi)).eq_of_src _ _

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasZeroObject C] in
private theorem supportedBiproductIso_naturality (H : C ⥤ ModuleCat.{u} R) [H.Additive]
    (X Y : ℤ → C) (f : ∀ i, X i ⟶ Y i) (s : Finset ℤ)
    (hX : ∀ i, i ∉ s → IsZero (X i)) (hY : ∀ i, i ∉ s → IsZero (Y i)) :
    (supportedBiproductIso H X s hX).inv ≫
        H.map (biproduct.map (fun i : ↥s ↦ f i.val)) =
      Limits.Sigma.map (fun i ↦ H.map (f i)) ≫ (supportedBiproductIso H Y s hY).inv := by
  apply Limits.Sigma.hom_ext
  intro i
  by_cases hi : i ∈ s
  · rw [← Category.assoc, supportedBiproductIso_inv H X s hX i hi,
      ← H.map_comp, biproduct.ι_map, H.map_comp]
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
      supportedBiproductIso_inv H Y s hY i hi]
  · exact (H.map_isZero (hX i hi)).eq_of_src _ _

end Support

private abbrev gradedTensorFamily (d : CanonicalTensorLocalizationData R)
    (U V : finiteFilteredModuleDerivedCategory R) (a i : ℤ) :=
  (d.gr i).obj U ⊗ (d.gr (a - i)).obj V

private def gradedCoproductIsoAt (d : CanonicalTensorLocalizationData R)
    (U V : finiteFilteredModuleDerivedCategory R) (n a : ℤ) (s : Finset ℤ)
    (hs : ∀ i, i ∉ s → IsZero (gradedTensorFamily R d U V a i)) :
    (homologyFunctor (ModuleCat.{u} R) n).obj ((d.gr a).obj ((d.star.obj U).obj V)) ≅
      ∐ fun i ↦ (homologyFunctor (ModuleCat.{u} R) n).obj
        (gradedTensorFamily R d U V a i) :=
  (homologyFunctor (ModuleCat.{u} R) n).mapIso (d.graded a U V s hs) ≪≫
    supportedBiproductIso (homologyFunctor (ModuleCat.{u} R) n)
      (gradedTensorFamily R d U V a) s hs

private theorem gradedCoproductIsoAt_extension (d : CanonicalTensorLocalizationData R)
    (U V : finiteFilteredModuleDerivedCategory R) (n a : ℤ) (s t : Finset ℤ)
    (hst : s ⊆ t)
    (hs : ∀ i, i ∉ s → IsZero (gradedTensorFamily R d U V a i))
    (ht : ∀ i, i ∉ t → IsZero (gradedTensorFamily R d U V a i)) :
    (gradedCoproductIsoAt R d U V n a s hs).inv =
      (gradedCoproductIsoAt R d U V n a t ht).inv := by
  obtain ⟨inc, hinc, he⟩ := d.graded_extension a U V s t hst hs ht
  have hi : inc ≫ (d.graded a U V t ht).inv = (d.graded a U V s hs).inv := by
    apply (cancel_epi (d.graded a U V s hs).hom).1
    rw [← Category.assoc, he, Iso.hom_inv_id, Iso.hom_inv_id]
  dsimp only [gradedCoproductIsoAt, Iso.trans_inv, Functor.mapIso_inv]
  rw [← hi, Functor.map_comp, ← Category.assoc]
  rw [supportedBiproductIso_extension _ _ s t hst hs ht inc hinc]

private theorem gradedCoproductIsoAt_naturality (d : CanonicalTensorLocalizationData R)
    {U U' V V' : finiteFilteredModuleDerivedCategory R} (f : U ⟶ U') (g : V ⟶ V')
    (n a : ℤ) (s : Finset ℤ)
    (hs : ∀ i, i ∉ s → IsZero (gradedTensorFamily R d U V a i))
    (hs' : ∀ i, i ∉ s → IsZero (gradedTensorFamily R d U' V' a i)) :
    (gradedCoproductIsoAt R d U V n a s hs).inv ≫
        (homologyFunctor (ModuleCat.{u} R) n).map
          ((d.gr a).map ((d.star.map f).app V ≫ (d.star.obj U').map g)) =
      Limits.Sigma.map (fun i ↦ (homologyFunctor (ModuleCat.{u} R) n).map
          ((d.gr i).map f ⊗ₘ (d.gr (a - i)).map g)) ≫
        (gradedCoproductIsoAt R d U' V' n a s hs').inv := by
  let z := (d.gr a).map ((d.star.map f).app V ≫ (d.star.obj U').map g)
  let m := biproduct.map (fun i : ↥s ↦ (d.gr i.val).map f ⊗ₘ (d.gr (a - i.val)).map g)
  have he : (d.graded a U V s hs).inv ≫ z = m ≫ (d.graded a U' V' s hs').inv := by
    apply (cancel_epi (d.graded a U V s hs).hom).1
    apply (cancel_mono (d.graded a U' V' s hs').hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
      using (d.graded_naturality a f g s hs hs').symm
  dsimp only [gradedCoproductIsoAt, Iso.trans_inv, Functor.mapIso_inv]
  rw [Category.assoc, ← Functor.map_comp, he, Functor.map_comp, ← Category.assoc]
  dsimp only [m]
  rw [supportedBiproductIso_naturality (homologyFunctor (ModuleCat.{u} R) n)
    (gradedTensorFamily R d U V a) (gradedTensorFamily R d U' V' a)
      (fun i ↦ (d.gr i).map f ⊗ₘ (d.gr (a - i)).map g) s hs hs']
  exact Category.assoc _ _ _

private def gradedCoproductIso (d : CanonicalTensorLocalizationData R)
    (U V : finiteFilteredModuleDerivedCategory R) (n a : ℤ) :=
  gradedCoproductIsoAt R d U V n a (d.finite_support a U V).choose
    (d.finite_support a U V).choose_spec

private theorem gradedCoproductIso_naturality (d : CanonicalTensorLocalizationData R)
    {U U' V V' : finiteFilteredModuleDerivedCategory R} (f : U ⟶ U') (g : V ⟶ V')
    (n a : ℤ) :
    (gradedCoproductIso R d U V n a).inv ≫
        (homologyFunctor (ModuleCat.{u} R) n).map
          ((d.gr a).map ((d.star.map f).app V ≫ (d.star.obj U').map g)) =
      Limits.Sigma.map (fun i ↦ (homologyFunctor (ModuleCat.{u} R) n).map
          ((d.gr i).map f ⊗ₘ (d.gr (a - i)).map g)) ≫
        (gradedCoproductIso R d U' V' n a).inv := by
  let s := (d.finite_support a U V).choose
  let t := (d.finite_support a U' V').choose
  have hs := (d.finite_support a U V).choose_spec
  have ht := (d.finite_support a U' V').choose_spec
  have hs' (i : ℤ) (hi : i ∉ s ∪ t) : IsZero (gradedTensorFamily R d U V a i) :=
    hs i (fun h ↦ hi (Finset.mem_union.mpr (Or.inl h)))
  have ht' (i : ℤ) (hi : i ∉ s ∪ t) : IsZero (gradedTensorFamily R d U' V' a i) :=
    ht i (fun h ↦ hi (Finset.mem_union.mpr (Or.inr h)))
  change (gradedCoproductIsoAt R d U V n a s hs).inv ≫ _ =
    _ ≫ (gradedCoproductIsoAt R d U' V' n a t ht).inv
  rw [gradedCoproductIsoAt_extension R d U V n a s (s ∪ t)
    Finset.subset_union_left hs hs',
    gradedCoproductIsoAt_extension R d U' V' n a t (s ∪ t)
      Finset.subset_union_right ht ht']
  exact gradedCoproductIsoAt_naturality R d f g n a (s ∪ t) hs' ht'

section ShiftComparison
variable {R}
private theorem shiftTensorShiftIso_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ X') (g : Y ⟶ Y')
    (a b : ℤ) :
    (f⟦a⟧' ⊗ₘ g⟦b⟧') ≫ (shiftTensorShiftIso (ModuleCat.{u} R) X' Y' a b).hom =
      (shiftTensorShiftIso (ModuleCat.{u} R) X Y a b).hom ≫ (f ⊗ₘ g)⟦a + b⟧' := by
  let G := curriedTensor (DerivedCategory (ModuleCat.{u} R))
  have h₁ := NatTrans.shift_app_comm (G.flip.map (g⟦b⟧')) a X
  have h₂ := ((G.flip.obj (Y'⟦b⟧)).commShiftIso a).hom.naturality f
  have h₃ := NatTrans.shift_app_comm (G.map f) b Y
  have h₄ := ((G.obj X').commShiftIso b).hom.naturality g
  simp only [G, Functor.flip_map_app, curriedTensor_obj_map, curriedTensor_map_app,
    Functor.comp_map, Functor.flip_obj_obj] at h₁ h₂ h₃ h₄
  simp only [shiftTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  let A (K L : DerivedCategory (ModuleCat.{u} R)) :=
    (((G.flip.obj (L⟦b⟧)).commShiftIso a).hom.app K)
  let B (K L : DerivedCategory (ModuleCat.{u} R)) :=
    (((G.obj K).commShiftIso b).hom.app L)
  symm at h₁ h₃
  change (X⟦a⟧ ◁ g⟦b⟧') ≫ A X Y' = A X Y ≫ (X ◁ g⟦b⟧')⟦a⟧' at h₁
  change (f⟦a⟧' ▷ Y'⟦b⟧) ≫ A X' Y' = A X Y' ≫ (f ▷ Y'⟦b⟧)⟦a⟧' at h₂
  change (f ▷ Y⟦b⟧) ≫ B X' Y = B X Y ≫ (f ▷ Y)⟦b⟧' at h₃
  change (X' ◁ g⟦b⟧') ≫ B X' Y' = B X' Y ≫ (X' ◁ g)⟦b⟧' at h₄
  have hA : (f⟦a⟧' ⊗ₘ g⟦b⟧') ≫ A X' Y' = A X Y ≫ (f ⊗ₘ g⟦b⟧')⟦a⟧' := by
    rw [tensorHom_def', Category.assoc, h₂, ← Category.assoc, h₁,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def']
  have hB : (f ⊗ₘ g⟦b⟧') ≫ B X' Y' = B X Y ≫ (f ⊗ₘ g)⟦b⟧' := by
    rw [tensorHom_def, Category.assoc, h₄, ← Category.assoc, h₃,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have hC := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) b a (a + b)
    (add_comm b a)).inv.naturality (f ⊗ₘ g)
  change _ ≫ A X' Y' ≫ (B X' Y')⟦a⟧' ≫ _ = A X Y ≫ (B X Y)⟦a⟧' ≫ _
  rw [reassoc_of% hA, ← Functor.map_comp_assoc, hB, Functor.map_comp_assoc]
  exact congrArg (A X Y ≫ (B X Y)⟦a⟧' ≫ ·) hC

private def tensorShiftCohomologyIso' (X Y : DerivedCategory (ModuleCat.{u} R))
    (n a b c : ℤ) (h : a + b = c) :
    (homologyFunctor (ModuleCat.{u} R) n).obj (X⟦a⟧ ⊗ Y⟦b⟧) ≅
      (homologyFunctor (ModuleCat.{u} R) (n + c)).obj (X ⊗ Y) :=
  (homologyFunctor (ModuleCat.{u} R) n).mapIso
    (shiftTensorShiftIso (ModuleCat.{u} R) X Y a b) ≪≫
      ((homologyFunctor (ModuleCat.{u} R) 0).shiftIso (a + b) n (n + c)
        (by omega)).app (X ⊗ Y)

private theorem tensorShiftCohomologyIso'_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ X') (g : Y ⟶ Y')
    (n a b c : ℤ) (h : a + b = c) :
    (homologyFunctor (ModuleCat.{u} R) n).map (f⟦a⟧' ⊗ₘ g⟦b⟧') ≫
        (tensorShiftCohomologyIso' X' Y' n a b c h).hom =
      (tensorShiftCohomologyIso' X Y n a b c h).hom ≫
        (homologyFunctor (ModuleCat.{u} R) (n + c)).map (f ⊗ₘ g) := by
  have hn := ((homologyFunctor (ModuleCat.{u} R) 0).shiftIso (a + b) n (n + c)
    (by omega)).hom.naturality (f ⊗ₘ g)
  dsimp only [tensorShiftCohomologyIso', Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp, shiftTensorShiftIso_naturality,
    Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) hn
end ShiftComparison

private def canonicalSummandIso (d : CanonicalTensorLocalizationData R)
    (C D : Bounded (ModuleCat.{u} R)) (n a i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) n).obj
        (gradedTensorFamily R d (d.T.obj C) (d.T.obj D) a i) ≅
      ((kunnethModuleTensorHomology R (n + a)).obj
        ((homologyFunctor (ModuleCat.{u} R) (-i)).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) (-(a - i))).obj D.obj) :=
  (homologyFunctor (ModuleCat.{u} R) n).mapIso
    (tensorIso ((d.eTgr i).app C) ((d.eTgr (a - i)).app D)) ≪≫
      tensorShiftCohomologyIso'
        ((singleFunctor (ModuleCat.{u} R) 0).obj
          ((homologyFunctor (ModuleCat.{u} R) (-i)).obj C.obj))
        ((singleFunctor (ModuleCat.{u} R) 0).obj
          ((homologyFunctor (ModuleCat.{u} R) (-(a - i))).obj D.obj))
        n i (a - i) a (by omega)

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalSummandIso_naturality (d : CanonicalTensorLocalizationData R)
    {C C' D D' : Bounded (ModuleCat.{u} R)} (f : C ⟶ C') (g : D ⟶ D')
    (n a i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) n).map
        ((d.gr i).map (d.T.map f) ⊗ₘ (d.gr (a - i)).map (d.T.map g)) ≫
      (canonicalSummandIso R d C' D' n a i).hom =
    (canonicalSummandIso R d C D n a i).hom ≫
      (homologyFunctor (ModuleCat.{u} R) (n + a)).map
        ((singleFunctor (ModuleCat.{u} R) 0).map
          ((homologyFunctor (ModuleCat.{u} R) (-i)).map f.hom) ⊗ₘ
         (singleFunctor (ModuleCat.{u} R) 0).map
          ((homologyFunctor (ModuleCat.{u} R) (-(a - i))).map g.hom)) := by
  have h₁ := (d.eTgr i).hom.naturality f
  have h₂ := (d.eTgr (a - i)).hom.naturality g
  dsimp only [Functor.comp_map] at h₁ h₂
  dsimp only [canonicalSummandIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [tensorIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp, tensorHom_comp_tensorHom, h₁, h₂,
    ← tensorHom_comp_tensorHom, Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) (tensorShiftCohomologyIso'_naturality
    ((singleFunctor (ModuleCat.{u} R) 0).map
      ((homologyFunctor (ModuleCat.{u} R) (-i)).map f.hom))
    ((singleFunctor (ModuleCat.{u} R) 0).map
      ((homologyFunctor (ModuleCat.{u} R) (-(a - i))).map g.hom))
    n i (a - i) a (by omega))

private def diagonalEquiv (a : ℤ) : ℤ ≃ {ij : ℤ × ℤ // ij.1 + ij.2 = -a} where
  toFun i := ⟨(-i, -(a - i)), by dsimp; omega⟩
  invFun ij := -ij.val.1
  left_inv i := neg_neg i
  right_inv ij := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · omega
    · have := ij.property
      omega

private def diagonalTerm (C D : Bounded (ModuleCat.{u} R)) (n a : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = -a}) : ModuleCat.{u} R :=
  ((kunnethModuleTensorHomology R (n + a)).obj
    ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
      ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)

private def diagonalMap {C C' D D' : Bounded (ModuleCat.{u} R)}
    (f : C ⟶ C') (g : D ⟶ D') (n a : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = -a}) :
    diagonalTerm R C D n a ij ⟶ diagonalTerm R C' D' n a ij :=
  ((kunnethModuleTensorHomology R (n + a)).map
    ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
      ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
    ((kunnethModuleTensorHomology R (n + a)).obj
      ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
        ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)

private def canonicalCoproductIso (d : CanonicalTensorLocalizationData R)
    (C D : Bounded (ModuleCat.{u} R)) (n a : ℤ) :
    (∐ fun i : ℤ ↦ (homologyFunctor (ModuleCat.{u} R) n).obj
      (gradedTensorFamily R d (d.T.obj C) (d.T.obj D) a i)) ≅
        ∐ diagonalTerm R C D n a :=
  Limits.Sigma.mapIso
    (g := diagonalTerm R C D n a ∘ diagonalEquiv a)
    (fun i : ℤ ↦ canonicalSummandIso R d C D n a i) ≪≫
    Limits.Sigma.reindex (diagonalEquiv a) (diagonalTerm R C D n a)

private theorem canonicalCoproductIso_naturality (d : CanonicalTensorLocalizationData R)
    {C C' D D' : Bounded (ModuleCat.{u} R)} (f : C ⟶ C') (g : D ⟶ D')
    (n a : ℤ) :
    Limits.Sigma.map (fun i : ℤ ↦ (homologyFunctor (ModuleCat.{u} R) n).map
        ((d.gr i).map (d.T.map f) ⊗ₘ (d.gr (a - i)).map (d.T.map g))) ≫
      (canonicalCoproductIso R d C' D' n a).hom =
    (canonicalCoproductIso R d C D n a).hom ≫
      Limits.Sigma.map (diagonalMap R f g n a) := by
  apply Limits.Sigma.hom_ext
  intro i
  simp only [canonicalCoproductIso, Iso.trans_hom, Limits.Sigma.ι_map_assoc,
    Limits.Sigma.ι_mapIso_hom_assoc, Category.assoc, Limits.Sigma.ι_reindex_hom,
    Limits.Sigma.ι_reindex_hom_assoc, Limits.Sigma.ι_map]
  rw [reassoc_of% canonicalSummandIso_naturality R d f g n a i]
  dsimp only [diagonalMap, diagonalTerm, diagonalEquiv, kunnethModuleTensorHomology]
  rw [← Category.assoc, ← Functor.map_comp, ← tensorHom_def, Category.assoc]
  rfl

/-- The finite convolution graded formula after taking ordinary cohomology.
Source: Stacks Project, Tag 0H7Z, the graded cohomology calculation before Tor.
(blueprint: lem-kun-canonical-graded-cohomology).

Proof. For fixed C,D,a choose a finite support s from d.finite_support. Apply H^n
to d.graded and use preservation of finite biproducts. Its summand at r is
H^n(gr^r(T C) tensor gr^(a-r)(T D)). Apply the components of d.eTgr in both
factors, then the tensor-shift isomorphism, and the cohomology-shift isomorphism.
This identifies the summand with H^{n+a}(single(H^-r C) tensor
single(H^-(a-r) D)). The map r to (-r,-(a-r)) is a bijection onto the diagonal
of sum -a. The same summands vanish outside s since the original derived tensor
summands are zero; hence the finite coproduct identifies with the full coproduct.
For maps enlarge the two supports to their union. The equations d.graded_extension
make both comparisons agree with their enlargement, and d.graded_naturality gives
the map on the common support. Tensor shifts and homology shifts are natural, so
the summand map is the product of the two cohomology maps, as asserted. The zero
support gives zero on both sides and includes zero factors and the zero ring. -/
theorem kunnethCanonicalGradedCohomology (d : CanonicalTensorLocalizationData R) :
    let P (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) : ModuleCat.{u} R :=
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((kunnethModuleTensorHomology R p).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
    let m (p q : ℤ) {C C' D D' : Bounded (ModuleCat.{u} R)}
        (f : C ⟶ C') (g : D ⟶ D') : P p q C D ⟶ P p q C' D' :=
      Limits.Sigma.map fun ij ↦
        ((kunnethModuleTensorHomology R p).map
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
          ((kunnethModuleTensorHomology R p).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)
    ∃ eGr : ∀ (C D : Bounded (ModuleCat.{u} R)) (n a : ℤ),
        (homologyFunctor (ModuleCat.{u} R) n).obj
            ((d.gr a).obj ((d.star.obj (d.T.obj C)).obj (d.T.obj D))) ≅
          P (n + a) (-a) C D,
      ∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D') (n a : ℤ),
        (homologyFunctor (ModuleCat.{u} R) n).map
              ((d.gr a).map ((d.star.map (d.T.map f)).app (d.T.obj D) ≫
                (d.star.obj (d.T.obj C')).map (d.T.map g))) ≫
            (eGr C' D' n a).hom =
          (eGr C D n a).hom ≫ m (n + a) (-a) f g := by
  classical
  dsimp only
  refine ⟨fun C D n a ↦
    gradedCoproductIso R d (d.T.obj C) (d.T.obj D) n a ≪≫
      canonicalCoproductIso R d C D n a, ?_⟩
  intro C C' D D' f g n a
  have h := gradedCoproductIso_naturality R d (d.T.map f) (d.T.map g) n a
  have h' : (homologyFunctor (ModuleCat.{u} R) n).map
        ((d.gr a).map ((d.star.map (d.T.map f)).app (d.T.obj D) ≫
          (d.star.obj (d.T.obj C')).map (d.T.map g))) ≫
      (gradedCoproductIso R d (d.T.obj C') (d.T.obj D') n a).hom =
    (gradedCoproductIso R d (d.T.obj C) (d.T.obj D) n a).hom ≫
      Limits.Sigma.map (fun i : ℤ ↦ (homologyFunctor (ModuleCat.{u} R) n).map
        ((d.gr i).map (d.T.map f) ⊗ₘ (d.gr (a - i)).map (d.T.map g))) := by
    apply (cancel_epi
      (gradedCoproductIso R d (d.T.obj C) (d.T.obj D) n a).inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using congrArg
        (fun z ↦ z ≫ (gradedCoproductIso R d (d.T.obj C') (d.T.obj D') n a).hom) h
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, h', Category.assoc, canonicalCoproductIso_naturality]
  simp only [Category.assoc]
  rfl

end DerivedCategory
