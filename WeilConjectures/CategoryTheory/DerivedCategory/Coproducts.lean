/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Coproducts in the derived category

Let `C` be an abelian category with K-injective resolutions. We show that a coproduct of
cochain complexes (which is computed degreewise) is also a coproduct in the derived category
(`DerivedCategory.isColimitCofanMkQObj`). No exactness of coproducts is needed: for a K-injective
complex `I`, morphisms `Q.obj X ⟶ Q.obj I` in the derived category are homotopy classes of
morphisms `X ⟶ I` (`DerivedCategory.homEquivOfIsKInjective`), and homotopy classes of morphisms
out of a coproduct are families of homotopy classes of morphisms out of the summands
(`HomotopyCategory.isColimitCofanQuotient`).

## Main definitions and statements

- `CategoryTheory.Limits.Cofan.IsColimit.ofBijective`,
  `CategoryTheory.Limits.Fan.IsLimit.ofBijective`:
  (co)fans are (co)limits as soon as the induced maps on morphisms are bijective.
- `DerivedCategory.homEquivOfIsKInjective`: morphisms `Q.obj K ⟶ Q.obj L` for `L` K-injective
  are morphisms in the homotopy category.
- `DerivedCategory.isColimitCofanMkQObj`: coproducts of cochain complexes are coproducts in the
  derived category.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {β : Type*} {X : β → C}

/-- A cofan `s` is a colimit if for any object `Y`, the precomposition with the coprojections
induces a bijection `(s.pt ⟶ Y) → ∀ j, (X j ⟶ Y)`. -/
noncomputable def Cofan.IsColimit.ofBijective (s : Cofan X)
    (h : ∀ Y, Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) : IsColimit s :=
  Cofan.IsColimit.mk s (fun t ↦ (Equiv.ofBijective _ (h t.pt)).symm t.inj)
    (fun t j ↦ congrFun ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.inj) j)
    (fun t _ hm ↦ (h t.pt).1
      ((funext hm).trans ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.inj).symm))

/-- A fan `s` is a limit if for any object `Y`, the composition with the projections
induces a bijection `(Y ⟶ s.pt) → ∀ j, (Y ⟶ X j)`. -/
noncomputable def Fan.IsLimit.ofBijective (s : Fan X)
    (h : ∀ Y, Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) : IsLimit s :=
  Fan.IsLimit.mk s (fun t ↦ (Equiv.ofBijective _ (h t.pt)).symm t.proj)
    (fun t j ↦ congrFun ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.proj) j)
    (fun t _ hm ↦ (h t.pt).1
      ((funext hm).trans ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.proj).symm))

lemma Cofan.IsColimit.bijective {s : Cofan X} (hs : IsColimit s) (Y : C) :
    Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g :=
  ⟨fun _ _ h ↦ Cofan.IsColimit.hom_ext hs _ _ (congrFun h),
    fun f ↦ ⟨Cofan.IsColimit.desc hs f, funext (Cofan.IsColimit.fac hs f)⟩⟩

lemma Fan.IsLimit.bijective {s : Fan X} (hs : IsLimit s) (Y : C) :
    Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j :=
  ⟨fun _ _ h ↦ Fan.IsLimit.hom_ext hs _ _ (congrFun h),
    fun f ↦ ⟨Fan.IsLimit.lift hs f, funext (Fan.IsLimit.fac hs f)⟩⟩

/-- The bijectivity condition of `Cofan.IsColimit.ofBijective` is invariant under isomorphisms
of the target. -/
lemma Cofan.bijective_of_iso (s : Cofan X) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) :
    Function.Bijective fun (g : s.pt ⟶ Y') (j : β) ↦ s.inj j ≫ g := by
  have : (fun (g : s.pt ⟶ Y') (j : β) ↦ s.inj j ≫ g) =
      (Equiv.piCongrRight fun j ↦ (Iso.refl (X j)).homCongr e) ∘
        (fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) ∘ ((Iso.refl s.pt).homCongr e).symm := by
    ext g j
    simp
  rw [this]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

/-- The bijectivity condition of `Fan.IsLimit.ofBijective` is invariant under isomorphisms
of the source. -/
lemma Fan.bijective_of_iso (s : Fan X) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) :
    Function.Bijective fun (g : Y' ⟶ s.pt) (j : β) ↦ g ≫ s.proj j := by
  have : (fun (g : Y' ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) =
      (Equiv.piCongrRight fun j ↦ e.homCongr (Iso.refl (X j))) ∘
        (fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) ∘ (e.homCongr (Iso.refl s.pt)).symm := by
    ext g j
    simp
  rw [this]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

end CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- For a K-injective complex `L`, morphisms `Q.obj K ⟶ Q.obj L` in the derived category
identify with morphisms in the homotopy category. -/
noncomputable def homEquivOfIsKInjective (K L : CochainComplex C ℤ) [L.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃
      (Q.obj K ⟶ Q.obj L) :=
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective _ L)).trans
    (Iso.homCongr ((quotientCompQhIso C).app K) ((quotientCompQhIso C).app L))

@[simp]
lemma homEquivOfIsKInjective_quotient_map {K L : CochainComplex C ℤ} [L.IsKInjective]
    (f : K ⟶ L) :
    homEquivOfIsKInjective K L ((HomotopyCategory.quotient C (.up ℤ)).map f) = Q.map f := by
  simp [homEquivOfIsKInjective]

lemma homEquivOfIsKInjective_quotient_map_comp {K K' L : CochainComplex C ℤ} [L.IsKInjective]
    (u : K' ⟶ K) (g : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) :
    homEquivOfIsKInjective K' L ((HomotopyCategory.quotient C (.up ℤ)).map u ≫ g) =
      Q.map u ≫ homEquivOfIsKInjective K L g := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  rw [← Functor.map_comp, homEquivOfIsKInjective_quotient_map,
    homEquivOfIsKInjective_quotient_map, Functor.map_comp]

lemma homEquivOfIsKInjective_comp_quotient_map {K L L' : CochainComplex C ℤ} [L.IsKInjective]
    [L'.IsKInjective] (g : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) (v : L ⟶ L') :
    homEquivOfIsKInjective K L' (g ≫ (HomotopyCategory.quotient C (.up ℤ)).map v) =
      homEquivOfIsKInjective K L g ≫ Q.map v := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  rw [← Functor.map_comp, homEquivOfIsKInjective_quotient_map,
    homEquivOfIsKInjective_quotient_map, Functor.map_comp]

variable [Abelian.HasKInjectiveResolutions C]

/-- If `C` has K-injective resolutions, a coproduct of cochain complexes (which is computed
degreewise) is also a coproduct in the derived category. -/
noncomputable def isColimitCofanMkQObj {β : Type*} {K : β → CochainComplex C ℤ} {s : Cofan K}
    (hs : IsColimit s) : IsColimit (Cofan.mk (Q.obj s.pt) fun j ↦ Q.map (s.inj j)) := by
  refine Cofan.IsColimit.ofBijective _ fun Y ↦ ?_
  obtain ⟨I, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isKInjective Y
  refine Cofan.bijective_of_iso _ e.symm ?_
  have h := Cofan.IsColimit.bijective (HomotopyCategory.isColimitCofanQuotient hs)
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  have : (fun (g : Q.obj s.pt ⟶ Q.obj I) (j : β) ↦ Q.map (s.inj j) ≫ g) =
      (Equiv.piCongrRight fun j ↦ homEquivOfIsKInjective (K j) I) ∘
        (fun g (j : β) ↦ (HomotopyCategory.quotient C (.up ℤ)).map (s.inj j) ≫ g) ∘
          (homEquivOfIsKInjective s.pt I).symm := by
    ext g j
    simp [homEquivOfIsKInjective_quotient_map_comp]
  exact this ▸ (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

end DerivedCategory
