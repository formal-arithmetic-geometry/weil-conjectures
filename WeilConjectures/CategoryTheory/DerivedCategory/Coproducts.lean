/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
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

- `DerivedCategory.homEquivOfIsKInjective`: morphisms `Q.obj K ⟶ Q.obj L` for `L` K-injective
  are morphisms in the homotopy category.
- `DerivedCategory.isColimitCofanMkQObj`: coproducts of cochain complexes are coproducts in the
  derived category.
-/

@[expose] public section

open CategoryTheory Limits Category

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
