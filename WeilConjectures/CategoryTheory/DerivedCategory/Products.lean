/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts

/-!
# Products in the derived category

Let `C` be an abelian category with K-injective resolutions in which products of shape `β` exist
and are exact. We show that a product of cochain complexes (which is computed degreewise) is also
a product in the derived category (`DerivedCategory.isLimitFanMkQObj`).

We choose K-injective resolutions `K j ⟶ I j`. A product of K-injective complexes is K-injective
(`CochainComplex.isKInjective_of_isLimitFan`), and is a product in the derived category
(`DerivedCategory.isLimitFanMkQObjOfIsKInjective`). As homology commutes with exact products,
the product of the resolutions `∏ K j ⟶ ∏ I j` is a quasi-isomorphism.

## Main statements

- `CochainComplex.isKInjective_of_isLimitFan`: a product of K-injective complexes is
  K-injective.
- `DerivedCategory.isLimitFanMkQObj`: products of cochain complexes are products in the derived
  category when products are exact.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {β : Type*} {X Y : β → C}

/-- A fan over `X` is a limit if it is isomorphic to a limit fan over a family `Y` isomorphic
to `X`. -/
noncomputable def Fan.IsLimit.ofIsos {s : Fan X} {t : Fan Y} (ht : IsLimit t)
    (e : ∀ j, X j ≅ Y j) (a : s.pt ≅ t.pt) (w : ∀ j, a.hom ≫ t.proj j = s.proj j ≫ (e j).hom) :
    IsLimit s :=
  have w' (j : β) : a.inv ≫ s.proj j = t.proj j ≫ (e j).inv := by
    rw [← cancel_epi a.hom, Iso.hom_inv_id_assoc, reassoc_of% (w j), Iso.hom_inv_id, comp_id]
  Fan.IsLimit.mk _ (fun u ↦ Fan.IsLimit.lift ht (fun j ↦ u.proj j ≫ (e j).hom) ≫ a.inv)
    (fun u j ↦ by simp [w'])
    (fun u m hm ↦ by
      rw [← cancel_mono a.hom, assoc, Iso.inv_hom_id, comp_id]
      exact Fan.IsLimit.hom_ext ht _ _ fun j ↦ by simp [w, reassoc_of% (hm j)])

/-- A morphism between the points of limit fans over isomorphic families which is compatible
with the projections is an isomorphism. -/
lemma Fan.IsLimit.isIso_of_isos {s : Fan X} {t : Fan Y} (hs : IsLimit s) (ht : IsLimit t)
    (e : ∀ j, X j ≅ Y j) (f : s.pt ⟶ t.pt) (w : ∀ j, f ≫ t.proj j = s.proj j ≫ (e j).hom) :
    IsIso f :=
  ⟨Fan.IsLimit.lift hs fun j ↦ t.proj j ≫ (e j).inv,
    Fan.IsLimit.hom_ext hs _ _ fun j ↦ by simp [reassoc_of% (w j)],
    Fan.IsLimit.hom_ext ht _ _ fun j ↦ by simp [w]⟩

end CategoryTheory.Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A product of K-injective cochain complexes is K-injective. -/
lemma isKInjective_of_isLimitFan {β : Type*} {I : β → CochainComplex C ℤ}
    [∀ j, (I j).IsKInjective] {t : Fan I} (ht : IsLimit t) : t.pt.IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal]
  intro A f hA
  refine Fan.IsLimit.hom_ext (HomotopyCategory.isLimitFanQuotient ht) _ _ fun j ↦ ?_
  rw [zero_comp]
  exact IsKInjective.rightOrthogonal (I j) _ hA

end CochainComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] {β : Type*}

/-- A product of K-injective cochain complexes is a product in the derived category. -/
noncomputable def isLimitFanMkQObjOfIsKInjective {I : β → CochainComplex C ℤ}
    [∀ j, (I j).IsKInjective] {t : Fan I} (ht : IsLimit t) :
    IsLimit (Fan.mk (Q.obj t.pt) fun j ↦ Q.map (t.proj j)) := by
  have := CochainComplex.isKInjective_of_isLimitFan ht
  refine Fan.IsLimit.ofBijective _ fun Y ↦ ?_
  refine Fan.bijective_of_iso _ (Q.objObjPreimageIso Y) ?_
  have h := Fan.IsLimit.bijective (HomotopyCategory.isLimitFanQuotient ht)
    ((HomotopyCategory.quotient C (.up ℤ)).obj (Q.objPreimage Y))
  have : (fun (g : Q.obj (Q.objPreimage Y) ⟶ Q.obj t.pt) (j : β) ↦ g ≫ Q.map (t.proj j)) =
      (Equiv.piCongrRight fun j ↦ homEquivOfIsKInjective (Q.objPreimage Y) (I j)) ∘
        (fun g (j : β) ↦ g ≫ (HomotopyCategory.quotient C (.up ℤ)).map (t.proj j)) ∘
          (homEquivOfIsKInjective (Q.objPreimage Y) t.pt).symm := by
    ext g j
    simp [homEquivOfIsKInjective_comp_quotient_map]
  exact this ▸ (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

variable [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete β) C]
  [HasExactLimitsOfShape (Discrete β) C]

/-- If `C` has K-injective resolutions and products of shape `β` in `C` are exact, a product of
cochain complexes (which is computed degreewise) is also a product in the derived category. -/
noncomputable def isLimitFanMkQObj {K : β → CochainComplex C ℤ} {s : Fan K} (hs : IsLimit s) :
    IsLimit (Fan.mk (Q.obj s.pt) fun j ↦ Q.map (s.proj j)) := by
  choose I hI i _ hi using fun j ↦ Abelian.HasKInjectiveResolutions.exists_isKInjective (K j)
  let φ : s.pt ⟶ ∏ᶜ I := Pi.lift fun j ↦ s.proj j ≫ i j
  have hφ : QuasiIso φ := ⟨fun n ↦ (quasiIsoAt_iff_isIso_homologyMap φ n).2
    (Fan.IsLimit.isIso_of_isos (HomologicalComplex.isLimitFanHomology hs n)
      (HomologicalComplex.isLimitFanHomology (productIsProduct I) n)
      (fun j ↦ asIso (HomologicalComplex.homologyMap (i j) n)) _
      (fun j ↦ by simp [φ, ← HomologicalComplex.homologyMap_comp]))⟩
  exact Fan.IsLimit.ofIsos (isLimitFanMkQObjOfIsKInjective (productIsProduct I))
    (fun j ↦ asIso (Q.map (i j))) (asIso (Q.map φ))
    (fun j ↦ by simp only [asIso_hom, fan_mk_proj, ← Functor.map_comp, φ, Pi.lift_π])

end DerivedCategory
