/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Natural isomorphisms out of a derived category, from K-injective complexes

Let `C` be an abelian category with K-injective resolutions. Every object of `D(C)` is
isomorphic to `Q(I)` for a K-injective complex `I`, and every morphism `Q(I) ⟶ Q(I')` between
K-injective complexes is the image of a morphism of complexes. Hence two functors
`Φ Ψ : D(C) ⥤ E` are isomorphic as soon as their values on the objects `Q(I)`, `I` K-injective,
are isomorphic compatibly with the morphisms of complexes between K-injective complexes
(`DerivedCategory.isoOfKInjective`).
-/

@[expose] public section

open CategoryTheory Abelian

namespace DerivedCategory

variable {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] [Category E] (Φ Ψ : DerivedCategory C ⥤ E)

/-- A natural isomorphism `Φ ≅ Ψ` of functors out of `D(C)` from isomorphisms
`Φ(Q(I)) ≅ Ψ(Q(I))` for the K-injective complexes `I`, natural with respect to the morphisms of
complexes between K-injective complexes. -/
noncomputable def isoOfKInjective
    (e : ∀ (I : CochainComplex C ℤ) [I.IsKInjective], Φ.obj (Q.obj I) ≅ Ψ.obj (Q.obj I))
    (he : ∀ (I I' : CochainComplex C ℤ) [I.IsKInjective] [I'.IsKInjective] (g : I ⟶ I'),
      Φ.map (Q.map g) ≫ (e I').hom = (e I).hom ≫ Ψ.map (Q.map g)) :
    Φ ≅ Ψ :=
  NatIso.ofComponents
    (fun L ↦ Φ.mapIso (kInjectiveRepIso L) ≪≫ e (kInjectiveRep L) ≪≫
      Ψ.mapIso (kInjectiveRepIso L).symm)
    (fun {L L'} f ↦ by
      obtain ⟨g, hg⟩ := CochainComplex.IsKInjective.exists_Q_map_eq (kInjectiveRep L)
        (kInjectiveRep L') ((kInjectiveRepIso L).inv ≫ f ≫ (kInjectiveRepIso L').hom)
      have hf : f = (kInjectiveRepIso L).hom ≫ Q.map g ≫ (kInjectiveRepIso L').inv := by
        simp [hg]
      have h := he _ _ g
      subst hf
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Functor.map_comp, ← Functor.map_comp_assoc Φ (kInjectiveRepIso L').inv,
        Iso.inv_hom_id, ← Functor.map_comp_assoc Ψ (kInjectiveRepIso L).inv]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h])

end DerivedCategory
