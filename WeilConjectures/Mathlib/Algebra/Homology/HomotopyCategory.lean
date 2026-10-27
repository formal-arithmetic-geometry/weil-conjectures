/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The functor induced on homotopy categories by the identity functor

The functor `(𝟭 V).mapHomotopyCategory c` induced on homotopy categories by the identity
functor of a preadditive category `V` is isomorphic to the identity functor
(`CategoryTheory.Functor.mapHomotopyCategoryIdIso`). This is the homotopy category
counterpart of Mathlib's `CategoryTheory.Functor.mapHomologicalComplexIdIso`.

Both this isomorphism and Mathlib's `CategoryTheory.Functor.mapHomotopyCategoryCompIso`
attached to `Iso.refl (F ⋙ G)` are in fact *identities*
(`CategoryTheory.Functor.mapHomotopyCategoryIdIso_hom_app_eq_id` and
`CategoryTheory.Functor.mapHomotopyCategoryCompIso_refl_hom_app`), since the corresponding
isomorphisms at the level of complexes are identities by definition.

This material is destined for `Mathlib/Algebra/Homology/HomotopyCategory.lean`, next to
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Functor

variable (V : Type u) [Category.{v} V] [Preadditive V] {ι : Type*} (c : ComplexShape ι)

/-- The functor on homotopy categories induced by the identity functor is isomorphic to
the identity functor: the homotopy category counterpart of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`. -/
noncomputable def mapHomotopyCategoryIdIso :
    (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  Quotient.natIsoLift _ ((𝟭 V).mapHomotopyCategoryFactors c ≪≫
    isoWhiskerRight (mapHomologicalComplexIdIso V c) (HomotopyCategory.quotient V c) ≪≫
    (HomotopyCategory.quotient V c).leftUnitor ≪≫
    (HomotopyCategory.quotient V c).rightUnitor.symm)

@[simp]
lemma mapHomotopyCategoryIdIso_hom_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).hom.app K) := by
  simp only [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors,
    Quotient.natIsoLift_hom, Quotient.natTransLift_app, id_obj, Iso.trans_hom,
    isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj, Quotient.lift.isLift_hom,
    whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app, Category.comp_id]
  apply Category.id_comp

@[simp]
lemma mapHomotopyCategoryIdIso_inv_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).inv.app K) := by
  simp [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors]

/-- The isomorphism `Functor.mapHomotopyCategoryIdIso` is the identity: it is induced by
`Functor.mapHomologicalComplexIdIso`, which is the identity by definition. -/
lemma mapHomotopyCategoryIdIso_hom_app_eq_id (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryIdIso V c).hom.app Y = 𝟙 Y := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  rw [mapHomotopyCategoryIdIso_hom_app]
  exact (HomotopyCategory.quotient V c).map_id X

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {V W V' : Type*} [Category V] [Category W] [Category V'] [Preadditive V]
  [Preadditive W] [Preadditive V'] {ι : Type*} (c : ComplexShape ι)

/-- The isomorphism `Functor.mapHomotopyCategoryCompIso` attached to `Iso.refl (F ⋙ G)` is
the identity: it is induced by `Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))`,
which is the identity by definition. -/
lemma mapHomotopyCategoryCompIso_refl_hom_app (F : V ⥤ W) (G : W ⥤ V') [F.Additive]
    [G.Additive] (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app Y = 𝟙 _ := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have h₁ : (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app
      ((HomotopyCategory.quotient V c).obj X) =
      (HomotopyCategory.quotient V' c).map
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app X) := rfl
  have h₂ : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app X = 𝟙 _ := rfl
  rw [h₁, h₂]
  exact (HomotopyCategory.quotient V' c).map_id _

/-- The inverse of the isomorphism `Functor.mapHomotopyCategoryCompIso` attached to
`Iso.refl (F ⋙ G)` is the identity. -/
lemma mapHomotopyCategoryCompIso_refl_inv_app (F : V ⥤ W) (G : W ⥤ V') [F.Additive]
    [G.Additive] (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app Y = 𝟙 _ := by
  rw [← cancel_epi ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app Y),
    Iso.hom_inv_id_app, mapHomotopyCategoryCompIso_refl_hom_app]
  exact (Category.comp_id _).symm

end CategoryTheory.Functor

namespace CategoryTheory

variable {ι : Type*} {c : ComplexShape ι}

/-- An isomorphism of additive functors induces an isomorphism of the functors on homotopy
categories. -/
@[simps]
noncomputable def NatIso.mapHomotopyCategory {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {F G : V ⥤ W} [hF : F.Additive] [hG : G.Additive] (e : F ≅ G)
    (c : ComplexShape ι) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
    NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
    NatTrans.mapHomotopyCategory_id]

section Square

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Preadditive A] [Preadditive B] [Preadditive A'] [Preadditive B']
  {T : A ⥤ A} {E : A ⥤ B} {gA : A ⥤ A'} {gB : B ⥤ B'} {T' : A' ⥤ A'} {E' : A' ⥤ B'}
  [T.Additive] [E.Additive] [gA.Additive] [gB.Additive] [T'.Additive] [E'.Additive]

/-- `NatTrans.mapHomotopyCategory` carries a square of natural transformations that commutes
objectwise to the corresponding square on homotopy categories: if for every object `P`
```
gB (E (T P)) ──gB (p P)──▶ gB (E P)
     │                         │
  σ (T P)                     σ P
     ▼                         ▼
E' (gA (T P)) ──E' (τ P)──▶ E' (T' (gA P)) ──p' (gA P)──▶ E' (gA P)
```
commutes, then so does the induced square on homotopy categories, where the composite functors
are identified through `Functor.mapHomotopyCategoryCompIso`. -/
lemma NatTrans.mapHomotopyCategory_comp_app_eq (p : T ⋙ E ⟶ E) (p' : T' ⋙ E' ⟶ E')
    (σ : E ⋙ gB ⟶ gA ⋙ E') (τ : T ⋙ gA ⟶ gA ⋙ T')
    (h : ∀ P, gB.map (p.app P) ≫ σ.app P = σ.app (T.obj P) ≫ E'.map (τ.app P) ≫ p'.app (gA.obj P))
    (K : HomotopyCategory A c) :
    (gB.mapHomotopyCategory c).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ E)) c).hom.app K ≫
          (NatTrans.mapHomotopyCategory p c).app K) ≫
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ gB)) c).hom ≫
        NatTrans.mapHomotopyCategory σ c ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (gA ⋙ E')) c).inv).app K =
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ gB)) c).hom ≫
        NatTrans.mapHomotopyCategory σ c ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (gA ⋙ E')) c).inv).app
        ((T.mapHomotopyCategory c).obj K) ≫
      (E'.mapHomotopyCategory c).map
        (((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ gA)) c).hom ≫
          NatTrans.mapHomotopyCategory τ c ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (gA ⋙ T')) c).inv).app K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (T' ⋙ E')) c).hom.app
        ((gA.mapHomotopyCategory c).obj K) ≫
      (NatTrans.mapHomotopyCategory p' c).app ((gA.mapHomotopyCategory c).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp, Category.comp_id,
    NatTrans.mapHomotopyCategory, HomotopyCategory.quotient_obj_as,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f]
  -- the identity sits at an object that is only defeq to the source of the composition
  erw [Category.id_comp]
  exact h (K.X n)

end Square

section Lift

variable {V W : Type*} [Category V] [Category W] [Preadditive V] [Preadditive W]

/-- Let `e' : E ⋙ q ⟶ p ⋙ E` on homotopy categories be induced by `e : E ⋙ q ⟶ p ⋙ E`
degreewise. If `e` is compatible with `α : p ⟶ 𝟭` and `β : q ⟶ 𝟭`, so is `e'`: the triangle
```
q (E K) ──e' K──▶ E (p K)
     ╲                │
   β (E K)          E (α K)
        ╲             ▼
         ╰──────────▶ E K
```
commutes on homotopy categories. -/
lemma NatTrans.app_comp_map_mapHomotopyCategory_app {E : V ⥤ W} {p : V ⥤ V} {q : W ⥤ W}
    [E.Additive] [p.Additive] [q.Additive] (e : E ⋙ q ⟶ p ⋙ E)
    (e' : E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c)
    (he' : ∀ C, e'.app ((HomotopyCategory.quotient V c).obj C) =
      (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (α : p ⟶ 𝟭 V) (β : q ⟶ 𝟭 W) (h : ∀ F, e.app F ≫ E.map (α.app F) = β.app (E.obj F))
    (K : HomotopyCategory V c) :
    e'.app K ≫ (E.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory α c).app K) =
      (NatTrans.mapHomotopyCategory β c).app ((E.mapHomotopyCategory c).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [he']
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (C.X n)

/-- Let `e`, `e₁` and `e₁₂` be transformations `E ⋙ q ⟶ p ⋙ E'` inducing `e'`, `e₁'` and `e₁₂'`
on homotopy categories degreewise. If they are compatible with `γR : p₁₂ ⟶ p ⋙ p₁` and
`γS : q₁₂ ⟶ q ⋙ q₁`, so are the induced transformations: the pentagon
```
q₁₂ (EY K) ──e₁₂' K──▶ ET (p₁₂ K)
     │                       │
  γS (EY K)              ET (γR K)
     ▼                       ▼
q₁ (q (EY K)) ──q₁ (e' K)──▶ q₁ (EZ (p K)) ──e₁' (p K)──▶ ET (p₁ (p K))
```
commutes on homotopy categories. -/
lemma NatTrans.app_comp_map_mapHomotopyCategory_app_eq_comp {VY VZ VT WY WZ WT : Type*}
    [Category VY] [Category VZ] [Category VT] [Category WY] [Category WZ] [Category WT]
    [Preadditive VY] [Preadditive VZ] [Preadditive VT] [Preadditive WY] [Preadditive WZ]
    [Preadditive WT] {EY : VY ⥤ WY} {EZ : VZ ⥤ WZ} {ET : VT ⥤ WT} {p : VY ⥤ VZ}
    {p₁ : VZ ⥤ VT} {p₁₂ : VY ⥤ VT} {q : WY ⥤ WZ} {q₁ : WZ ⥤ WT} {q₁₂ : WY ⥤ WT}
    [EY.Additive] [EZ.Additive] [ET.Additive] [p.Additive] [p₁.Additive] [p₁₂.Additive]
    [q.Additive] [q₁.Additive] [q₁₂.Additive]
    (e : EY ⋙ q ⟶ p ⋙ EZ) (e₁ : EZ ⋙ q₁ ⟶ p₁ ⋙ ET) (e₁₂ : EY ⋙ q₁₂ ⟶ p₁₂ ⋙ ET)
    (e' : EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c)
    (e₁' : EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (e₁₂' : EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⟶
      p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (he' : ∀ C, e'.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WZ c).map ((NatTrans.mapHomologicalComplex e c).app C))
    (he₁' : ∀ C, e₁'.app ((p.mapHomotopyCategory c).obj ((HomotopyCategory.quotient VY c).obj C)) =
      (HomotopyCategory.quotient WT c).map
        ((NatTrans.mapHomologicalComplex e₁ c).app ((p.mapHomologicalComplex c).obj C)))
    (he₁₂' : ∀ C, e₁₂'.app ((HomotopyCategory.quotient VY c).obj C) =
      (HomotopyCategory.quotient WT c).map ((NatTrans.mapHomologicalComplex e₁₂ c).app C))
    (γR : p₁₂ ⟶ p ⋙ p₁) (γS : q₁₂ ⟶ q ⋙ q₁)
    (h : ∀ F, e₁₂.app F ≫ ET.map (γR.app F) =
      γS.app (EY.obj F) ≫ q₁.map (e.app F) ≫ e₁.app (p.obj F))
    (K : HomotopyCategory VY c) :
    e₁₂'.app K ≫ (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR c).app K) =
      (NatTrans.mapHomotopyCategory γS c).app ((EY.mapHomotopyCategory c).obj K) ≫
        (q₁.mapHomotopyCategory c).map (e'.app K) ≫
        e₁'.app ((p.mapHomotopyCategory c).obj K) := by
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [he₁₂', he', he₁']
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_obj_as, ← Functor.map_comp]
  congr 1
  ext n : 2
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (C.X n)

end Lift

end CategoryTheory
