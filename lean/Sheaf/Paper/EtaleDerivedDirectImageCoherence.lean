/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NA
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Normalized composition of bounded-below étale direct images

Source: Stacks Project, sites-cohomology.tex, Tag 0D6E,
lemma-derived-pushforward-composition; bounded-below constant-coefficient specialization
(blueprint: lem-cbc-etale-derived-direct-image-coherence).

The comparison is oriented from the composite pushforward to the iterated pushforward.
Named composite morphisms avoid hiding scheme-category associators and identity equalities.
The categories are the bounded-below subcategories of `Etale.DerivedCategoryModule`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma compositor_inv_fac
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) (I : HomotopyCategory.Plus C) :
    H.rightDerivedFunctorPlusUnit.app I ≫
        (Functor.rightDerivedFunctorPlusCompIso' F G e).inv.app
          (DerivedCategory.Plus.Qh.obj I) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.inv).app I) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj I) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app I) := by
  rw [← cancel_mono ((Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app
    (DerivedCategory.Plus.Qh.obj I))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have h := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F G e) I
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  have hQ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus e.inv).app I) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app I) =
        𝟙 _ := by
    rw [← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      DerivedCategory.Plus.Qh.map_id]
  calc
    _ = H.rightDerivedFunctorPlusUnit.app I := Category.comp_id _
    _ = DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus e.inv).app I) ≫
        (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus e.hom).app I) ≫
            H.rightDerivedFunctorPlusUnit.app I) := by
      rw [← Category.assoc, hQ, Category.id_comp]
    _ = _ := by
      rw [← h, Functor.rightDerivedFunctorPlusCompUnit_app]
      simp only [Category.assoc]


private lemma natTrans_ext_injectives
    {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C]
    {F G : DerivedCategory.Plus C ⥤ D} (c c' : F ⟶ G)
    (hc : ∀ I : HomotopyCategory.Plus C, (∀ n : ℤ, Injective (I.obj.as.X n)) →
      c.app (DerivedCategory.Plus.Qh.obj I) = c'.app (DerivedCategory.Plus.Qh.obj I)) :
    c = c' := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff K n).mp hn
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := (HomotopyCategory.Plus.quotient _).obj
    ((InjectiveObject.ι _).mapCochainComplexPlus.obj L)
  have hI (n : ℤ) : Injective (I.obj.as.X n) := by
    dsimp [I]
    infer_instance
  change DerivedCategory.Plus.Qh.obj I ≅ K at e
  rw [← cancel_epi (F.map e.hom), c.naturality, c'.naturality, hc I hI]

private lemma compositor_inv_unit_right
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [EnoughInjectives D]
    (F : C ⥤ D) (G : D ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ F) (u : G ≅ 𝟭 D)
    (E : G.rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus D))
    (he : e.hom = Functor.whiskerLeft F u.hom ≫ F.rightUnitor.hom)
    (hE : ∀ I : HomotopyCategory.Plus D,
      G.rightDerivedFunctorPlusUnit.app I ≫ E.hom.app (DerivedCategory.Plus.Qh.obj I) =
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus u.hom).app I)) :
    (Functor.rightDerivedFunctorPlusCompIso' F G e).inv ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus E.hom =
      𝟙 F.rightDerivedFunctorPlus := by
  rw [Iso.inv_comp_eq, Category.comp_id]
  symm
  refine Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C)
    _ _ _ ?_
  ext I : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj]
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F G e) I
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hfac
  have hnat : G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app I) ≫
        E.hom.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj I)) =
      E.hom.app (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj I)) ≫
        F.rightDerivedFunctorPlusUnit.app I := E.hom.naturality _
  rw [hfac, Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc, hnat,
    ← Category.assoc, hE]
  congr 1
  rw [he]
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    NatTrans.mapHomotopyCategoryPlus_rightUnitor_hom_app, Category.comp_id]
  rfl

private theorem normalized_coherence (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    ∃ (d : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (fg : X ⟶ Z) (_w : fg = f ≫ g),
        rightDerivedLowerStarPlus A fg ≅
          rightDerivedLowerStarPlus A f ⋙
            rightDerivedLowerStarPlus A g)
      (e : ∀ T : Scheme.{u},
        rightDerivedLowerStarPlus A (𝟙 T) ≅
          𝟭 (DerivedCategory.Plus (Sheaf T.smallEtaleTopology A))),
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar A fg).rightDerivedFunctorPlusUnit.app I ≫
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
              ((NatTrans.mapHomotopyCategoryPlus
                (lowerStarComp A f g fg w).inv).app I) ≫
            (lowerStar A g).rightDerivedFunctorPlusUnit.app
              ((lowerStar A f).mapHomotopyCategoryPlus.obj I) ≫
            (rightDerivedLowerStarPlus A g).map
              ((lowerStar A f).rightDerivedFunctorPlusUnit.app I)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (c : rightDerivedLowerStarPlus A fg ⟶
            rightDerivedLowerStarPlus A f ⋙
              rightDerivedLowerStarPlus A g),
        (∀ I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
          (∀ n : ℤ, Injective (I.obj.as.X n)) →
          c.app (DerivedCategory.Plus.Qh.obj I) =
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I)) →
        c = (d f g fg w).hom) ∧
      (∀ (T : Scheme.{u})
          (I : HomotopyCategory.Plus (Sheaf T.smallEtaleTopology A)),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar A (𝟙 T)).rightDerivedFunctorPlusUnit.app I ≫
            (e T).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (lowerStarId A T).hom).app I)) ∧
      (∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
        (d (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom ≫
            Functor.whiskerRight (d f g (f ≫ g) rfl).hom
              (rightDerivedLowerStarPlus A h) =
          (d f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus A f)
              (d g h (g ≫ h) rfl).hom) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus A f)
              (e Y).hom = 𝟙 (rightDerivedLowerStarPlus A f)) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d (𝟙 X) f f (Category.id_comp f).symm).hom ≫
            Functor.whiskerRight (e X).hom
              (rightDerivedLowerStarPlus A f) =
          𝟙 (rightDerivedLowerStarPlus A f)) := by
  have {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (lowerStar A f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction A f)
  let d {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (fg : X ⟶ Z) (w : fg = f ≫ g) :=
    (Functor.rightDerivedFunctorPlusCompIso' (lowerStar A f) (lowerStar A g)
      (lowerStarComp A f g fg w)).symm
  refine ⟨@d, lowerStarIdDerivedPlus A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y Z f g fg w I hI
    exact compositor_inv_fac (lowerStar A f) (lowerStar A g) (lowerStar A fg)
      (lowerStarComp A f g fg w) I
  · intro X Y Z f g fg w c hc
    exact natTrans_ext_injectives c (d f g fg w).hom hc
  · intro T I hI
    exact lowerStarIdDerivedPlus_hom_app_fac A T I
  · intro X Y Z W f g h
    have ha := Functor.rightDerivedFunctorPlusCompIso'_assoc
      (lowerStar A f) (lowerStar A g) (lowerStar A h)
      (lowerStar A (f ≫ g)) (lowerStar A (g ≫ h)) (lowerStar A ((f ≫ g) ≫ h))
      (lowerStarComp A f g (f ≫ g) rfl) (lowerStarComp A g h (g ≫ h) rfl)
      (lowerStarComp A (f ≫ g) h ((f ≫ g) ≫ h) rfl)
      (lowerStarComp A f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h))
      (lowerStarComp_assoc' A f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl)
    let c₁ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A f) (lowerStar A g)
      (lowerStarComp A f g (f ≫ g) rfl)
    let c₂ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A g) (lowerStar A h)
      (lowerStarComp A g h (g ≫ h) rfl)
    let c₃ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A (f ≫ g))
      (lowerStar A h) (lowerStarComp A (f ≫ g) h ((f ≫ g) ≫ h) rfl)
    let c₄ := Functor.rightDerivedFunctorPlusCompIso' (lowerStar A f)
      (lowerStar A (g ≫ h))
      (lowerStarComp A f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h))
    have he : Functor.isoWhiskerRight c₁ (lowerStar A h).rightDerivedFunctorPlus ≪≫ c₃ =
        Functor.isoWhiskerLeft (lowerStar A f).rightDerivedFunctorPlus c₂ ≪≫ c₄ :=
      Iso.ext ha
    simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, d, c₁, c₂, c₃, c₄, Iso.symm_hom,
      rightDerivedLowerStarPlus] using congrArg Iso.inv he
  · intro X Y f
    exact compositor_inv_unit_right (lowerStar A f) (lowerStar A (𝟙 Y))
      (lowerStarComp A f (𝟙 Y) f (Category.comp_id f).symm) (lowerStarId A Y)
      (lowerStarIdDerivedPlus A Y)
      (by rw [lowerStarComp_id_right]; rfl) (lowerStarIdDerivedPlus_hom_app_fac A Y)
  · intro X Y f
    have hu := lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' A f
      (lowerStarComp A (𝟙 X) f f (Category.id_comp f).symm) (by
        rw [lowerStarComp_id_left]
        refine NatTrans.ext (funext fun M ↦ ?_)
        simp)
    have he : Functor.isoWhiskerRight (lowerStarIdDerivedPlus A X).symm
          (lowerStar A f).rightDerivedFunctorPlus ≪≫
        Functor.rightDerivedFunctorPlusCompIso' (lowerStar A (𝟙 X)) (lowerStar A f)
          (lowerStarComp A (𝟙 X) f f (Category.id_comp f).symm) =
        (lowerStar A f).rightDerivedFunctorPlus.leftUnitor := by
      apply Iso.ext
      exact hu
    have hi := congrArg Iso.inv he
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv] at hi
    refine NatTrans.ext (funext fun K ↦ ?_)
    simpa only [d, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app, NatTrans.id_app, rightDerivedLowerStarPlus]
      using NatTrans.congr_app hi K


-- Keep the existing named equality witness in the compositor's type.
set_option linter.unusedVariables false in
/-- The canonical normalized compositor, identity comparisons, and their coherence.

Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition
(blueprint: lem-cbc-etale-derived-direct-image-coherence).

Proof plan: (1) construct the underived comparisons from fibre-product associativity and
identity isomorphisms (`lowerStarComp.inv`, `lowerStarId.hom`); restriction makes them linear
and natural. (2) The fibre-product universal property proves their associativity and unit
laws. (3) Exact constant-coefficient inverse image is left adjoint to direct image, so direct
image preserves injectives; additivity preserves the lower bound. (4) On injective complexes
form the normalized compositor by the three derived-unit computation isomorphisms displayed
below. (5) Enough injectives gives an injective representative for every bounded-below
object. The K-injective Hom bijection proves independence of representatives, naturality,
and uniqueness by conjugation. (6) Apply the same construction to the identity comparison.
(7) Expand both associativity paths on an injective representative and cancel the computation
maps; the underived associativity law identifies them. Equivalently use
`rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc` for the inverse canonical comparisons.
(8) Expand each unit composite, cancel the computation maps, and apply the underived unit
law. Naturality and injective representatives extend all equalities to every object.
-/
theorem exists_normalizedDerivedDirectImageCoherence (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (d : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (fg : X ⟶ Z) (w : fg = f ≫ g),
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) fg ≅
          rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
            rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g)
      (e : ∀ T : Scheme.{u},
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (𝟙 T) ≅
          𝟭 (DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))),
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar (ModuleCat.{u + 1} Λ) fg).rightDerivedFunctorPlusUnit.app I ≫
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
              ((NatTrans.mapHomotopyCategoryPlus
                (lowerStarComp (ModuleCat.{u + 1} Λ) f g fg w).inv).app I) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlusUnit.app
              ((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomotopyCategoryPlus.obj I) ≫
            (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
              ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusUnit.app I)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
          (w : fg = f ≫ g)
          (c : rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) fg ⟶
            rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
              rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g),
        (∀ I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (∀ n : ℤ, Injective (I.obj.as.X n)) →
          c.app (DerivedCategory.Plus.Qh.obj I) =
            (d f g fg w).hom.app (DerivedCategory.Plus.Qh.obj I)) →
        c = (d f g fg w).hom) ∧
      (∀ (T : Scheme.{u})
          (I : HomotopyCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        (∀ n : ℤ, Injective (I.obj.as.X n)) →
        (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 T)).rightDerivedFunctorPlusUnit.app I ≫
            (e T).hom.app (DerivedCategory.Plus.Qh.obj I) =
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (lowerStarId (ModuleCat.{u + 1} Λ) T).hom).app I)) ∧
      (∀ {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
        (d (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom ≫
            Functor.whiskerRight (d f g (f ≫ g) rfl).hom
              (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) h) =
          (d f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)
              (d g h (g ≫ h) rfl).hom) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
            Functor.whiskerLeft (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)
              (e Y).hom = 𝟙 (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (d (𝟙 X) f f (Category.id_comp f).symm).hom ≫
            Functor.whiskerRight (e X).hom
              (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f) =
          𝟙 (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f)) := by
  exact normalized_coherence (ModuleCat.{u + 1} Λ)

end AlgebraicGeometry.Etale
