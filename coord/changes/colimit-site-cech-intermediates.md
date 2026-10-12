# colimitSite_cech_complex_transport and colimitSite_cech_complex_colimit

## Reason
Split the original Cech comparison into strict transport and colimit-cocone sub-conclusions.
The final comparison isomorphism is proved directly with Mathlib from the colimit witness.
Existing public statements and definitions are unchanged. New lemmas get their own modules;
the item's imports of them are private to its proof.

## Old
No declarations named `CategoryTheory.colimitSite_cech_complex_transport` or
`CategoryTheory.colimitSite_cech_complex_colimit` existed in the library.
The existing `CategoryTheory.colimitSite_cech_complex_isIso` signature is unchanged verbatim.

## New
The two new signatures, verbatim, are:

```lean
theorem colimitSite_cech_complex_transport
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) {T : Type u} [Finite T] {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
      Presieve.ofArrows f hom ∈ P i U →
    ∀ S : SiteCechComplex f hom,
      (∀ a : Under i,
        Presieve.ofArrows (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
          (fun t ↦ (F.map a.hom).toFunctor.map (hom t)) ∈
            P a.right ((F.map a.hom).toFunctor.obj U) ∧
        ∃ Sa : SiteCechComplex (fun t ↦ (F.map a.hom).toFunctor.obj (f t))
            (fun t ↦ (F.map a.hom).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (F.map a.hom).toFunctor.obj (S.W p t) ≅ Sa.W p t,
              ∀ k, e.hom ≫ Sa.pr p t k = (F.map a.hom).toFunctor.map (S.pr p t k)) ∧
      (Presieve.ofArrows (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
          (fun t ↦ (V.ι.app i).toFunctor.map (hom t)) ∈
            Q ((V.ι.app i).toFunctor.obj U) ∧
        ∃ Sc : SiteCechComplex (fun t ↦ (V.ι.app i).toFunctor.obj (f t))
            (fun t ↦ (V.ι.app i).toFunctor.map (hom t)),
          ∀ (p : ℕ) (t : Fin (p + 1) → T),
            ∃ e : (V.ι.app i).toFunctor.obj (S.W p t) ≅ Sc.W p t,
              ∀ k, e.hom ≫ Sc.pr p t k = (V.ι.app i).toFunctor.map (S.pr p t k))
```

```lean
theorem colimitSite_cech_complex_colimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (P : ∀ j, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderComposition]
    [∀ j, (P j).IsStableUnderBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteColimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange] [Q.HasPullbacks]
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    [∀ j, (V.ι.app j).toFunctor.IsContinuous (P j).toGrothendieck Q.toGrothendieck]
    (G : ∀ j, Sheaf (P j).toGrothendieck AddCommGrpCat.{u})
    (θ : ∀ (j k : J) (a : j ⟶ k),
      (G j).obj ⟶ (F.map a).toFunctor.op ⋙ (G k).obj)
    (hθid : ∀ (j : J) (X : F.obj j),
      Arrow.mk ((θ j j (𝟙 j)).app (op X)) = Arrow.mk (𝟙 ((G j).obj.obj (op X))))
    (hθcomp : ∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l) (X : F.obj j),
      Arrow.mk ((θ j l (a ≫ b)).app (op X)) =
        Arrow.mk ((θ j k a).app (op X) ≫
          (θ k l b).app (op ((F.map a).toFunctor.obj X))))
    (H : J ⥤ Sheaf Q.toGrothendieck AddCommGrpCat.{u})
    (E : ∀ j, H.obj j ≅
      (sheafPullback (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).obj (G j)) :
    let β := fun (j : J) (X : F.obj j) ↦
      (((sheafAdjunctionContinuous (V.ι.app j).toFunctor AddCommGrpCat.{u}
        (P j).toGrothendieck Q.toGrothendieck).unit.app (G j)).hom.app (op X)) ≫
        (E j).inv.hom.app (op ((V.ι.app j).toFunctor.obj X))
    (∀ (j k : J) (a : j ⟶ k) (X : F.obj j),
      Arrow.mk (β j X ≫ (H.map a).hom.app (op ((V.ι.app j).toFunctor.obj X))) =
        Arrow.mk ((θ j k a).app (op X) ≫ β k ((F.map a).toFunctor.obj X))) →
    ∀ (c : Cocone H), IsColimit c →
    ∀ (i : J) {T : Type u} [Finite T] {U : F.obj i}
      (f : T → F.obj i) (hom : ∀ t, f t ⟶ U),
      Presieve.ofArrows f hom ∈ P i U →
    ∀ S : SiteCechComplex f hom,
      ∃ (D : Under i ⥤ CochainComplex AddCommGrpCat.{u} ℕ)
        (eD : ∀ a : Under i, D.obj a ≅
          S.complex ((F.map a.hom).toFunctor.op ⋙ (G a.right).obj))
        (K : Cocone D)
        (eK : K.pt ≅ S.complex ((V.ι.app i).toFunctor.op ⋙ c.pt.obj)),
        (∀ (a a' : Under i) (b : a ⟶ a') (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (D.map b).f p ≫ (eD a').hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            (θ a.right a'.right b.right).app
              (op ((F.map a.hom).toFunctor.obj (S.W p t))))) ∧
        (∀ (a : Under i) (p : ℕ) (t : Fin (p + 1) → T),
          Arrow.mk ((eD a).inv.f p ≫ (K.ι.app a).f p ≫ eK.hom.f p ≫
            AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)) =
          Arrow.mk (AddCommGrpCat.ofHom (Pi.evalAddMonoidHom
            (fun t ↦ (G a.right).obj.obj
              (op ((F.map a.hom).toFunctor.obj (S.W p t)))) t) ≫
            β a.right ((F.map a.hom).toFunctor.obj (S.W p t)) ≫
            (c.ι.app a.right).hom.app
              (op ((V.ι.app a.right).toFunctor.obj
                ((F.map a.hom).toFunctor.obj (S.W p t)))))) ∧
        Nonempty (IsColimit K)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ColimitSiteCechComplex | F2 | proof uses both new lemmas; unchanged signature |

The new names have no existing downstream users. Existing users of the main theorem,
`Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent` and
`Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing`, see the identical statement.
No target definition changes and no target statement review is reopened.

## Status
landed 20261012T053930-L-2634602 2026-10-12 (merge of deliver/F2/Sheaf.CategoryTheory.ColimitSiteCechComplex)
