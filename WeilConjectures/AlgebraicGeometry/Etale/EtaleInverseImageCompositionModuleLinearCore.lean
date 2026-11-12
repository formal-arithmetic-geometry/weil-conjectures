/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Linearity of the composition comparisons on constant-ring etale modules

Source: Stacks Project, Modules on Sites, Tags 03D8 and 03D7
(blueprint: lem-weil-pbc-inverse-image-composition-module-linear-core).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry


/-- Compatibility of composite adjunction hom-equivalences with forgetful comparisons.
This is the categorical calculation in step 4 of the module proof. -/
private theorem comp_homEquiv_forget
    {M₁ M₂ M₃ A₁ A₂ A₃ : Type*}
    [Category M₁] [Category M₂] [Category M₃]
    [Category A₁] [Category A₂] [Category A₃]
    (U₁ : M₁ ⥤ A₁) (U₂ : M₂ ⥤ A₂) (U₃ : M₃ ⥤ A₃)
    (L₁ : M₁ ⥤ M₂) (L₂ : M₂ ⥤ M₃) (R₁ : M₂ ⥤ M₁) (R₂ : M₃ ⥤ M₂)
    (l₁ : A₁ ⥤ A₂) (l₂ : A₂ ⥤ A₃) (r₁ : A₂ ⥤ A₁) (r₂ : A₃ ⥤ A₂)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : l₁ ⊣ r₁) (b₂ : l₂ ⊣ r₂)
    (p₁ : R₁ ⋙ U₁ ≅ U₂ ⋙ r₁) (p₂ : R₂ ⋙ U₂ ≅ U₃ ⋙ r₂)
    (e₁ : L₁ ⋙ U₂ ≅ U₁ ⋙ l₁) (e₂ : L₂ ⋙ U₃ ≅ U₂ ⋙ l₂)
    (h₁ : ∀ G F (k : L₁.obj G ⟶ F),
      U₁.map (a₁.homEquiv G F k) ≫ p₁.hom.app F =
      b₁.homEquiv (U₁.obj G) (U₂.obj F) (e₁.inv.app G ≫ U₂.map k))
    (h₂ : ∀ G F (k : L₂.obj G ⟶ F),
      U₂.map (a₂.homEquiv G F k) ≫ p₂.hom.app F =
      b₂.homEquiv (U₂.obj G) (U₃.obj F) (e₂.inv.app G ≫ U₃.map k))
    (G : M₁) (F : M₃) (k : (L₁ ⋙ L₂).obj G ⟶ F) :
    U₁.map ((a₁.comp a₂).homEquiv G F k) ≫ p₁.hom.app (R₂.obj F) ≫
      r₁.map (p₂.hom.app F) =
    (b₁.comp b₂).homEquiv (U₁.obj G) (U₃.obj F)
      (l₂.map (e₁.inv.app G) ≫ e₂.inv.app (L₁.obj G) ≫ U₃.map k) := by
  rw [Adjunction.comp_homEquiv a₁ a₂, Adjunction.comp_homEquiv b₁ b₂]
  simp only [Equiv.trans_apply, Functor.comp_obj]
  rw [← Category.assoc, h₁, ← b₁.homEquiv_naturality_right, Category.assoc, h₂]
  exact congrArg (b₁.homEquiv (U₁.obj G) (r₂.obj (U₃.obj F)))
    (b₂.homEquiv_naturality_left (e₁.inv.app G)
      (e₂.inv.app (L₁.obj G) ≫ U₃.map k)).symm

/-- The unit formula obtained by applying forgetful compatibility to the identity. -/
private theorem unit_forget
    {M N A B : Type*} [Category M] [Category N] [Category A] [Category B]
    (U : M ⥤ A) (V : N ⥤ B) (L : M ⥤ N) (R : N ⥤ M)
    (l : A ⥤ B) (r : B ⥤ A) (a : L ⊣ R) (b : l ⊣ r)
    (p : R ⋙ U ≅ V ⋙ r) (e : L ⋙ V ≅ U ⋙ l)
    (h : ∀ G F (k : L.obj G ⟶ F),
      U.map (a.homEquiv G F k) ≫ p.hom.app F =
      b.homEquiv (U.obj G) (V.obj F) (e.inv.app G ≫ V.map k)) (G : M) :
    U.map (a.unit.app G) ≫ p.hom.app (L.obj G) ≫ r.map (e.hom.app G) =
      b.unit.app (U.obj G) := by
  have hh := h G (L.obj G) (𝟙 _)
  rw [a.homEquiv_id, V.map_id] at hh
  simp only [Functor.comp_obj, Category.comp_id] at hh
  rw [← Category.assoc, hh, b.homEquiv_apply, Category.assoc, ← r.map_comp,
    e.inv_hom_id_app G]
  exact (congrArg (fun k => b.unit.app (U.obj G) ≫ k)
    (r.map_id ((U ⋙ l).obj G))).trans (Category.comp_id _)


/-- Erase the identity comparisons after a strictly commuting forgetful square. -/
private theorem erase_map_id
    {A B : Type*} [Category A] [Category B] (r : B ⥤ A)
    {X : A} (Y : B) (f g : X ⟶ r.obj Y)
    (h : f ≫ 𝟙 (r.obj Y) ≫ r.map (𝟙 Y) = g) : f = g := by
  simpa only [r.map_id, Category.comp_id] using h

private theorem erase_middle_id
    {A : Type*} [Category A] {X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ 𝟙 Y ≫ g = h) : f ≫ g = h := by
  simpa only [Category.id_comp] using w

/-- Pasting a naturality square with a unit comparison. -/
private theorem paste_rectangle
    {A : Type*} [Category A] {X P Q R S : A}
    (a : X ⟶ P) (d : P ⟶ Q) (q : Q ⟶ S) (p : P ⟶ R) (e : R ⟶ S)
    (u : X ⟶ R) (h : p ≫ e = d ≫ q) (hu : a ≫ p = u) :
    (a ≫ d) ≫ q = u ≫ e := by
  rw [Category.assoc, ← h, ← Category.assoc, hu]

/-- Test a comparison after applying an adjunction and cancelling an isomorphism. -/
private theorem compare_by_homEquiv
    {A B : Type*} [Category A] [Category B]
    {l : A ⥤ B} {r : B ⥤ A} (b : l ⊣ r) (G : A)
    {M N S : B} (ec : M ≅ l.obj G) (e : N ≅ S)
    (f : M ⟶ N) (g : l.obj G ⟶ S)
    (h : b.homEquiv G N (ec.inv ≫ f) ≫ r.map e.hom = b.homEquiv G S g) :
    f ≫ e.hom = ec.hom ≫ g := by
  apply (cancel_epi ec.inv).1
  rw [ec.inv_hom_id_assoc]
  apply (b.homEquiv G S).injective
  rw [← Category.assoc, b.homEquiv_naturality_right]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option profiler true in
set_option maxHeartbeats 1000000 in
-- The dependent comparison package requires additional elaboration heartbeats.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The abelian composition comparisons lift to module isomorphisms for inverse
image with the specified unit equation. Source: Stacks Project, Tags 03D8 and 03D7
(blueprint: lem-weil-pbc-inverse-image-composition-module-linear-core).

The lambda-bound ring sheaves, forgetful functors and module direct images below are
immediately applied to their actual definitions. The gamma maps are characterized by
constant sections. The inverse images, comparison maps and adjunctions are the data of
`etaleInverseImageModulesExact`; the hom-equivalence equations specify that these are
precisely the module adjunctions with the underlying abelian adjunctions.

Proof:
1. The three constant-section equations and naturality of `toSheafify`, followed
by `sheafify_hom_ext`, identify the ring maps for successive and composite pullback.
2. `SheafOfModules.pushforwardCongr₂` along the pullback-pasting isomorphism,
composed with `pushforwardComp.symm`, constructs the module direct-image comparison.
Its underlying map on sections is the abelian comparison.
3. `conjugateIsoEquiv` constructs the module inverse-image comparison from this
module direct-image comparison. Its mate unit equation is `unit_conjugateEquiv_symm`.
4. The specified hom-equivalence equations and their naturality identify the
composite module hom-equivalence with the abelian one. They also identify the
composite-map unit. Applying the injective abelian hom-equivalence to the desired
underlying comparison equation reduces it to the module mate equation, naturality
of the direct-image comparison, and the abelian mate equation. Naturality and
invertibility of both module comparisons follow from their constructors. -/
theorem etaleInverseImageCompositionModuleLinearCore
    (X Y Z : Scheme.{u}) (uMap : Y ⟶ X) (vMap : Z ⟶ Y) (R : CommRingCat.{u + 1}) :
    (fun (RX : Sheaf (X.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (RY : Sheaf (Y.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (RZ : Sheaf (Z.smallGrothendieckTopology @Etale) CommRingCat.{u + 1})
      (etaX : ((Functor.const X.Etaleᵒᵖ).obj R) ⟶ RX.obj)
      (etaY : ((Functor.const Y.Etaleᵒᵖ).obj R) ⟶ RY.obj)
      (etaZ : ((Functor.const Z.Etaleᵒᵖ).obj R) ⟶ RZ.obj) =>
    ∀ (gammaU : RX ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ uMap).sheafPushforwardContinuous
      CommRingCat.{u + 1}
        (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).obj RY)
      (gammaV : RY ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ vMap).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj RZ)
      (gammaUV : RX ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫
        uMap)).sheafPushforwardContinuous CommRingCat.{u + 1}
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj RZ),
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gammaU.hom.app W (etaX.app W r) =
        etaY.app ((MorphismProperty.Over.pullback @Etale ⊤ uMap).op.obj W) r) →
    (∀ (W : Y.Etaleᵒᵖ) (r : R),
      gammaV.hom.app W (etaY.app W r) =
        etaZ.app ((MorphismProperty.Over.pullback @Etale ⊤ vMap).op.obj W) r) →
    (∀ (W : X.Etaleᵒᵖ) (r : R),
      gammaUV.hom.app W (etaX.app W r) =
        etaZ.app ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫ uMap)).op.obj W) r) →
    (fun (UX : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ Sheaf (X.smallGrothendieckTopology @Etale)
      AddCommGrpCat.{u + 1})
      (UY : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ Sheaf (Y.smallGrothendieckTopology @Etale)
        AddCommGrpCat.{u + 1})
      (UZ : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ Sheaf (Z.smallGrothendieckTopology @Etale)
        AddCommGrpCat.{u + 1})
      (PU : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX))
      (PV : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (PUV : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) ⥤ SheafOfModules.{u + 1} ((sheafCompose
        (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX))
      (pU : PU ⋙ UX ≅ UY ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} uMap)
      (pV : PV ⋙ UY ≅ UZ ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} vMap)
      (pUV : PUV ⋙ UX ≅ UZ ⋙ Etale.lowerStar AddCommGrpCat.{u + 1} (vMap ≫ uMap)) =>
    ∀ (LU : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (eU : LU ⋙ UY ≅ UX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} uMap)
      (aU : LU ⊣ PU),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
      (h : LU.obj G ⟶ F),
      UX.map (aU.homEquiv G F h) ≫ pU.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} uMap).homEquiv
          (UX.obj G) (UY.obj F) (eU.inv.app G ≫ UY.map h)) →
    ∀ (LV : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (eV : LV ⋙ UZ ≅ UY ⋙ Etale.upperStar AddCommGrpCat.{u + 1} vMap)
      (aV : LV ⊣ PV),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (h : LV.obj G ⟶ F),
      UY.map (aV.homEquiv G F h) ≫ pV.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} vMap).homEquiv
          (UY.obj G) (UZ.obj F) (eV.inv.app G ≫ UZ.map h)) →
    ∀ (LUV : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ⥤ SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (eUV : LUV ⋙ UZ ≅ UX ⋙ Etale.upperStar AddCommGrpCat.{u + 1} (vMap ≫ uMap))
      (aUV : LUV ⊣ PUV),
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (F : SheafOfModules.{u + 1} ((sheafCompose
      (Z.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (h : LUV.obj G ⟶ F),
      UX.map (aUV.homEquiv G F h) ≫ pUV.hom.app F =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (vMap ≫ uMap)).homEquiv
          (UX.obj G) (UZ.obj F) (eUV.inv.app G ≫ UZ.map h)) →
    ∃ (d : PUV ≅ PV ⋙ PU) (c : LU ⋙ LV ≅ LUV),
      (∀ F : SheafOfModules.{u + 1} ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ),
        UX.map (d.hom.app F) ≫ pU.hom.app (PV.obj F) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} uMap).map (pV.hom.app F) =
          pUV.hom.app F ≫
          (Etale.lowerStarComp AddCommGrpCat.{u + 1} vMap uMap).inv.app (UZ.obj F)) ∧
      (∀ G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX),
        UZ.map (c.hom.app G) ≫ eUV.hom.app G =
          eV.hom.app (LU.obj G) ≫
            (Etale.upperStar AddCommGrpCat.{u + 1} vMap).map (eU.hom.app G) ≫
            (Etale.upperStarComp AddCommGrpCat.{u + 1} vMap uMap).inv.app (UX.obj G)) ∧
      (∀ G : SheafOfModules.{u + 1} ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX),
        (aU.comp aV).unit.app G ≫ (PV ⋙ PU).map (c.hom.app G) =
          aUV.unit.app G ≫ d.hom.app (LUV.obj G))
      )
      (SheafOfModules.toSheaf ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) (SheafOfModules.toSheaf ((sheafCompose
        (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY))
        (SheafOfModules.toSheaf ((sheafCompose (Z.smallGrothendieckTopology @Etale) (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ))
      (SheafOfModules.pushforward (J := (X.smallGrothendieckTopology @Etale)) (K :=
        (Y.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ uMap)
        ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤
          uMap).sheafPushforwardContinuous CommRingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (Y.smallGrothendieckTopology @Etale)).obj RY) gammaU))
      (SheafOfModules.pushforward (J := (Y.smallGrothendieckTopology @Etale)) (K :=
        (Z.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ vMap)
        ((sheafCompose (Y.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤
          vMap).sheafPushforwardContinuous CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).obj RZ) gammaV))
      (SheafOfModules.pushforward (J := (X.smallGrothendieckTopology @Etale)) (K :=
        (Z.smallGrothendieckTopology @Etale))
        (F := MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫ uMap))
        ((sheafCompose (X.smallGrothendieckTopology @Etale) (forget₂ CommRingCat.{u + 1} RingCat.{u
          + 1})).map (Y := ((MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫
          uMap)).sheafPushforwardContinuous CommRingCat.{u + 1} (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale)).obj RZ) gammaUV))
      (Iso.refl _) (Iso.refl _) (Iso.refl _))
      ((constantSheaf (X.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      ((constantSheaf (Y.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      ((constantSheaf (Z.smallGrothendieckTopology @Etale) CommRingCat.{u + 1}).obj R)
      (toSheafify (X.smallGrothendieckTopology @Etale) ((Functor.const X.Etaleᵒᵖ).obj R))
      (toSheafify (Y.smallGrothendieckTopology @Etale) ((Functor.const Y.Etaleᵒᵖ).obj R))
      (toSheafify (Z.smallGrothendieckTopology @Etale) ((Functor.const Z.Etaleᵒᵖ).obj R))
 := by
  classical
  let JX : GrothendieckTopology (MorphismProperty.Over @Etale ⊤ X) :=
    X.smallGrothendieckTopology (Q := @Etale) @Etale
  let JY : GrothendieckTopology (MorphismProperty.Over @Etale ⊤ Y) :=
    Y.smallGrothendieckTopology (Q := @Etale) @Etale
  let JZ : GrothendieckTopology (MorphismProperty.Over @Etale ⊤ Z) :=
    Z.smallGrothendieckTopology (Q := @Etale) @Etale
  let : HasWeakSheafify JX CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify JY CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify JZ CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify X.smallEtaleTopology CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify Y.smallEtaleTopology CommRingCat.{u + 1} := inferInstance
  let : HasWeakSheafify Z.smallEtaleTopology CommRingCat.{u + 1} := inferInstance
  intro gammaU gammaV gammaUV hU hV hUV LU eU aU hLU LV eV aV hLV LUV eUV aUV hLUV
  let f := MorphismProperty.Over.pullback @Etale ⊤ uMap
  let g := MorphismProperty.Over.pullback @Etale ⊤ vMap
  let h := MorphismProperty.Over.pullback @Etale ⊤ (vMap ≫ uMap)
  have : f.IsContinuous JX JY :=
    Etale.isContinuous_overPullback uMap
  have : g.IsContinuous JY JZ :=
    Etale.isContinuous_overPullback vMap
  have : h.IsContinuous JX JZ :=
    Etale.isContinuous_overPullback (vMap ≫ uMap)
  let RZ : Sheaf JZ CommRingCat.{u + 1} := (constantSheaf JZ
    CommRingCat.{u + 1}).obj R
  let SX : Sheaf JX RingCat.{u + 1} :=
    (sheafCompose JX (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf JX CommRingCat.{u + 1}).obj R)
  let SY : Sheaf JY RingCat.{u + 1} :=
    (sheafCompose JY (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf JY CommRingCat.{u + 1}).obj R)
  let SZ : Sheaf JZ RingCat.{u + 1} :=
    (sheafCompose JZ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ
  let UX := SheafOfModules.toSheaf.{u + 1} SX
  let UZ := SheafOfModules.toSheaf.{u + 1} SZ
  let UY := SheafOfModules.toSheaf.{u + 1} SY
  let AX := Sheaf JX
    AddCommGrpCat.{u + 1}
  let AY := Sheaf JY
    AddCommGrpCat.{u + 1}
  let AZ := Sheaf JZ
    AddCommGrpCat.{u + 1}
  let lu : AX ⥤ AY := Etale.upperStar AddCommGrpCat.{u + 1} uMap
  let lv : AY ⥤ AZ := Etale.upperStar AddCommGrpCat.{u + 1} vMap
  let luv : AX ⥤ AZ := Etale.upperStar AddCommGrpCat.{u + 1} (vMap ≫ uMap)
  let pu : AY ⥤ AX := Etale.lowerStar AddCommGrpCat.{u + 1} uMap
  let pv : AZ ⥤ AY := Etale.lowerStar AddCommGrpCat.{u + 1} vMap
  let puv : AZ ⥤ AX := Etale.lowerStar AddCommGrpCat.{u + 1} (vMap ≫ uMap)
  let au : lu ⊣ pu := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} uMap
  let av : lv ⊣ pv := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} vMap
  let auv : luv ⊣ puv :=
    Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (vMap ≫ uMap)
  let d0 : puv ≅ pv ⋙ pu := (Etale.lowerStarComp AddCommGrpCat.{u + 1} vMap uMap).symm
  let c0 : lu ⋙ lv ≅ luv := (Etale.upperStarComp AddCommGrpCat.{u + 1} vMap uMap).symm
  let phi : SX ⟶ (f.sheafPushforwardContinuous RingCat.{u + 1}
      JX JY).obj SY := (sheafCompose JX
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map gammaU
  let psi : SY ⟶ (g.sheafPushforwardContinuous RingCat.{u + 1}
      JY JZ).obj SZ := (sheafCompose JY
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map gammaV
  let chi : SX ⟶ (h.sheafPushforwardContinuous RingCat.{u + 1}
      JX JZ).obj SZ := (sheafCompose JX
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map gammaUV
  let alpha : f ⋙ g ≅ h := (MorphismProperty.Over.pullbackComp vMap uMap).symm
  have : (f ⋙ g).IsContinuous JX
      JZ :=
    Functor.isContinuous_comp f g _ JY _
  have hr : gammaUV ≫
      (Functor.sheafPushforwardContinuousNatTrans alpha.hom CommRingCat.{u + 1}
        JX JZ).app RZ =
      gammaU ≫ (f.sheafPushforwardContinuous CommRingCat.{u + 1}
        JX JY).map gammaV := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext JX _ _
      (((f ⋙ g).sheafPushforwardContinuous CommRingCat.{u + 1}
        JX JZ).obj RZ).property
    ext W r
    change RZ.obj.map (alpha.hom.app W.unop).op
        (gammaUV.hom.app W ((toSheafify JX
          ((Functor.const X.Etaleᵒᵖ).obj R)).app W r)) =
      gammaV.hom.app (f.op.obj W)
        (gammaU.hom.app W ((toSheafify JX
          ((Functor.const X.Etaleᵒᵖ).obj R)).app W r))
    erw [hUV, hU, hV]
    exact congrArg (fun k => k r)
      ((toSheafify JZ
        ((Functor.const Z.Etaleᵒᵖ).obj R)).naturality
        (alpha.hom.app W.unop).op).symm
  have hr' : chi ≫
      (Functor.sheafPushforwardContinuousNatTrans alpha.hom RingCat.{u + 1}
        JX JZ).app
        ((sheafCompose JZ
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RZ) =
      phi ≫ (f.sheafPushforwardContinuous RingCat.{u + 1}
        JX JY).map psi := by
    exact congrArg
      ((sheafCompose JX
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) hr
  let d := SheafOfModules.pushforwardCongr₂ chi alpha hr' ≪≫
    (SheafOfModules.pushforwardComp (J := JX)
      (K := JY) (K' := JZ) (F := f) (G := g) phi psi).symm
  let c := (conjugateIsoEquiv aUV (aU.comp aV)).symm d
  have hd : ∀ F, UX.map (d.hom.app F) = d0.hom.app (UZ.obj F) := by
    intro F
    ext W x
    change (((SheafOfModules.pushforwardComp (J := JX) (K := JY) (K' := JZ)
      (F := f) (G := g) phi psi).inv.app F).val.app W).hom
      ((((SheafOfModules.pushforwardCongr₂ chi alpha hr').hom.app F).val.app W).hom x) = _
    simp only [SheafOfModules.pushforwardComp_inv_app_val_app,
      SheafOfModules.pushforwardCongr₂_hom_app_val_app_hom_apply]; rfl
  have hu : ∀ G, (aU.comp aV).unit.app G ≫
      (SheafOfModules.pushforward psi ⋙ SheafOfModules.pushforward phi).map
        (c.hom.app G) = aUV.unit.app G ≫ d.hom.app (LUV.obj G) := by
    intro G
    exact (unit_conjugateEquiv_symm aUV (aU.comp aV) d.hom G).symm
  have hcomp : ∀ G F (k : (LU ⋙ LV).obj G ⟶ F),
      UX.map ((aU.comp aV).homEquiv G F k) =
      (au.comp av).homEquiv (UX.obj G) (UZ.obj F)
        (lv.map (eU.inv.app G) ≫
          eV.inv.app (LU.obj G) ≫ UZ.map k) := by
    let pU : SheafOfModules.pushforward phi ⋙ UX ≅ UY ⋙ pu := Iso.refl _
    let pV : SheafOfModules.pushforward psi ⋙ UY ≅ UZ ⋙ pv := Iso.refl _
    intro G F k
    have hh := comp_homEquiv_forget UX UY UZ LU LV
      (SheafOfModules.pushforward phi) (SheafOfModules.pushforward psi)
      lu lv pu pv aU aV au av pU pV eU eV hLU hLV G F k
    set_option backward.isDefEq.respectTransparency false in
      exact erase_map_id pu (UY.obj ((SheafOfModules.pushforward psi).obj F))
        (UX.map ((aU.comp aV).homEquiv G F k))
        ((au.comp av).homEquiv (UX.obj G) (UZ.obj F)
          (lv.map (eU.inv.app G) ≫ eV.inv.app (LU.obj G) ≫ UZ.map k)) hh
  have hunit : ∀ G, UX.map (aUV.unit.app G) ≫
      puv.map (eUV.hom.app G) =
      auv.unit.app (UX.obj G) := by
    let pUV : SheafOfModules.pushforward chi ⋙ UX ≅ UZ ⋙ puv := Iso.refl _
    intro G
    have hh := unit_forget UX UZ LUV (SheafOfModules.pushforward chi)
      luv puv aUV auv pUV eUV hLUV G
    set_option backward.isDefEq.respectTransparency false in
      exact erase_middle_id (UX.map (aUV.unit.app G)) (puv.map (eUV.hom.app G))
        (auv.unit.app (UX.obj G)) hh
  have hconj : conjugateEquiv auv (au.comp av) c0.hom = d0.hom :=
    congrArg Iso.inv
      (Etale.conjugateIsoEquiv_upperStarComp AddCommGrpCat.{u + 1} vMap uMap)
  have hmate : ∀ G, (au.comp av).unit.app G ≫
      (pv ⋙ pu).map (c0.hom.app G) =
      auv.unit.app G ≫ d0.hom.app (luv.obj G) := by
    intro G
    have hh := unit_conjugateEquiv auv (au.comp av) c0.hom G
    exact hh.symm.trans (congrArg
      (fun (q : puv ⟶ pv ⋙ pu) => auv.unit.app G ≫ q.app (luv.obj G)) hconj)
  refine ⟨d, c, ?_, ?_, hu⟩
  · intro F
    ext W x
    rfl
  · clear_value d c
    intro G
    let ec := eV.app (LU.obj G) ≪≫
      lv.mapIso (eU.app G)
    have hec : ec.inv = lv.map (eU.inv.app G) ≫ eV.inv.app (LU.obj G) := rfl
    change UZ.map (c.hom.app G) ≫ eUV.hom.app G =
      eV.hom.app (LU.obj G) ≫ lv.map (eU.hom.app G) ≫ c0.hom.app (UX.obj G)
    rw [← Category.assoc]
    change UZ.map (c.hom.app G) ≫ eUV.hom.app G = ec.hom ≫ c0.hom.app (UX.obj G)
    apply compare_by_homEquiv (au.comp av) (UX.obj G) ec (eUV.app G)
      (UZ.map (c.hom.app G)) (c0.hom.app (UX.obj G))
    rw [hec, Category.assoc]
    change (au.comp av).homEquiv (UX.obj G) (UZ.obj (LUV.obj G))
      (lv.map (eU.inv.app G) ≫
        eV.inv.app (LU.obj G) ≫ UZ.map (c.hom.app G)) ≫ _ = _
    rw [← hcomp G (LUV.obj G) (c.hom.app G), (aU.comp aV).homEquiv_apply,
      hu G, UX.map_comp]
    conv_lhs =>
      arg 1
      arg 2
      rw [hd (LUV.obj G)]
    conv_rhs => erw [(au.comp av).homEquiv_apply]
    exact (paste_rectangle (UX.map (aUV.unit.app G))
      (d0.hom.app (UZ.obj (LUV.obj G))) ((pv ⋙ pu).map (eUV.hom.app G))
      (puv.map (eUV.hom.app G)) (d0.hom.app (luv.obj (UX.obj G)))
      (auv.unit.app (UX.obj G)) (d0.hom.naturality (eUV.hom.app G))
      (hunit G)).trans (hmate (UX.obj G)).symm

end AlgebraicGeometry
