/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.FourierTateSupportComparison

/-! # Naturality of the compact-support Fourier datum

Source: prop-base-linear.proof.md, final paragraph
(blueprint: lem-fd-support-datum-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

private theorem transport_natural
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (P : A ⥤ A) (Q : B ⥤ B) (s : F ⋙ Q ≅ P ⋙ F)
    {K L : A} (φ : P.obj K ≅ K) (ψ : P.obj L ≅ L) (f : K ⟶ L)
    (h : P.map f ≫ ψ.hom = φ.hom ≫ f) :
    Q.map (F.map f) ≫ (s.app L ≪≫ F.mapIso ψ).hom =
      (s.app K ≪≫ F.mapIso φ).hom ≫ F.map f := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  change (F ⋙ Q).map f ≫ s.hom.app L ≫ F.map ψ.hom = _
  rw [s.hom.naturality_assoc]
  change s.hom.app K ≫ F.map (P.map f) ≫ F.map ψ.hom = _
  rw [← F.map_comp, h, F.map_comp]

private theorem transport_chain_natural
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (P P' : A ⥤ A) (Q Q' : B ⥤ B)
    (s₁ : Q ≅ Q') (s₂ : F ⋙ Q' ≅ P' ⋙ F) (s₃ : P' ≅ P)
    {K L : A} (φ : P.obj K ≅ K) (ψ : P.obj L ≅ L) (f : K ⟶ L)
    (h : P.map f ≫ ψ.hom = φ.hom ≫ f) :
    Q.map (F.map f) ≫
        (s₁.app (F.obj L) ≪≫ s₂.app L ≪≫ F.mapIso (s₃.app L ≪≫ ψ)).hom =
      (s₁.app (F.obj K) ≪≫ s₂.app K ≪≫ F.mapIso (s₃.app K ≪≫ φ)).hom ≫
        F.map f := by
  simpa only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using
      transport_natural F P Q
        (Functor.isoWhiskerLeft F s₁ ≪≫ s₂ ≪≫ Functor.isoWhiskerRight s₃ F) φ ψ f h

set_option maxHeartbeats 600000 in
-- Check the prescribed arithmetic exchange against the exact-derived comparisons.
private theorem pushDatum_natural
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) {K L : category D Λ X}
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K)
    (ψ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj L ≅ L)
    (a : K ⟶ L)
    (h : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).map a ≫
      ψ.hom = φ.hom ≫ a) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).map
        ((rightDerivedLowerShriekOfCompactification Λ (compactification D c)).map a) ≫
        (pushDatum D Λ c L ψ).hom =
      (pushDatum D Λ c K φ).hom ≫
        (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).map a := by
  let F := rightDerivedLowerShriekOfCompactification Λ (compactification D c)
  let sq := frobeniusSquare D c
  let : IsIso sq.middle := inferInstanceAs
    (IsIso (StrictWeilCondensed.modelFrobenius D (middle D c)).hom)
  let comm : CommSq (StrictWeilCondensed.modelFrobenius D X).hom (map D f) (map D f)
      (StrictWeilCondensed.modelFrobenius D Y).hom := ⟨(map_properties D f (𝟙 Y)).2.2⟩
  let := (CompactificationReindexing.square_isIso Λ sq comm).2
  exact transport_chain_natural F _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeilCondensed.modelFrobenius D Y).hom).symm
    (asIso (CompactificationReindexing.squareExchange Λ sq))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeilCondensed.modelFrobenius D X).hom) φ ψ a h

/-- Compact support followed by a shift carries a morphism of the specified
input Weil data to a morphism of output Weil data.
Source: prop-base-linear.proof.md, final paragraph
(blueprint: lem-fd-support-datum-naturality).
Proof: the compactification exchange is a natural transformation. Compose its
naturality square with the two exact-derived pullback comparisons and the images
of the input data; functoriality and the input equation give the pushforward
square. Naturality of the shift comparison gives the displayed shifted square. -/
theorem supportPartDatum_natural
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (r : ℤ)
    {K L : category D Λ X}
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K)
    (η : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj L ≅ L)
    (a : K ⟶ L)
    (h : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).map a ≫
      η.hom = φ.hom ≫ a) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).map
        ((supportPart D Λ c r).map a) ≫ (supportPartDatum D Λ c r L η).hom =
      (supportPartDatum D Λ c r K φ).hom ≫ (supportPart D Λ c r).map a := by
  have h₁ := pushDatum_natural D Λ c φ η a h
  simpa only [supportPart, supportPartDatum, Functor.comp_map, Functor.comp_obj,
    Category.assoc] using
    transport_natural (shiftFunctor (category D Λ Y) r) _ _
      ((StrictWeilCondensed.action Λ
        (StrictWeilCondensed.modelFrobenius D Y)).commShiftIso r) _ _ _ h₁

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
