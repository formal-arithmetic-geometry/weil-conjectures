/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientOpenMateQuotient
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientTensorQuotientSquare
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Ordinary supported coefficient tensors under open restriction -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

private theorem constantComposition_inv (A : Type (u + 1)) [CommRing A]
    {R S T : Scheme.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hc : c = a ≫ b) (M : ModuleCat.{u + 1} A) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) c).inv.app M ≫
        (upperStarComp (ModuleCat.{u + 1} A) a b c hc).hom.app
          ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) a).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b).inv.app M) := by
  have h : (upperStarComp (ModuleCat.{u + 1} A) a b c hc).hom.app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) a).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b).hom.app M) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).hom.app M =
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) c).hom.app M := by
    subst c
    exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) a b M
  let e := (upperStar (ModuleCat.{u + 1} A) a).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b).app M) ≪≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).app M
  apply (cancel_mono e.hom).1
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  change _ ≫ _ ≫ (upperStar (ModuleCat.{u + 1} A) a).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b).hom.app M) ≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).hom.app M =
    _ ≫ _ ≫ (upperStar (ModuleCat.{u + 1} A) a).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) b).hom.app M) ≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).hom.app M
  rw [h, Iso.inv_hom_id_app]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

private theorem constantSquare_inv (A : Type (u + 1)) [CommRing A]
    {P Q X X' : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X')
    (a : X' ⟶ X) (hp : h ≫ p = q ≫ a) (M : ModuleCat.{u + 1} A) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) q).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) q).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).inv.app M) ≫
        (squareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hp)).hom.app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) h).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).inv.app M) := by
  dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, ← Category.assoc,
    ← constantComposition_inv A q a (h ≫ p) hp M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact constantComposition_inv A h p (h ≫ p) rfl M

private theorem projectedQuotient_square (A : Type (u + 1)) [CommRing A]
    {P Q X X' : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X')
    (a : X' ⟶ X) (hp : h ≫ p = q ≫ a) (M : ModuleCat.{u + 1} A)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {F' : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶ F)
    (e' : (constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶ F')
    (t : F' ⟶ (upperStar (ModuleCat.{u + 1} A) a).obj F)
    (ht : e' ≫ t =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) a).map e) :
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) q).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) q).map e') ≫
      ((upperStar (ModuleCat.{u + 1} A) q).map t ≫
        (squareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hp)).hom.app F) =
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
      (upperStar (ModuleCat.{u + 1} A) h).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).inv.app M ≫
          (upperStar (ModuleCat.{u + 1} A) p).map e) := by
  rw [Category.assoc, ← Functor.map_comp_assoc, ht, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (squareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk hp)).hom.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% (constantSquare_inv A h p q a hp M)]
  rw [← Functor.map_comp]

private theorem projectedQuotient_comp (A : Type (u + 1)) [CommRing A]
    {P Q X : Scheme.{u}} (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X)
    (hp : q = h ≫ p) (M : ModuleCat.{u + 1} A)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶ F) :
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) q).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) q).map e) ≫
      (upperStarComp (ModuleCat.{u + 1} A) h p q hp).hom.app F =
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
      (upperStar (ModuleCat.{u + 1} A) h).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).inv.app M ≫
          (upperStar (ModuleCat.{u + 1} A) p).map e) := by
  rw [Category.assoc, (upperStarComp (ModuleCat.{u + 1} A) h p q hp).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, constantComposition_inv A h p q hp M,
    Category.assoc, ← Functor.map_comp]

/-- The ordinary first coefficient map on the open product, with canonical projection
composition. Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-open-tensor). -/
noncomputable def supportFirstOrdinaryOpenCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b]
    (U : X.Opens) (M : ModuleCat.{u + 1} A) :
    (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U)).obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).obj
        ((supportedFirstCoefficients A f g b).obj M) :=
  (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g)).map
      ((supportCoefficientMate (supportedCoefficientAdjunction A b)
        (supportedCoefficientAdjunction A (supportOnOpen b U))
        (upperStar (ModuleCat.{u + 1} A) U.ι)
        (supportTransport A U.ι b (supportOnOpen b U)
          (supportOnOpen_complement b U))).app M) ≫
    (squareUpperStarIso (ModuleCat.{u + 1} A)
      (CommSq.mk (supportedFirstOpenMap_fst f g U))).hom.app
        ((supportedCoefficients A b).obj M)

/-- The ordinary uncut second coefficient map on the first open product.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-open-tensor). -/
noncomputable def supportFirstOrdinaryOpenSecondCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d]
    (U : X.Opens) (N : ModuleCat.{u + 1} A) :
    (supportedSecondCoefficients A (U.ι ≫ f) g d).obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).obj
        ((supportedSecondCoefficients A f g d).obj N) :=
  (upperStarComp (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
    (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
    (supportedFirstOpenMap_snd f g U).symm).hom.app ((supportedCoefficients A d).obj N)

/-- The natural transformation underlying the ordinary cut first-coefficient map.
It is constructed by whiskering the actual support mate and the projection-square iso,
so it can be passed directly to the exact derived transformation construction.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-open-tensor). -/
noncomputable def supportFirstOrdinaryOpenCoefficientNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b] (U : X.Opens) :
    supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U) ⟶
      supportedFirstCoefficients A f g b ⋙
        upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U) :=
  Functor.whiskerRight
      (supportCoefficientMate (supportedCoefficientAdjunction A b)
        (supportedCoefficientAdjunction A (supportOnOpen b U))
        (upperStar (ModuleCat.{u + 1} A) U.ι)
        (supportTransport A U.ι b (supportOnOpen b U) (supportOnOpen_complement b U)))
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g)) ≫
    (Functor.associator (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) U.ι)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g))).hom ≫
    Functor.whiskerLeft (supportedCoefficients A b)
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (CommSq.mk (supportedFirstOpenMap_fst f g U))).hom ≫
    (Functor.associator (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))).inv

/-- The natural transformation underlying the ordinary uncut second-coefficient map.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-open-tensor). -/
noncomputable def supportFirstOrdinaryOpenSecondCoefficientNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens) :
    supportedSecondCoefficients A (U.ι ≫ f) g d ⟶
      supportedSecondCoefficients A f g d ⋙
        upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U) :=
  Functor.whiskerLeft (supportedCoefficients A d)
      (upperStarComp (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
        (supportedFirstOpenMap_snd f g U).symm).hom ≫
    (Functor.associator (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))).inv

private theorem firstCoefficientNatTrans_app
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b]
    (U : X.Opens) (M : ModuleCat.{u + 1} A) :
    (supportFirstOrdinaryOpenCoefficientNatTrans A f g b U).app M =
      supportFirstOrdinaryOpenCoefficientMap A f g b U M := by
  simp [supportFirstOrdinaryOpenCoefficientNatTrans,
    supportFirstOrdinaryOpenCoefficientMap]

private theorem secondCoefficientNatTrans_app
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d]
    (U : X.Opens) (N : ModuleCat.{u + 1} A) :
    (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U).app N =
      supportFirstOrdinaryOpenSecondCoefficientMap A f g d U N := by
  simp [supportFirstOrdinaryOpenSecondCoefficientNatTrans,
    supportFirstOrdinaryOpenSecondCoefficientMap]

/-- The ordinary supported coefficient tensor square for restriction in the first variable.
Source: Stacks Tag 0F1E, the coefficient calculation in step 11 of
lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-ordinary-open-tensor).
Proof: the product-support mate preserves its quotient by the mate normalization theorem.
The projected first mate preserves the first quotient by naturality of the pullback square
and compatibility of inverse image of constants with composition. The uncut second map
preserves the second quotient by the same composition compatibility. The proved ordinary
quotient-square theorem then gives the tensor square, by cancellation of the product
quotient. This proof applies to arbitrary modules, including zero modules, empty opens,
and empty supports, and requires no flatness. -/
theorem supportedCoefficientTensor_ordinaryOpenFirst
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (M N : ModuleCat.{u + 1} A) :
    (supportCoefficientMate
        (supportedCoefficientAdjunction A (supportedProductImmersion f g b d))
        (supportedCoefficientAdjunction A
          (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
        (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
        (supportTransport A (supportedFirstOpenMap f g U)
          (supportedProductImmersion f g b d)
          (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
          (supportedFirstOpenSupport_complement f g b d U))).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).map
        (supportedCoefficientTensor A f g b d M N) ≫
      Functor.OplaxMonoidal.δ
        (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
        ((supportedFirstCoefficients A f g b).obj M)
        ((supportedSecondCoefficients A f g d).obj N) =
    supportedCoefficientTensor A (U.ι ≫ f) g (supportOnOpen b U) d M N ≫
      ((supportFirstOrdinaryOpenCoefficientNatTrans A f g b U).app M ⊗ₘ
        (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U).app N) := by
  rw [firstCoefficientNatTrans_app, secondCoefficientNatTrans_app]
  apply supportedCoefficientTensor_quotientSquare A f g b d (U.ι ≫ f) g
    (supportOnOpen b U) d (supportedFirstOpenMap f g U) M N
  · exact supportedCoefficientOpenMate_quotient A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U) (M ⊗ N)
  · exact projectedQuotient_square A (supportedFirstOpenMap f g U) (pullback.fst f g)
      (pullback.fst (U.ι ≫ f) g) U.ι (supportedFirstOpenMap_fst f g U) M
      (supportedCoefficientQuotient A b M)
      (supportedCoefficientQuotient A (supportOnOpen b U) M) _
      (supportedCoefficientOpenMate_quotient A U.ι b (supportOnOpen b U)
        (supportOnOpen_complement b U) M)
  · exact projectedQuotient_comp A (supportedFirstOpenMap f g U) (pullback.snd f g)
      (pullback.snd (U.ι ≫ f) g) (supportedFirstOpenMap_snd f g U).symm N
      (supportedCoefficientQuotient A d N)

end AlgebraicGeometry.Etale
