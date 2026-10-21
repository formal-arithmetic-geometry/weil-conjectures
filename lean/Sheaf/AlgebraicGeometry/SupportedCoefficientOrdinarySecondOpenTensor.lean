/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenMateQuotient
import Sheaf.AlgebraicGeometry.SupportedCoefficientTensorQuotientSquare
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Ordinary supported coefficient tensors under second-variable open restriction -/

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

/-- The ordinary uncut first coefficient map on the second open product.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-second-open-tensor). -/
noncomputable def supportSecondOrdinaryOpenFirstCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b]
    (V : Y.Opens) (M : ModuleCat.{u + 1} A) :
    (supportedFirstCoefficients A f (V.ι ≫ g) b).obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).obj
        ((supportedFirstCoefficients A f g b).obj M) :=
  (upperStarComp (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
    (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
    (supportedSecondOpenMap_fst f g V).symm).hom.app ((supportedCoefficients A b).obj M)

/-- The ordinary second coefficient map on the open product, with canonical projection
composition. Source: Tag 0F1E
(blueprint: lem-pur-supported-coefficient-ordinary-second-open-tensor). -/
noncomputable def supportSecondOrdinaryOpenCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d]
    (V : Y.Opens) (N : ModuleCat.{u + 1} A) :
    (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)).obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).obj
        ((supportedSecondCoefficients A f g d).obj N) :=
  (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))).map
      ((supportCoefficientMate (supportedCoefficientAdjunction A d)
        (supportedCoefficientAdjunction A (supportOnOpen d V))
        (upperStar (ModuleCat.{u + 1} A) V.ι)
        (supportTransport A V.ι d (supportOnOpen d V)
          (supportOnOpen_complement d V))).app N) ≫
    (squareUpperStarIso (ModuleCat.{u + 1} A)
      (CommSq.mk (supportedSecondOpenMap_snd f g V))).hom.app
        ((supportedCoefficients A d).obj N)

/-- The natural transformation underlying the ordinary uncut first-coefficient map.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-second-open-tensor). -/
noncomputable def supportSecondOrdinaryOpenFirstCoefficientNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b] (V : Y.Opens) :
    supportedFirstCoefficients A f (V.ι ≫ g) b ⟶
      supportedFirstCoefficients A f g b ⋙
        upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V) :=
  Functor.whiskerLeft (supportedCoefficients A b)
      (upperStarComp (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
        (supportedSecondOpenMap_fst f g V).symm).hom ≫
    (Functor.associator (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))).inv

/-- The natural transformation underlying the ordinary cut second-coefficient map.
It is constructed by whiskering the actual support mate and the projection-square iso,
so it can be passed directly to the exact derived transformation construction.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-ordinary-second-open-tensor). -/
noncomputable def supportSecondOrdinaryOpenCoefficientNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (V : Y.Opens) :
    supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V) ⟶
      supportedSecondCoefficients A f g d ⋙
        upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V) :=
  Functor.whiskerRight
      (supportCoefficientMate (supportedCoefficientAdjunction A d)
        (supportedCoefficientAdjunction A (supportOnOpen d V))
        (upperStar (ModuleCat.{u + 1} A) V.ι)
        (supportTransport A V.ι d (supportOnOpen d V) (supportOnOpen_complement d V)))
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))) ≫
    (Functor.associator (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) V.ι)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g)))).hom ≫
    Functor.whiskerLeft (supportedCoefficients A d)
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (CommSq.mk (supportedSecondOpenMap_snd f g V))).hom ≫
    (Functor.associator (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))).inv

private theorem firstCoefficientNatTrans_app
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b]
    (V : Y.Opens) (M : ModuleCat.{u + 1} A) :
    (supportSecondOrdinaryOpenFirstCoefficientNatTrans A f g b V).app M =
      supportSecondOrdinaryOpenFirstCoefficientMap A f g b V M := by
  simp [supportSecondOrdinaryOpenFirstCoefficientNatTrans,
    supportSecondOrdinaryOpenFirstCoefficientMap]

private theorem secondCoefficientNatTrans_app
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d]
    (V : Y.Opens) (N : ModuleCat.{u + 1} A) :
    (supportSecondOrdinaryOpenCoefficientNatTrans A f g d V).app N =
      supportSecondOrdinaryOpenCoefficientMap A f g d V N := by
  simp [supportSecondOrdinaryOpenCoefficientNatTrans,
    supportSecondOrdinaryOpenCoefficientMap]

/-- The ordinary supported coefficient tensor square for restriction in the second variable.
Source: Stacks Tag 0F1E, the coefficient calculation in step 11 of
lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-ordinary-second-open-tensor).
Proof: the product-support mate preserves its quotient by the mate normalization theorem.
The projected second mate preserves the second quotient by naturality of the pullback square
and compatibility of inverse image of constants with composition. The uncut first map
preserves the first quotient by the same composition compatibility. The proved ordinary
quotient-square theorem then gives the tensor square, by cancellation of the product
quotient. This proof applies to arbitrary modules, including zero modules, empty opens,
and empty supports, and requires no flatness. -/
theorem supportedCoefficientTensor_ordinaryOpenSecond
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (M N : ModuleCat.{u + 1} A) :
    (supportCoefficientMate
        (supportedCoefficientAdjunction A (supportedProductImmersion f g b d))
        (supportedCoefficientAdjunction A
          (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V)))
        (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))
        (supportTransport A (supportedSecondOpenMap f g V)
          (supportedProductImmersion f g b d)
          (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
          (supportedSecondOpenSupport_complement f g b d V))).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).map
        (supportedCoefficientTensor A f g b d M N) ≫
      Functor.OplaxMonoidal.δ
        (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))
        ((supportedFirstCoefficients A f g b).obj M)
        ((supportedSecondCoefficients A f g d).obj N) =
    supportedCoefficientTensor A f (V.ι ≫ g) b (supportOnOpen d V) M N ≫
      ((supportSecondOrdinaryOpenFirstCoefficientNatTrans A f g b V).app M ⊗ₘ
        (supportSecondOrdinaryOpenCoefficientNatTrans A f g d V).app N) := by
  rw [firstCoefficientNatTrans_app, secondCoefficientNatTrans_app]
  apply supportedCoefficientTensor_quotientSquare A f g b d f (V.ι ≫ g)
    b (supportOnOpen d V) (supportedSecondOpenMap f g V) M N
  · exact supportedCoefficientOpenMate_quotient A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V) (M ⊗ N)
  · exact projectedQuotient_comp A (supportedSecondOpenMap f g V) (pullback.fst f g)
      (pullback.fst f (V.ι ≫ g)) (supportedSecondOpenMap_fst f g V).symm M
      (supportedCoefficientQuotient A b M)
  · exact projectedQuotient_square A (supportedSecondOpenMap f g V) (pullback.snd f g)
      (pullback.snd f (V.ι ≫ g)) V.ι (supportedSecondOpenMap_snd f g V) N
      (supportedCoefficientQuotient A d N)
      (supportedCoefficientQuotient A (supportOnOpen d V) N) _
      (supportedCoefficientOpenMate_quotient A V.ι d (supportOnOpen d V)
        (supportOnOpen_complement d V) N)

end AlgebraicGeometry.Etale
