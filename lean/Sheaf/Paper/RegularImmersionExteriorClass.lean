/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityConventions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.Paper.PurityFrameClass
import Sheaf.Paper.PurityFrameIndependence
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

public import Sheaf.Paper.RegularImmersionClassData
/-!
# Supported exterior product of regular-immersion classes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
def-pur-regular-immersion-exterior-class (blueprint: def-pur-regular-immersion-exterior-class).

All coefficients are the actual finite quotient of the fixed purity setting. Supported
classes use the published Hom model, and their restriction uses the section-normalized
closed coefficient exchange. The frame product is the existing ordered Kummer-boundary fold.

## Main declarations

* `regularProductSupport`.
* `regularExteriorClass`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The product support and the intersection of the two projection-pulled supports
are uniquely isomorphic over X1 times_k X2.
Source: exterior products in sk-thm-regular(d)
(blueprint: def-pur-regular-immersion-exterior-class).
Proof: both schemes represent pairs of points in Z1 and Z2 with the same image in k.
The pullback universal properties give mutually inverse maps over the product. The
intersection map is monic, so its equation over the product determines the map uniquely. -/
theorem regularProductSupport_existsUnique
    {B X Y Z W : Scheme.{u}} (a : X ⟶ B) (b : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! e : pullback (i ≫ a) (j ≫ b) ≅
        pullback (pullback.snd i (pullback.fst a b)) (pullback.snd j (pullback.snd a b)),
      e.hom ≫ cupIntersection (pullback.snd i (pullback.fst a b))
        (pullback.snd j (pullback.snd a b)) = Etale.supportedProductImmersion a b i j := by
  sorry

/-- The unique support comparison over the product.
Source: sk-thm-regular(d) (blueprint: def-pur-regular-immersion-exterior-class). -/
def regularProductSupport {B X Y Z W : Scheme.{u}} (a : X ⟶ B) (b : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :=
  (regularProductSupport_existsUnique a b i j).exists.choose

/-- The defining equation of the canonical support comparison.
Source: sk-thm-regular(d) (blueprint: def-pur-regular-immersion-exterior-class).
Proof: take the property of the unique comparison supplied by the pullback universal
properties in regularProductSupport_existsUnique. -/
theorem regularProductSupport_over {B X Y Z W : Scheme.{u}} (a : X ⟶ B) (b : Y ⟶ B)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (regularProductSupport a b i j).hom ≫
      cupIntersection (pullback.snd i (pullback.fst a b)) (pullback.snd j (pullback.snd a b)) =
        Etale.supportedProductImmersion a b i j := by
  sorry

/-- The degree of the product is twice the sum of the codimensions.
Source: sk-thm-regular(d) (blueprint: def-pur-regular-immersion-exterior-class).
Proof: use the integer cast of the natural sum and distribute multiplication by two. -/
theorem regularProductDegree (c d : ℕ) :
    2 * (c : ℤ) + 2 * (d : ℤ) = 2 * ((c + d : ℕ) : ℤ) := by
  sorry

/-- Transport a supported class along its specified support isomorphism and degree
equality. This is the existing closed-coefficient comparison and frameCupTransport.
Source: exterior products (blueprint: def-pur-regular-immersion-exterior-class). -/
def regularSupportTransfer (P : PurityFiniteSetting.{u}) {Z W X : Scheme.{u}}
    (i : Z ⟶ X) (j : W ⟶ X) (e : Z ≅ W) (h : e.hom ≫ j = i)
    (a b : ℤ) (hab : a = b) (c : ℕ)
    (γ : cupSupportedHom P j ((cupSingle P X).obj (P.frameTwist X c)) a) :
    cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) b :=
  frameCupTransport ((cupSingle P X).map (P.frameClosedCoefficientIso i j e h).hom)
    a b hab γ (𝟙 _)

/-- The actual supported exterior product of two classes: projection inverse images,
the published supported cup, ordered Tate multiplication, and the canonical support
identification. Thus this does not replace the exterior product by an arbitrary map.
Source: the final sentence of the theorem
(blueprint: def-pur-regular-immersion-exterior-class). -/
def regularExteriorClass (P : PurityFiniteSetting.{u})
    {X Y Z W : Scheme.{u}} (a : X ⟶ Spec (.of P.field.k)) (b : Y ⟶ Spec (.of P.field.k))
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] (c d : ℕ)
    (γ : cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)))
    (δ : cupSupportedHom P j ((cupSingle P Y).obj (P.frameTwist Y d)) (2 * (d : ℤ))) :
    cupSupportedHom P (Etale.supportedProductImmersion a b i j)
      ((cupSingle P (pullback a b)).obj (P.frameTwist (pullback a b) (c + d)))
      (2 * ((c + d : ℕ) : ℤ)) :=
  P.regularSupportTransfer (Etale.supportedProductImmersion a b i j)
    (cupIntersection (pullback.snd i (pullback.fst a b))
      (pullback.snd j (pullback.snd a b)))
    (regularProductSupport a b i j) (regularProductSupport_over a b i j)
    (2 * (c : ℤ) + 2 * (d : ℤ)) (2 * ((c + d : ℕ) : ℤ)) (regularProductDegree c d)
    (c + d)
    (P.regularNaturalCup (pullback.fst a b ≫ a)
      (pullback.snd i (pullback.fst a b)) (pullback.snd j (pullback.snd a b))
      (2 * (c : ℤ)) (2 * (d : ℤ)) c d
      (P.regularSupportedPullback i _ (pullback.fst a b) (pullback.fst i (pullback.fst a b))
        (IsPullback.of_hasPullback _ _) a c γ)
      (P.regularSupportedPullback j _ (pullback.snd a b) (pullback.fst j (pullback.snd a b))
        (IsPullback.of_hasPullback _ _) b d δ))


end WeilConjectures.PurityFiniteSetting
