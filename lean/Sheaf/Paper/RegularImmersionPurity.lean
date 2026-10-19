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
public import Sheaf.Paper.RegularImmersionExteriorClass
public import Sheaf.Paper.RegularImmersionSignedEvaluation
public import Sheaf.Paper.RegularImmersionCancellation
import Sheaf.Paper.PurityFiniteSetting
/-!
# Purity for regular closed immersions

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
thm-pur-regular-immersion-purity (blueprint: thm-pur-regular-immersion-purity).

All coefficients are the actual finite quotient of the fixed purity setting. Supported
classes use the published Hom model, and their restriction uses the section-normalized
closed coefficient exchange. The frame product is the existing ordered Kummer-boundary fold.

## Main declarations

* `regularImmersionPurity` and `regularPurityIso`: concentration and normalized purity.
* `regularFundamentalClass_etale` and `regularFundamentalClass_product`: compatibility.
* `regularCancelledPurityIso`: precisely the inverse of the twisted class isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Purity with its specified generator, concentration and free rank-one cohomology.
The equivalence regularSupportedEquiv is precisely the displayed equality of H^0 with
supported H^(2c), in the published supported-Hom convention. In particular the last
clause concerns the transpose of the unique frame-normalized class, not an arbitrary
isomorphism between two rank-one objects.
Source: blueprint main-20261015, thm-pur-regular-immersion-purity
(blueprint: thm-pur-regular-immersion-purity).
Proof, following the four steps of the node:
1. Apply clause (a) of sk-thm-regular in the identical finite coefficient setting
   def-pur-conventions/sk-def-purity-conv. It gives concentration, rank one and the
   supported-cohomology adjunction regularSupportedEquiv. No ramification divisibility
   is needed and regularity allows the empty sequence at c=0.
2. Its frame class is exactly def-pur-frame-class: each individual divisor contributes
   its own Kummer boundary at exponent ell^n, followed by the ordered supported cup.
   The root-to-twist insertion is the same projection-induced insertion; both empty
   products are the unit. Clause (b), or lem-pur-frame-independence followed by the
   degree-zero sheaf axiom, identifies its class with regularFundamentalClass.
3. Clause (c) makes its transpose regularFundamentalClassMap an isomorphism. It takes
   1 to the class just identified. Applying H^0 identifies the target with the
   constant coefficient module, so the sheaf is free of rank one.
4. Clause (d) supplies the etale and exterior-product identities stated below;
   since the generator and its transpose are the same, these are the compatibilities
   of this very isomorphism. Twisting by (-c)[-2c] and inverting gives the equivalent
   cancelled form, with that direction. -/
theorem regularImmersionPurity (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    P.RegularFrameNormalization i aX c (P.regularFundamentalClass i aX c hi hZ) ∧
      (∀ (r : ℤ), r ≠ 0 →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((P.regularExceptional i aX).obj (P.regularTate X c)))) ∧
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((P.regularExceptional i aX).obj (P.regularTate X c)) ≅ P.constant Z) ∧
      IsIso (P.regularFundamentalClassMap i aX c hi hZ) := by
  sorry

/-- The canonical purity isomorphism with its frame-normalized hom component.
Source: the displayed cl_i (blueprint: thm-pur-regular-immersion-purity). -/
def regularPurityIso (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :=
  @asIso _ _ _ _ (P.regularFundamentalClassMap i aX c hi hZ)
    (P.regularImmersionPurity i aX c hi hZ).2.2.2

/-- After every etale base change the restricted global class is precisely the
unique frame-normalized class of the new pair. This formulation also allows etale
neighbourhoods which are not quasi-compact or separated: their supported class and
its local normalization are defined without an exceptional functor on that neighbourhood.
Source: the final sentence, etale compatibility
(blueprint: thm-pur-regular-immersion-purity).
Proof: sk-thm-regular(d) pulls frames back to frames; Kummer classes, each boundary
and the supported cup commute with restriction. Frame independence and sheaf gluing
identify the resulting class. This is the actual supported pullback because its closed
coefficient exchange is the adjunction mate normalized on local constants. -/
theorem regularFundamentalClass_etale (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    {D Y : Scheme.{u}} (v : Y ⟶ X) [Etale v] (j : D ⟶ Y) [IsClosedImmersion j]
    (g : D ⟶ Z) (sq : IsPullback g j i v)
    (δ : cupSupportedHom P j ((cupSingle P Y).obj (P.frameTwist Y c)) (2 * (c : ℤ))) :
    P.RegularFrameNormalization j (v ≫ aX) c δ ↔
      δ = P.regularSupportedPullback i j v g sq aX c
        (P.regularFundamentalClass i aX c hi hZ) := by
  sorry

/-- The product is again a regular pair of the sum codimension, and its normalized
fundamental class is exactly the exterior product of the original classes. Quantifying
over a candidate class states its unique characterization without choosing any further
orientation or assuming regularity of the product as extra data.
Source: sk-thm-regular(d), exterior-product compatibility
(blueprint: thm-pur-regular-immersion-purity).
Proof: sk-thm-regular(d) applies lem-pur-product-regular-sequence to affine regular
frames; their concatenation is a regular frame of length c+d. Smoothness of both
factors and their regular closed subschemes over the perfect field implies smoothness,
hence regularity, of the product closed subscheme. On product frames the ordered
boundary fold is the supported exterior product, by lem-pur-exterior-product-frame
and Kunneth with supports. Frame independence and uniqueness of gluing identify the
global classes. Empty frames give the unit and all degrees are even, so no permutation
sign is introduced. This is Step 4 of the item, applying clause (d) of sk-thm-regular. -/
theorem regularFundamentalClass_product (P : PurityFiniteSetting.{u})
    {X Y Z W : Scheme.{u}} (a : X ⟶ Spec (.of P.field.k)) (b : Y ⟶ Spec (.of P.field.k))
    [IsSeparated a] [QuasiCompact a] [Smooth a]
    [IsSeparated b] [QuasiCompact b] [Smooth b]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] (c d : ℕ)
    (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hj : PurityConventions.IsRegularOfPureCodimension j d)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (hW : ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) :
    PurityConventions.IsRegularOfPureCodimension
        (Etale.supportedProductImmersion a b i j) (c + d) ∧
      (∀ z : ↥(pullback (i ≫ a) (j ≫ b) : Scheme.{u}),
        IsRegularLocalRing ((pullback (i ≫ a) (j ≫ b)).presheaf.stalk z)) ∧
      ∀ ε : cupSupportedHom P (Etale.supportedProductImmersion a b i j)
          ((cupSingle P (pullback a b)).obj (P.frameTwist (pullback a b) (c + d)))
          (2 * ((c + d : ℕ) : ℤ)),
        P.RegularFrameNormalization (Etale.supportedProductImmersion a b i j)
            (pullback.fst a b ≫ a) (c + d) ε ↔
          ε = P.regularExteriorClass a b i j c d
            (P.regularFundamentalClass i a c hi hZ) (P.regularFundamentalClass j b d hj hW) := by
  sorry

/-- The normalized class isomorphism has the native cancellation carrier.
Source: the displayed class isomorphism
(blueprint: thm-pur-regular-immersion-purity).
Proof: unfold both Iso carriers, regularPurityIso and regularFundamentalClassMap.
They have identical constant-single source and exceptional shifted-Tate target. -/
theorem regularPurityIsoType_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    (type_of% (P.regularPurityIso i aX c hi hZ)) =
      regularCancellationClassType (ModuleCat.{u + 1} P.Coefficient) Z
        ((P.regularSingle Z).obj (P.constant Z))
        ((P.regularExceptional i aX).obj (P.regularTate X c)) := by
  sorry

/-- The identical normalized class isomorphism in the native cancellation carrier.
Source: inverse twisting of the displayed class isomorphism
(blueprint: thm-pur-regular-immersion-purity). -/
def regularCancellationClass (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    regularCancellationClassType (ModuleCat.{u + 1} P.Coefficient) Z
      ((P.regularSingle Z).obj (P.constant Z))
      ((P.regularExceptional i aX).obj (P.regularTate X c)) :=
  cast (P.regularPurityIsoType_eq i aX c hi hZ) (P.regularPurityIso i aX c hi hZ)

/-- Ri! A_X is canonically A_Z(-c)[-2c]: this is exactly the inverse of cl_i tensor
the negative shifted line, with the counit-normalized cancellation comparison.
The expression fixes the inverse direction and the same generator as the frame class.
Source: the equivalent displayed purity isomorphism
(blueprint: thm-pur-regular-immersion-purity). -/
def regularCancelledPurityIso (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :=
  @regularCancelledIsoGeneral (ModuleCat.{u + 1} P.Coefficient)
    _ _ _ _ _ _ _ _ Z
    ((P.regularExceptional i aX).obj (P.regularTate X c))
    (P.regularTate Z (-(c : ℤ)))
    ((P.regularExceptional i aX).obj ((P.regularSingle X).obj (P.constant X)))
    ((P.regularSingle Z).obj (P.constant Z))
    (P.regularCancellation i aX c) (P.regularCancellationClass i aX c hi hZ)
    (P.regularCancellationUnitIso Z c)

end WeilConjectures.PurityFiniteSetting
