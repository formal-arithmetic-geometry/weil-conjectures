/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.WeilSheaf.NativeDerivedBaseChange
public import Sheaf.Paper.NativeModuleConstructibilityComparison
public import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.NativeScalarForgetting

/-! # Comparison of native exchange with the restricted condensed exchange

Source: blueprint thm-weil-pbc-qbar.proof.md, Constructibility and the isomorphism;
finite-span coefficient comparison and unit--square--counit normalization.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Scalar forgetting followed by the normalized ring-realization transport, before
section-ring presentation. The chosen isomorphisms form a single family normalized on
every finite-extension chart and natural in scheme maps.
Source: nativeModuleConstructibilityComparison.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
def nativeExchangeEncoding (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  AdicSheaf.forgetAb l X ⋙ Mod.comap (nativeModuleCoefficientIso l X).hom

/-- Scalar forgetting and transport are equivalences. Source: Stacks 03EK.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
@[instance] theorem nativeExchangeEncoding_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeExchangeEncoding l X).IsEquivalence := by
  have : (AdicSheaf.forgetAb l X).IsEquivalence :=
    nativeScalarForgetting_isEquivalence l X
  have : (Mod.comap (nativeModuleCoefficientIso l X).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (nativeModuleCoefficientIso l X).hom).isEquivalence_functor
  dsimp only [nativeExchangeEncoding]
  infer_instance

/-- Scalar transport leaves addition of underlying maps unchanged. Source: Stacks 03EK.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
@[instance] theorem nativeExchangeEncoding_additive (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeExchangeEncoding l X).Additive := by
  refine ⟨?_⟩
  intro M N f g
  rfl

attribute [irreducible] nativeExchangeEncoding

/-- The same real encoding, transported along a specified equality of bundled
coefficient rings. Equality fixes the multiplication as well as the underlying sheaf.
Source: normalized coefficient transport in nativeModuleConstructibilityComparison.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
def nativeExchangeEncodingAt (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    AdicSheaf l X ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X) :=
  hΛ.symm ▸ nativeExchangeEncoding l X

/-- Equality transport preserves the encoding equivalence. Source: Stacks 03EK.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
@[instance] theorem nativeExchangeEncodingAt_isEquivalence (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    (nativeExchangeEncodingAt l Λ hΛ X).IsEquivalence := by
  subst Λ
  change (nativeExchangeEncoding l X).IsEquivalence
  infer_instance

/-- Equality transport preserves additivity. Source: Stacks 03EK.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
@[instance] theorem nativeExchangeEncodingAt_additive (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    (nativeExchangeEncodingAt l Λ hΛ X).Additive := by
  subst Λ
  change (nativeExchangeEncoding l X).Additive
  infer_instance

attribute [irreducible] nativeExchangeEncodingAt

/-- The underlying arrow of a morphism in a full subcategory.
Source: the fully faithful inclusion of an object-property subcategory.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
def nativeUnderlyingExchangeArrow {C : Type*} [Category C] (P : ObjectProperty C)
    {A B : P.FullSubcategory} (f : A ⟶ B) : Arrow C :=
  Arrow.mk (P.ι.map f)

/-- The inclusion of a full subcategory preserves invertibility.
Source: functoriality of inverses.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison). -/
theorem nativeUnderlyingExchangeArrow_isIso {C : Type*} [Category C] (P : ObjectProperty C)
    {A B : P.FullSubcategory} (f : A ⟶ B) (hf : IsIso f) :
    IsIso (nativeUnderlyingExchangeArrow P f).hom := by
  let := hf
  change IsIso (P.ι.map f)
  infer_instance

attribute [irreducible] nativeUnderlyingExchangeArrow

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CondensedRing.boundedConstructibleBaseChangeOfPreserves
  upperStarFromPoint Functor.leftDerivedFunctor Mod.monoidalCategory
  CondensedRing.boundedConstructibleUpperStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  CondensedRing.boundedConstructibleUpperStarCompatibility
  CondensedRing.boundedConstructiblePullbackSquareComparison
  Functor.squareTransport Adjunction.restrictFullyFaithful

/-- The encoded native mate and the underlying restricted condensed mate are isomorphic
as arrows. No properness or native constructibility hypothesis enters this comparison.
Source: blueprint thm-weil-pbc-qbar.proof.md, Constructibility and the isomorphism;
finite-span comparison, steps 4--8; Stacks 09T5 and 070Y.
(blueprint: lem-sf-native-derived-exchange-condensed-comparison).

Proof: the normalized coefficient isomorphism identifies direct images by their
identity section maps. The inverse-image comparison is its adjunction conjugate.
Consequently the ordinary units, counits and pullback compositors are compatible.
Exact scalar transport preserves K-injectives, so these direct-image comparisons
localize on common K-injective representatives. The derived adjunction transpose is
the localization of the ordinary transpose. Use derivedPushComparison_unit on the
native K-injective models and derived_adjoint_square_comparison to compare the units
and counits. The theorem exchangeMate_cube then identifies encoding of the native
exchange with the exact-localization condensed exchange. Exact condensed inverse
image identifies its localization with its left derived functor. Finally the
bounded-constructible restricted adjunction is obtained by full faithful restriction:
its unit and counit are carried by the inclusion to the ambient unit and counit,
through the canonical push and pull compatibility isomorphisms. Pasting these
isomorphisms identifies the restricted unit--square--counit formula with the same
ambient exchange. Finally naturality in the input carries this comparison along e
from the encoded M to K.obj. Their composite is the required isomorphism of arrows. Transport
along hΛ first replaces the standard bundled coefficient by Λ; equality fixes all
ring data. This is valid for every Cartesian square and every input whose encoded
complex is identified with a bounded-constructible K; it asserts no invertibility
of either exchange. -/
theorem nativeDerivedExchange_condensed_comparison
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (K : BoundedConstructible (condensedRingObj Λ.X X.left))
    (e : (nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M ≅ K.obj) :
    Nonempty (Arrow.mk ((nativeExchangeEncodingAt l Λ hΛ Y'.left).mapDerivedCategory.map
        ((adicDerivedBaseChange l
          ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M)) ≅
      nativeUnderlyingExchangeArrow (boundedConstructible (condensedRingObj Λ.X Y'.left))
        ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
          (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
          sq.toCommSq).app K)) := by
  sorry

end AlgebraicGeometry.ProEtale
