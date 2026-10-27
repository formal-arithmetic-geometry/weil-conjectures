/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.SixFunctorDatum

/-! # Identity support comparisons and normalized mates

These are the unchanged definitions formerly in IdentificationCoefficientTransport.
They are shared by its normalization lemmas and its formal adjunction calculation.
Source: the normalized trace paragraph of the identification proof
(blueprint: def-sf-identity-coefficient-transport-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The canonical identity compactification at the geometric point.
Source: the identity compactification in the node's first paragraph
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfPointIdentityCompactification (D : FiniteFieldDatum.{u}) :
    Compactification (𝟙 (Spec.{u} (.of D.k))) :=
  Compactification.ofIsProper (𝟙 (Spec.{u} (.of D.k)))

/-- Equality transport of a compactified support functor.
Source: coherent identifications in thm-sf-comp-composition
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfSupportEquality {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) {X Y : SixFunctorSpace D}
    (f g : X ⟶ Y) (h : f = g) (c : Compactification f.hom.left) :
    S.support g (h ▸ c) ≅ S.support f c := by
  subst g
  exact Iso.refl _

/-- The specified support compositor with the identity composite transported to a.
Source: thm-sf-comp-composition and fix-lem-exchanges (2),(4)
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityComposition {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :
    S.support (sixFunctorStructure X) c ⋙
      S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        S.support (sixFunctorStructure X) c :=
  (S.composition (sixFunctorStructure X) (𝟙 (sixFunctorPoint D)) c
    (sfPointIdentityCompactification D)
    ((Category.comp_id (sixFunctorStructure X)).symm ▸ c)).symm ≪≫
      sfSupportEquality S (sixFunctorStructure X)
        (sixFunctorStructure X ≫ 𝟙 (sixFunctorPoint D))
        (Category.comp_id (sixFunctorStructure X)).symm c

/-- The specified compact-support compositor is the identity unitor on every
bounded constructible input. This condition contains no assertion about right mates.
Source: the identity clause of thm-sf-comp-composition and the completed identity
comparison in fix-lem-exchanges (blueprint: def-sf-identity-coefficient-transport-data). -/
def SfIdentityCompositionLaw {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B)
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _) : Prop :=
  ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) (K : B X),
    (sfIdentityComposition S X c).hom.app K =
      v.hom.app ((S.support (sixFunctorStructure X) c).obj K)

/-- The identity-normalized counit, e composed with the inverse of v at J L.
Source: the displayed definition of nu
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityNormalizedCounit {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :=
  v.inv.app ((S.exceptional (𝟙 (sixFunctorPoint D))
    (sfPointIdentityCompactification D)).obj L) ≫
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).counit.app L

/-- The inverse right mate, using the pasted composite adjunction and alpha inverse.
Source: the definition of c and the conjugation convention
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfIdentityTransportMate {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  conjugateIsoEquiv
    ((S.exceptionalAdjunction (sixFunctorStructure X) c).comp
      (S.exceptionalAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)))
    (S.exceptionalAdjunction (sixFunctorStructure X) c)
    (sfIdentityComposition S X c).symm

/-- The compositor normalization and the three conclusions at one coefficient stage.
The counit equation is an equality of actual morphisms.
Source: the two displayed equations and isomorphism clauses
(blueprint: lem-sf-identification-coefficient-transport). -/
structure SfIdentityStageLaws {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (P : ∀ X, B X → Prop)
    (L : B (sixFunctorPoint D))
    (v : S.support (𝟙 (sixFunctorPoint D))
      (sfPointIdentityCompactification D) ≅ 𝟭 _) : Prop where
  composition_identity : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left)
    (K : B X), P X K →
    (sfIdentityComposition S X c).hom.app K =
      v.hom.app ((S.support (sixFunctorStructure X) c).obj K)
  normalized_counit_iso : IsIso (sfIdentityNormalizedCounit S L v)
  mate_iso : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    IsIso ((sfIdentityTransportMate S X c).hom.app L)
  mate_is_normalized_counit : ∀ (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] (c : Compactification (sixFunctorStructure X).hom.left),
    (sfIdentityTransportMate S X c).hom.app L =
      (S.exceptional (sixFunctorStructure X) c).map (sfIdentityNormalizedCounit S L v)
  counit_equation : ∀ (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left),
    (S.support (sixFunctorStructure X) c).map
        ((sfIdentityTransportMate S X c).hom.app L) ≫
      (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app L =
    (S.exceptionalAdjunction (sixFunctorStructure X) c).counit.app
        ((S.exceptional (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D)).obj L) ≫
      sfIdentityNormalizedCounit S L v

/-- Coefficient transport of the identity comparison through the supplied support square.
For integral reduction that square is normalized by the actual Roos projections; for
localization and common stages it is the specified scalar comparison.
Source: fix-lem-exchanges (2),(4), and reduction/limit unit projection normalization
(blueprint: lem-sf-identification-coefficient-transport). -/
def SfIdentityChange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B₁ : SixFunctorSpace D → Type v₁} [∀ X, Category.{w₁} (B₁ X)]
    {S : SixFunctorPushStage D B} {S₁ : SixFunctorPushStage D B₁}
    {F : ∀ X, B X ⥤ B₁ X} (Q : SixFunctorCoefficientComparison S S₁ F)
    (v : S.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _)
    (v₁ : S₁.support (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅ 𝟭 _) :
    Prop :=
  ∀ K : B (sixFunctorPoint D),
    (Q.supportAdjunction (𝟙 (sixFunctorPoint D))
        (sfPointIdentityCompactification D)).left.hom.app K ≫
      v₁.hom.app ((F (sixFunctorPoint D)).obj K) =
    (F (sixFunctorPoint D)).map (v.hom.app K)

/-- The finite identity comparison is the identity compactification, proper direct-image
identification, and the canonical direct-image identity, lifted through the full inclusion.
Source: finite identity compactification in thm-sf-comp-composition
(blueprint: lem-sf-identification-coefficient-transport). -/
def sfFiniteIdentityComparison
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorFiniteOperations D C E n hn) :
    (@SixFunctorPushStage.support.{u, u+2, u+2} D
      (sixFunctorFiniteCategory D C E n hn)
      (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
      S.finite) (𝟙 (sixFunctorPoint D)) (sfPointIdentityCompactification D) ≅
        Functor.id.{u+2, u+2} (sixFunctorFiniteCategory D C E n hn (sixFunctorPoint D)) :=
  ((intrinsicFiniteTorsionConstructible C.l E n hn
      (Spec (.of D.k))).fullyFaithfulι.{u+2, u+2}.whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight
        (@SixFunctorPushStage.properIdentity.{u, u+2, u+2} D
          (sixFunctorFiniteCategory D C E n hn)
          (fun X ↦ inferInstanceAs (Category.{u+2} (sixFunctorFiniteCategory D C E n hn X)))
          S.finite _ _ (𝟙 (sixFunctorPoint D)) inferInstance)
        (intrinsicFiniteTorsionConstructible C.l E n hn (Spec (.of D.k))).ι ≪≫
      S.finiteDirectImage (𝟙 (sixFunctorPoint D)) ≪≫
      Functor.isoWhiskerLeft _
        (@sixFunctorDirectIdentity (Padic.coefficientExtensionRing C.l E n) _
          (Padic.finite_coefficientExtensionRing C.l E n hn) (Spec (.of D.k))) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

end WeilConjectures
