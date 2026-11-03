/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs

/-! Invertibility of one normalized exchange component.
(blueprint: new-p3-qcqs-exchange-component)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 300000 in
-- The four factors have the native ordinary derived-category endpoints.
private theorem componentIsIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (c : Compactification f) (K : C ℓ X) :
    IsIso (exchangeComponent ℓ S a b sq c K) := by
  have h : IsIso (CompactificationReindexing.squareExchange
      (Profinite.padicAlgClRingObj ℓ)
      (c := c) (c' := c.ofIsPullback sq) (w := a.hom) (v := b.hom)
      { middle := pullback.fst c.g b.hom
        openSquare := c.isPullback_i_ofIsPullback sq
        properSquare := (c.isPullback_g_ofIsPullback sq).flip.toCommSq }) :=
    (CompactificationReindexing.square_isIso
      (Λ := Profinite.padicAlgClRingObj ℓ)
      (c := c) (c' := c.ofIsPullback sq) (w := a.hom) (v := b.hom)
      { middle := pullback.fst c.g b.hom
        openSquare := c.isPullback_i_ofIsPullback sq
        properSquare := (c.isPullback_g_ofIsPullback sq).flip.toCommSq }
      sq.toCommSq).2
  have : IsIso (exchangeTransformation ℓ S a b sq c) := by
    unfold exchangeTransformation
    let := h
    infer_instance
  unfold exchangeComponent
  infer_instance

@[irreducible] private def constructibleExchangeIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (c : Compactification f) :
    S.support ℓ c ⋙ pull ℓ b ≅ pull ℓ a ⋙ S.support ℓ c :=
  NatIso.ofComponents (fun K ↦ by
    letI := componentIsIso ℓ S a b sq c K
    exact (bc ℓ Y).isoMk (asIso (exchangeComponent ℓ S a b sq c K))) (by
      intro K L t
      apply ObjectProperty.hom_ext
      change _ ≫ exchangeComponent ℓ S a b sq c L =
        exchangeComponent ℓ S a b sq c K ≫ _
      simpa only [Functor.comp_map, ObjectProperty.ι_map, exchangeComponent] using
        (exchangeTransformation ℓ S a b sq c).naturality t)

private theorem constructibleExchangeIso_normalized
    {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (c : Compactification f) (K : C ℓ X) :
    (((constructibleExchangeIso ℓ S a b sq c).hom.app K).hom) =
      exchangeComponent ℓ S a b sq c K := by
  unfold constructibleExchangeIso
  rfl

/-- The specified proper/open exchange component along an automorphism square is a natural
isomorphism on every compactification, so it forms an `Exchange`.
Source: Stacks Tag 0F7J, lemma-shriek-composition (base change of the compactification along
the square); latest blueprint lem-fix-weil-operations.proof, paragraph 1 (the exchange for an
automorphism square is invertible) (blueprint: new-p3-qcqs-exchange-component).

Proof: fix a compactification `c` and put `iso c` with components `exchangeComponent`.
Naturality in `K`: every factor of `exchangeComponent` is the component at `K` of a natural
transformation (the exact-to-total pullback identifications, the proper/open square exchange,
`Rc_!` of the second identification, and the system comparison). Invertibility: the two
pullback identifications and the system comparison are isomorphisms; the square exchange is
an isomorphism by `CompactificationReindexing.square_isIso`, since `a` and `b` are isomorphisms
and so is the middle map `pullback.fst c.g b.hom`. Then `normalized` holds by construction. -/
theorem qcqsExchangeComponentExists
    {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom) :
    Nonempty (Exchange ℓ S a b sq) := by
  exact ⟨{ iso := constructibleExchangeIso ℓ S a b sq
           normalized := constructibleExchangeIso_normalized ℓ S a b sq }⟩
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
