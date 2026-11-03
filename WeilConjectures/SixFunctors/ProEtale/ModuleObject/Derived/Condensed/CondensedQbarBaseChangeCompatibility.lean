/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeEquality
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeLeftAdjunct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeRightAdjunct

/-!
# Condensed finite-to-algebraic-closure coefficient change and exchange

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, final transport paragraph;
`ModuleObject/ChangeOfCoefficients.lean`, Derived section
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility).

The coefficient ring is the finite-subextension-valued continuous-function ring
`Profinite.padicAlgClRingObj`, not the full continuous-function ring. All categories below
are the published bounded constructible full subcategories, without a completeness condition.
The pull and push comparisons are restrictions of the specified ambient comparisons.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- Keep the ambient mate folded while restricting its component to the full subcategory.
attribute [local irreducible] derivedPushHom

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Square

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

private theorem p3Archive_lifted_inv_naturality (α : l ⋙ tD ≅ tC ⋙ l')
    {K M : PC.FullSubcategory} (v : K ⟶ M) :
    (PF.lift (PE.ι ⋙ l') hl').map ((PE.lift (PC.ι ⋙ tC) htC).map v) ≫
        (PF.isoMk (α.app M.obj)).inv =
      (PF.isoMk (α.app K.obj)).inv ≫
        (PF.lift (PD.ι ⋙ tD) htD).map ((PD.lift (PC.ι ⋙ l) hl).map v) := by
  exact ObjectProperty.hom_ext _ (α.inv.naturality v.hom)

private theorem p3Archive_right_normalization (ε : r ⋙ l ⟶ 𝟭 B) (ε' : r' ⋙ l' ⟶ 𝟭 D)
    (q : ∀ U, l'.obj (tA.obj U) ⟶ tB.obj (l.obj U))
    (hn : ∀ {U V : A} (v : U ⟶ V), l'.map (tA.map v) ≫ q V =
      q U ≫ tB.map (l.map v))
    {U : A} {W : B} {V : D} (β : U ⟶ r.obj W) (δ : tA.obj (r.obj W) ⟶ r'.obj (tB.obj W))
    (α : tB.obj W ⟶ V)
    (hδ : l'.map δ ≫ ε'.app (tB.obj W) = q (r.obj W) ≫ tB.map (ε.app W)) :
    l'.map (tA.map β ≫ (δ ≫ r'.map α)) ≫ ε'.app V =
      q U ≫ tB.map (l.map β ≫ ε.app W) ≫ α := by
  have he := ε'.naturality α
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at he
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [he]
  slice_lhs 2 3 => rw [hδ]
  slice_lhs 1 2 => rw [hn β]
  simp only [Category.assoc]

private theorem p3Archive_pull_inv_naturality {K M : PadicSubfieldConstructible U ℓ E}
    (v : K ⟶ M) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).map
        ((constructibleToPadicAlgCl U ℓ E).map v) ≫
      (constructibleToQbarPullIso ℓ k E h M).inv =
    (constructibleToQbarPullIso ℓ k E h K).inv ≫
      (constructibleToPadicAlgCl T ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k)))).map v) := by
  exact p3Archive_lifted_inv_naturality _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h) v

-- Matching the goal against `lifted_push_counit` must compare these terms by their arguments;
-- unfolding them reaches compositions in the derived categories (about 30 s of unification).

/-- Scalar extension's push comparison satisfies the mate counit identity.
Source: ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean, iterated_mateEquiv_conjugateEquiv_symm
and mateEquiv_counit (blueprint: lem-weil-pbc-qbar-condensed-push-counit).

Proof in words. The two coefficient extension/restriction adjunctions and the two
geometric pullback/pushforward adjunctions form a square. Iterated mate cancellation
identifies pushHomOfComapIso with the mate of inverse pullIsoOfComapIso. Apply the
mate counit equation at the underlying object K. Fully faithful restriction to
bounded constructible objects preserves counits, and its inclusion is faithful,
so the ambient equation gives exactly the displayed restricted equation. -/
private theorem p3Archive_constructibleToQbar_push_counit (K : PadicSubfieldConstructible T ℓ E) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj.{u} ℓ) ℓ
        (h.asOver (Spec (.of k)))).map
        (constructibleToQbarPushHom ℓ k E h K) ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h.asOver (Spec (.of k)))).counit.app
            ((constructibleToPadicAlgCl T ℓ E).obj K) =
      (constructibleToQbarPullIso ℓ k E h
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
            (h.asOver (Spec (.of k)))).obj K)).inv ≫
        (constructibleToPadicAlgCl T ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
              (h.asOver (Spec (.of k)))).counit.app K) := by
  exact lifted_push_counit _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ (h.asOver (Spec (.of k))) K)
    _ _
    (fun K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E
      (h.asOver (Spec (.of k))) K)
    (fun K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ (h.asOver (Spec (.of k))) K)
    _ _ _ K

/-- Normalization of the right side of coefficient exchange under the pullback adjunction.
Source: ModuleObject/Colimit/TwoColimit.lean, final transport paragraph;
ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean
(blueprint: lem-weil-pbc-qbar-condensed-exchange-right-adjunct).

Proof in words. Expand the target comparison and functoriality of pullback. Naturality of the
Omega pullback/pushforward counit moves alpha_g' to the right of that counit. The adjunct
of the push comparison for f' is inverse alpha_f' at its E pushforward followed by scalar
extension of the E counit. Indeed pushHomOfComapIso is the mate of inverse
pullIsoOfComapIso, by iterated mate/conjugation cancellation. Restriction along the fully
faithful constructible inclusions preserves this counit identity. Naturality of inverse
alpha_f' at the E base-change morphism moves that morphism across inverse alpha_f'.
Finally scalar-extension functoriality combines its pullback and the E counit. This is the
displayed middle expression. This step uses no coefficient square coherence, and applies
to any morphism with the type of the E base-change component. Thus it is independent of the
left-side normalization. Identity and zero morphisms satisfy the same naturality laws. -/
private theorem p3Archive_constructibleToQbar_exchange_right_adjunct_legacy
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
      ((constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
              (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f'.asOver (Spec (.of k)))).counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              (g'.asOver (Spec (.of k)))).obj
            ((constructibleToPadicAlgCl X ℓ E).obj K)) =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g.asOver (Spec (.of k)))).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
              (f.asOver (Spec (.of k)))).obj K))).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (f'.asOver (Spec (.of k)))).map
            ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
                (sq.asOver (Spec (.of k)))).app K) ≫
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
              (f'.asOver (Spec (.of k)))).counit.app
              ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
                  (g'.asOver (Spec (.of k)))).obj K)) ≫
      (constructibleToQbarPullIso ℓ k E g' K).hom := by
  dsimp only [constructibleToQbarTargetHom]
  exact p3Archive_right_normalization
    (l := boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (f'.asOver (Spec (.of k))))
    (r := ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E (f'.asOver (Spec (.of k))))
    (l' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k))))
    (r' := boundedConstructibleLowerStar ℓ (f'.asOver (Spec (.of k))))
    (tA := constructibleToPadicAlgCl Y' ℓ E)
    (tB := constructibleToPadicAlgCl X' ℓ E)
    (U := (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (g.asOver (Spec (.of k)))).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E (f.asOver (Spec (.of k)))).obj K))
    (W := (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
      (g'.asOver (Spec (.of k)))).obj K)
    (V := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (g'.asOver (Spec (.of k)))).obj ((constructibleToPadicAlgCl X ℓ E).obj K))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
        (f'.asOver (Spec (.of k)))).counit
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (f'.asOver (Spec (.of k)))).counit
    (fun U ↦ (constructibleToQbarPullIso ℓ k E f' U).inv)
    (fun v ↦ p3Archive_pull_inv_naturality ℓ k E f' v)
    ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k)))).app K)
    (constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K))
    (constructibleToQbarPullIso ℓ k E g' K).hom
    (p3Archive_constructibleToQbar_push_counit ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K))

/-- Coefficient extension respects the specified unit-square-counit exchange arrow.
Source: `ModuleObject/Colimit/TwoColimit.lean`, final transport paragraph;
`ModuleObject/ChangeOfCoefficients.lean`, Derived section; mate pasting in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`
(blueprint: lem-weil-pbc-qbar-condensed-exchange-equality).

Proof in words. Write T for scalar extension, l_h for derived pullback, r_h for derived
pushforward, α_h: T l_h,E ≅ l_h,Ω T for the pull comparison, and δ_h: T r_h,E → r_h,Ω T
for the push comparison. By their definitions from the same restriction/direct-image
isomorphism, δ_h is the mate of α_h inverse along the two pull/push adjunctions. This follows
by expanding pullIsoOfComapIso and pushHomOfComapIso: conjugation is the mate correspondence
for the composite adjunctions, and the two successive transpositions cancel. In particular,
the adjunct of δ_h at K is α_h inverse at r_h,E(K), followed by T of the E-counit.

The α comparisons respect composition of scheme morphisms. At the underived module level,
both composites are induced by the identical associativity map on inverse images and the
balanced tensor map b ⊗ (a ⊗ m) ↦ ba ⊗ m. The coefficient square commutes by naturality of
the coefficient map. This gives equality of natural transformations by the tensor and
sheafification universal properties. Exact pullback and flat scalar extension compute their
derived functors termwise; restriction preserves K-injectives since its left adjoint is
exact. Thus the same coherence descends through localization and agrees with the derived
comparisons defined by conjugation. The composition comparisons are the derived ones used
in boundedConstructiblePullbackSquareComparison, rather than newly chosen comparisons.

Let θ_A: l_f',A l_g,A ≅ l_g',A l_f,A be the square comparison. Coherence gives the following
commuting diagram, suppressing object arguments and the canonical associators:
T(θ_E), then α_g', then l_g',Ω(α_f) equals α_f', then l_f',Ω(α_g), then θ_Ω(T).
Both routes start at T l_f',E l_g,E and end at l_g',Ω l_f,Ω T. The equality also respects
the commutativity proof in the square: substitution by equal morphisms is natural, and
proof irrelevance identifies proofs of that equality.

Take mates of this equality along l_f,E ⊣ r_f,E and l_f',E ⊣ r_f',E, and along the analogous
Ω-adjunctions. Mate pasting preserves equality and composition (mateEquiv_hcomp and
mateEquiv_vcomp, equivalently mateEquiv_square). The mate of θ_A is exactly the specified
exchange B_A: expanding the mate is unit insertion, square transport, then counit contraction.
The edge mates are δ_f and δ_f', by the first paragraph. Thus the resulting equality is
B_Ω(T(K)) ∘ l_g,Ω(δ_f(K)) ∘ α_g(r_f,E(K)) =
r_f',Ω(α_g'(K)) ∘ δ_f'(l_g',E(K)) ∘ T(B_E(K)), exactly the asserted formula.
The bounded constructible adjunction and square comparison are restrictions along fully
faithful inclusions, which preserve the displayed units, counits, and composition constraints.
Neither δ nor B is
inverted; properness and Cartesianity are unnecessary. -/
theorem constructibleToQbar_exchange_equality_legacy
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl X ℓ E).obj K) =
      (constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective
  exact (constructibleToQbar_exchange_left_adjunct ℓ k E f g f' g' sq K).trans
    (p3Archive_constructibleToQbar_exchange_right_adjunct_legacy ℓ k E f g f' g' sq K).symm

/-- Restriction of the bounded-below comparison to a bounded constructible input. -/
private theorem constructibleToQbarPushHom_isIso_of_isProper [IsProper f]
    (K : PadicSubfieldConstructible X ℓ E) :
    IsIso (constructibleToQbarPushHom ℓ k E f K) := by
  obtain ⟨N, hN⟩ := K.property.1.1
  have : K.obj.IsGE N := hN
  exact (ObjectProperty.isIso_hom_iff
    (P := boundedConstructible (padicAlgClRingObj Y ℓ))
    (constructibleToQbarPushHom ℓ k E f K)).mp
    (isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE.{u}
      ℓ f E K.obj N)

/-- Proper finite-to-Qbar coefficient change preserves the specified exchange arrow.
Source: TwoColimit.lean, final transport paragraph; ChangeOfCoefficients.lean, Derived section
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility).

Proof: the chosen pullback makes f' proper. Extract a cohomological lower bound from
each bounded constructible input and apply
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`. That theorem combines
the scalar-basis decomposition with copower continuity in these same internal condensed
module categories (`lem-weil-pbc-condensed-subfield-bounded-copowers`). Transfer each
component through `ObjectProperty.isIso_hom_iff` to the constructible full subcategory.
The source and target comparisons are composites of these push isomorphisms with the
published pull isomorphisms, so both are invertible. Finally apply the separately stated
`constructibleToQbar_exchange_equality` to the specified square and input; it identifies
exactly the displayed arrows without assuming either exchange transformation invertible. -/
theorem constructibleToQbar_baseChange_compatibility [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) :
    (∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f K)) ∧
    (∀ K : PadicSubfieldConstructible X' ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f' K)) ∧
    (∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarSourceHom ℓ k E f g K) ∧
      IsIso (constructibleToQbarTargetHom ℓ k E f' g' K) ∧
      constructibleToQbarSourceHom ℓ k E f g K ≫
          (boundedConstructibleBaseChange ℓ (sq.toCommSq.asOver (Spec (.of k)))).app
            ((constructibleToPadicAlgCl X ℓ E).obj K) =
        (constructibleToPadicAlgCl Y' ℓ E).map
            ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
              (sq.toCommSq.asOver (Spec (.of k)))).app K) ≫
          constructibleToQbarTargetHom ℓ k E f' g' K) := by
  have : IsProper f' := by
    rw [← sq.hom_snd]
    infer_instance
  have hpush : ∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f K) :=
    constructibleToQbarPushHom_isIso_of_isProper ℓ k E f
  have hpush' : ∀ K : PadicSubfieldConstructible X' ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f' K) :=
    constructibleToQbarPushHom_isIso_of_isProper ℓ k E f'
  refine ⟨hpush, hpush', ?_⟩
  intro K
  have := hpush K
  have : IsIso (constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
        (g'.asOver (Spec (.of k)))).obj K)) :=
    hpush' _
  constructor
  · dsimp [constructibleToQbarSourceHom]
    infer_instance
  constructor
  · dsimp [constructibleToQbarTargetHom]
    infer_instance
  · exact constructibleToQbar_exchange_equality_legacy ℓ k E f g f' g' sq.toCommSq K

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
