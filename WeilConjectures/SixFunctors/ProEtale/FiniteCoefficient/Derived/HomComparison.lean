/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!

# Tor amplitude and internal hom under the pro-étale comparison

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites and `ν^*` the induced exact functor
`D(X_ét) ⥤ D(X_proét)`. This file records how `ν^*` interacts with the finite Tor amplitude and
with the internal hom of bounded constructible complexes at a finite coefficient ring `Λ`.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`
  (`lem-exc-comparison-tor-interval`): an étale complex has Tor amplitude in `[a, b]` if and only
  if its pullback to the pro-étale site has.
- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`
  (`lem-exc-comparison-tor-interval` (ii)): an étale complex whose pullback to the pro-étale
  site has Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`
  (`thm-sf-hom-comparison-constructible`): `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)` for `K` in
  `Dctf(X_ét, Λ)` and `M` in `Dᵇc(X_ét, Λ)`, on a finite-type scheme over `k = F̄_p`, glued from
  the separated case
  `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`
  (`lem-weil-finite-duality-site-comparison`).

## Implementation notes

The canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` needs a monoidal structure
on the derived `ν^*` compatible with the internal homs, which is not formalised (only the
tensor comparison `CategoryTheory.Functor.leftDerivedTensorComparison` is);
the comparison is therefore stated as the existence of an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The derived comparison pullback `ν^*` sends the monoidal unit `Λ_{X_ét}` of `D(X_ét)` to
the monoidal unit `Λ_X` of `D(X_proét)`. -/
noncomputable def mapDerivedCategoryComparisonUpperStarUnitIso (X : Scheme.{u}) :
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅ 𝟙_ _ :=
  D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso Λ X) ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

end DerivedCategory

/-- `Rν_*` sends the monoidal unit `Λ` of `D(X_proét, Λ)` to the monoidal unit `Λ` of
`D(X_ét, Λ)`: the pro-étale unit is `ν^*` of the étale unit
(`DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso`), and the unit
`M ⟶ Rν_* ν^* M` of the comparison adjunction is invertible on the bounded below `M = Λ`
(`isIso_derivedComparisonAdjunction_unit_app`). -/
noncomputable def rightDerivedComparisonLowerStarUnitIso (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  haveI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X (𝟙_ _)
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  (R(ν_*(X)[ModuleCat.{u + 1} Λ])).mapIso
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso Λ X).symm ≪≫
    (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app (𝟙_ _))).symm

namespace DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- Blueprint `lem-exc-comparison-tor-interval`: Finite Tor amplitude under the site
comparison, clause (i).

If a complex `K'` of étale `Λ`-sheaves has Tor amplitude in `[a, b]`, then `ν^* K'` has Tor
amplitude in `[a, b]` on the pro-étale site: a flat model of `K'` in degrees `[a, b]` is carried
by the exact functor `ν^*` to a flat model of `ν^* K'`, as `ν^*` preserves flat sheaves
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`). The blueprint's hypotheses that
`K'` be bounded constructible and that the exponent of `Λ` be invertible on `X` are not
needed. -/
theorem torAmplitudeIn_mapDerivedCategory {X : Scheme.{u}} [IsNoetherianRing Λ]
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K') :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj _ hKt

omit [Finite Λ] in
/-- Blueprint `lem-exc-comparison-tor-interval`: Finite Tor amplitude under the site
comparison, clause (i).

The derived comparison pullback `ν^*` carries `Dctf(X_ét, Λ)` into `Dctf(X_proét, Λ)`. -/
theorem constructibleFiniteTor_mapDerivedCategory {X : Scheme.{u}} [IsNoetherianRing Λ]
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K') :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') :=
  have ⟨hbc, a, b, hKt⟩ := hK'
  ⟨boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hbc, a, b,
    torAmplitudeIn_mapDerivedCategory Λ hKt⟩

variable {Λ} in
omit [Finite Λ] in
/-- Blueprint `lem-exc-comparison-tor-interval`: Site comparison preserves and detects Tor
intervals.

Let `K` be a complex of étale sheaves of `Λ`-modules. Then `K` has Tor amplitude in `[a, b]` if
and only if its pullback `ν^* K` to the pro-étale site has. The pullback is exact, faithful and
strong monoidal, and it preserves flat sheaves
(`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`), so this is
`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff`. The blueprint's hypothesis that `K`
be bounded below is not needed. -/
theorem torAmplitudeIn_mapDerivedCategory_iff {X : Scheme.{u}} [IsNoetherianRing Λ] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) ↔
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K :=
  _root_.DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff _ a b K

omit [Finite Λ] in
/-- Blueprint `lem-exc-comparison-tor-interval`: Finite Tor amplitude under the site
comparison, clause (ii).

Let `K'` be a complex of étale `Λ`-sheaves. If `ν^* K'` has Tor amplitude in `[a, b]` on
`X_proét`, then `K'` has Tor amplitude in `[a, b]` on the étale site.
This is the reverse implication of `torAmplitudeIn_mapDerivedCategory_iff`; the blueprint's
hypotheses that `K'` be bounded below, that `ν^* K'` be bounded constructible and that the
exponent of `Λ` be invertible on `X` are not needed. -/
theorem torAmplitudeIn_of_mapDerivedCategory {X : Scheme.{u}} [IsNoetherianRing Λ]
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) :
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K' :=
  (torAmplitudeIn_mapDerivedCategory_iff a b K').1 hKt

/-- The étale-origin step of blueprint `lem-weil-finite-duality-site-comparison`: for `X`
separated of finite type over an algebraic closure `k` of `𝔽_p`, `K ∈ Dctf(X_ét, Λ)` and
`M ∈ Dᵇc(X_ét, Λ)`, the pro-étale complex `RHom(ν^* K, ν^* M)` is of étale origin: the counit
`ν^* Rν_* R ⟶ R` of the comparison adjunction is an isomorphism at `R = RHom(ν^* K, ν^* M)`. -/
theorem isIso_derivedComparisonAdjunction_counit_app_derivedHom {k : Type u} [Field k]
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M))) :=
  sorry

/-- Blueprint `lem-weil-finite-duality-site-comparison`: Finite-stage duality under the site
comparison.

Let `X` be a separated scheme of finite type over an algebraic closure `k` of `𝔽_p`, let `Λ` be
a finite ring whose exponent is invertible on `X`, and let `ν : X_proét ⟶ X_ét` be the site
comparison.

1. For `K ∈ Dctf(X_ét, Λ)` and `M ∈ Dᵇc(X_ét, Λ)`, `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)`.
2. Moreover `ν^* ω_X ≅ ω_{X, proét}` for the dualizing complexes `Ra_X^! Λ` of the two sites.
3. These comparisons identify the Verdier duals and the double-dual maps: for
   `K ∈ Dctf(X_ét, Λ)`, `ν^* 𝔻_X K ≅ 𝔻_{X, proét} (ν^* K)`, and `ν^* K ≅ 𝔻 𝔻 (ν^* K)` on the
   pro-étale site. In particular finite-stage Verdier duality on the pro-étale constructible
   category is transported from étale Verdier duality.

The blueprint asserts that canonical comparison maps are isomorphisms. The map
`ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` is the adjoint of
`ν^* RHom(K, M) ⊗ᴸ ν^* K ≅ ν^* (RHom(K, M) ⊗ᴸ K) ⟶ ν^* M`, built from
`CategoryTheory.Functor.leftDerivedTensorComparison` of `ν^*` and the evaluation;
constructing it and proving it is an isomorphism is left to the subsection of this node. Here
the existence of isomorphisms is stated, and the identification of evaluations and double-dual
maps is rendered as clause 3. Clauses 2 and 3 are stated whenever the exceptional inverse image
along `a_X` defining the dualizing complexes is available. -/
theorem nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated {k : Type u} [Field k]
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [HasInvertibleExponent Λ X] :
    (∀ {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M →
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
          (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
        ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
          (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
            (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M))) ∧
    ∀ [HasCompactification aX],
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
          (Etale.dualizingComplex Λ aX) ≅
        ProEtale.dualizingComplex Λ aX) ∧
      ∀ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
            ((Etale.verdierDual Λ aX).obj (op K)) ≅
          (ProEtale.verdierDual Λ aX).obj
            (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))) ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K ≅
          (ProEtale.verdierDual Λ aX).obj
            (op ((ProEtale.verdierDual Λ aX).obj
              (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))))) := by
  have : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  -- clause 1: `RHom(ν^* K, ν^* M)` is of étale origin, and `Rν_*` of it is `RHom(K, M)`
  have h₁ {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
      (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
          (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
        ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
          (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
            (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) := by
    let adj := derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X
    obtain ⟨c, hc⟩ := hM.1.1
    have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X M ⟨c, hc⟩
    have := isIso_derivedComparisonAdjunction_counit_app_derivedHom Λ aX (p := p) hK hM
    exact ⟨(D(ν^*(X)[ModuleCat.{u + 1} Λ])).mapIso
      (((rightDerivedComparisonLowerStarCompDerivedHomIso (ModuleCat.{u + 1} Λ) K).app _).symm ≪≫
        ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).mapIso
          (asIso (adj.unit.app M)).symm).symm ≪≫ asIso (adj.counit.app _)⟩
  refine ⟨h₁, ?_⟩
  intro _
  -- clause 2: the pro-étale `Ra_X^!` is `ν^* ∘ a_X^× ∘ Rν_*`, and `Rν_* Λ ≅ Λ`
  let e₂ : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (Etale.dualizingComplex Λ aX) ≅
      ProEtale.dualizingComplex Λ aX :=
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso ((Etale.rightDerivedUpperShriek Λ aX).mapIso
      (rightDerivedComparisonLowerStarUnitIso (Spec (.of k)) Λ).symm)
  -- the étale inputs: `ω_X` is bounded constructible, and Verdier biduality on `Dctf`
  have hX : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (Etale.dualizingComplex Λ aX) ∧
      ∀ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
          ((Etale.verdierDual Λ aX).obj (op K)) ∧
        Nonempty (K ≅ (Etale.verdierDual Λ aX).obj (op ((Etale.verdierDual Λ aX).obj (op K)))) := by
    by_cases hne : Nonempty X
    · have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
      have hΛ : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k))
          (𝟙_ _) :=
        ⟨(Etale.DerivedCategory.boundedConstructible _ _).prop_of_iso
            (_root_.DerivedCategory.singleFunctorObjUnitIso _)
            (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
          (Etale.DerivedCategory.torAmplitudeIn _ _ 0 0).prop_of_iso
            (_root_.DerivedCategory.singleFunctorObjUnitIso _)
            (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
              (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
      exact ⟨(Etale.constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aX hΛ).1,
        fun hK ↦ ⟨Etale.constructibleFiniteTor_verdierDual Λ aX hK,
          Etale.nonempty_iso_verdierDual_verdierDual Λ aX hK⟩⟩
    · have : IsEmpty X := not_nonempty_iff.1 hne
      have hz := Etale.isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) X
      exact ⟨ObjectProperty.prop_of_isZero _ (hz _), fun _ ↦
        ⟨ObjectProperty.prop_of_isZero _ (hz _), ⟨(hz _).iso (hz _)⟩⟩⟩
  -- clause 3: clause 1 for `M = ω_X`, followed by clause 2
  have h₃ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj ((Etale.verdierDual Λ aX).obj (op K)) ≅
        (ProEtale.verdierDual Λ aX).obj (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))) :=
    have ⟨e⟩ := h₁ hK hX.1
    ⟨e ≪≫ ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj _).mapIso e₂⟩
  refine ⟨⟨e₂⟩, fun hK ↦ ⟨h₃ hK, ?_⟩⟩
  -- clause 4: transport étale biduality along clause 3, applied to `K` and to `𝔻_X K`
  obtain ⟨hDK, ⟨b⟩⟩ := hX.2 hK
  obtain ⟨e⟩ := h₃ hK
  obtain ⟨e'⟩ := h₃ hDK
  exact ⟨D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso b ≪≫ e' ≪≫
    (ProEtale.verdierDual Λ aX).mapIso e.op.symm⟩

/-- Blueprint `thm-sf-hom-comparison-constructible`: Internal-Hom comparison for finite-Tor
constructible inputs.

Let `X` be a scheme of finite type over an algebraic closure `k` of `𝔽_p`, let `Λ` be a finite
ring whose exponent is invertible on `X`, let `K ∈ Dctf(X_ét, Λ)` and `M ∈ Dᵇc(X_ét, Λ)`. Then
`ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)`.

The assertion is local on `X`, and on the separated affine opens of a finite cover it is
`lem-weil-finite-duality-site-comparison`, stated as
`ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`.
The local isomorphisms are glued through the comparison adjunction: write
`R = RHom(ν^* K, ν^* M)`. By the projection formula for `ν`
(`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarCompDerivedHomIso`) and full
faithfulness of `ν^*` on bounded below complexes, `Rν_* R ≅ RHom(K, Rν_* ν^* M) ≅ RHom(K, M)`,
which is bounded below. On each member `U` of the cover, `R|_U ≅ RHom(ν^* K|_U, ν^* M|_U)` is of
étale origin, so `R` is of étale origin
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_counit_app_of_openCover`), and
`ν^* RHom(K, M) ≅ ν^* Rν_* R ≅ R`. -/
theorem nonempty_iso_mapDerivedCategory_derivedHom {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) ≅
      ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)) := by
  let adj := derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X
  let R := ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj
    (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))).obj (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)
  obtain ⟨b, hb⟩ := hK.1.1.2
  obtain ⟨c, hc⟩ := hM.1.1
  -- `Rν_* R ≅ RHom(K, Rν_* ν^* M) ≅ RHom(K, M)`
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X M ⟨c, hc⟩
  let e₁ : (R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj R ≅
      ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M :=
    ((rightDerivedComparisonLowerStarCompDerivedHomIso (ModuleCat.{u + 1} Λ) K).app _).symm ≪≫
      ((Etale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).mapIso (asIso (adj.unit.app M)).symm
  -- which is bounded below
  have hR : _root_.DerivedCategory.TStructure.t.plus ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj R) :=
    have := _root_.DerivedCategory.isGE_obj_of_adjunction
      (Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K) M b c
    ⟨c - b, _root_.DerivedCategory.TStructure.t.isGE_of_iso e₁.symm _⟩
  -- a finite cover by affine opens
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : t → X.Opens := fun V ↦ V.1.1
  have hU : ∀ x, ∃ i, x ∈ U i := fun x ↦ by
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨V, hV⟩, hx⟩
  -- on each member of the cover, `R` is of étale origin
  have hloc (i : t) : ∃ N : _root_.DerivedCategory
      (Sheaf (U i : Scheme.{u}).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R ≅
        D(ν^*(U i)[ModuleCat.{u + 1} Λ]).obj N) := by
    have : IsAffine (U i) := i.1.2
    let j := (U i).ι
    have : LocallyOfFiniteType (j ≫ aX) := inferInstance
    have : QuasiCompact (j ≫ aX) := inferInstance
    have : IsSeparated (j ≫ aX) := inferInstance
    have : HasInvertibleExponent Λ (U i) := HasInvertibleExponent.of_hom j
    obtain ⟨e₂⟩ := ProEtale.nonempty_iso_mapDerivedCategory_upperStar_derivedHom
      (ModuleCat.{u + 1} Λ) j (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K)
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M)
    let eK := (mapDerivedCategoryComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).app K
    let eM := (mapDerivedCategoryComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).app M
    obtain ⟨e₃⟩ := (nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated Λ (j ≫ aX)
      (p := p)).1 (Etale.constructibleFiniteTor_mapDerivedCategory_upperStar Λ j hK)
      (hM.mapDerivedCategory_upperStar j)
    exact ⟨_, ⟨e₂ ≪≫ ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) (U i)).mapIso eK.op.symm).app _ ≪≫
      ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) (U i)).obj _).mapIso eM ≪≫ e₃.symm⟩⟩
  have := isIso_derivedComparisonAdjunction_counit_app_of_openCover (ModuleCat.{u + 1} Λ) U hU R
    hR hloc
  exact ⟨(D(ν^*(X)[ModuleCat.{u + 1} Λ])).mapIso e₁.symm ≪≫ asIso (adj.counit.app R)⟩

end AlgebraicGeometry.ProEtale.DerivedCategory
