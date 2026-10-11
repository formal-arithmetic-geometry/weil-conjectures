/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.Derived.Duality
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

/-!

# Tor amplitude and internal hom under the pro-étale comparison

Let `ν : X_proét ⥤ X_ét` be the comparison morphism of sites and `ν^*` the induced exact functor
`D(X_ét) ⥤ D(X_proét)`. This file records how `ν^*` interacts with the finite Tor amplitude and
with the internal hom of bounded constructible complexes at a finite coefficient ring `Λ`.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory`
  (`lem-sf-comparison-tor-amplitude` (ii)): an étale complex whose pullback to the pro-étale
  site is bounded constructible of Tor amplitude in `[a, b]` has Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom`
  (`thm-sf-hom-comparison-constructible`): `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)` for `K` in
  `Dctf(X_ét, Λ)` and `M` in `Dᵇc(X_ét, Λ)`, on a finite-type scheme over `k = F̄_p`, glued from
  the separated case
  `ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_isSeparated`
  (`lem-weil-finite-duality-site-comparison`).

## Implementation notes

The canonical comparison map `ν^* RHom(K, M) ⟶ RHom(ν^* K, ν^* M)` needs a monoidal structure
on the derived `ν^*` compatible with the internal homs, which is not formalised (only the
tensor comparison `AlgebraicGeometry.ProEtale.leftDerivedComparisonUpperStarTensorNatIso` is);
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

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (i).

Let `Λ` be a finite ring. If a complex `K'` of étale `Λ`-sheaves has Tor amplitude in
`[a, b]`, then `ν^* K'` has Tor amplitude in `[a, b]` on the pro-étale site: a flat model of
`K'` in degrees `[a, b]` is carried by the exact functor `ν^*` to a flat model of `ν^* K'`, as
`ν^*` preserves flat sheaves (`AlgebraicGeometry.ProEtale.flat_comparisonUpperStar_obj`). The
blueprint's hypotheses that `K'` be bounded constructible and that the exponent of `Λ` be
invertible on `X` are not needed. -/
theorem torAmplitudeIn_mapDerivedCategory {X : Scheme.{u}}
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hKt : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K') :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
    (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K').1 hKt
  exact (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b _).2
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomologicalComplex _).obj P, inferInstance, inferInstance,
      fun n ↦ flat_comparisonUpperStar_obj (hP n),
      ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactors.app P).symm ≪≫
        D(ν^*(X)[ModuleCat.{u + 1} Λ]).mapIso e⟩⟩

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (i).

The derived comparison pullback `ν^*` carries `Dctf(X_ét, Λ)` into `Dctf(X_proét, Λ)`, for a
finite ring `Λ`. -/
theorem constructibleFiniteTor_mapDerivedCategory {X : Scheme.{u}}
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K') :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K') :=
  have ⟨hbc, a, b, hKt⟩ := hK'
  ⟨boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hbc, a, b,
    torAmplitudeIn_mapDerivedCategory Λ hKt⟩

/-- Blueprint `lem-sf-comparison-tor-amplitude`: Finite Tor amplitude under the site
comparison, clause (ii).

Let `Λ` be a finite ring whose exponent is invertible on `X`, and let `K'` be a bounded below
complex of étale `Λ`-sheaves. If `ν^* K'` is bounded constructible on `X_proét` with Tor
amplitude in `[a, b]`, then `K'` has Tor amplitude in `[a, b]` on the étale site. -/
theorem torAmplitudeIn_of_mapDerivedCategory {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    {a b : ℤ} {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : _root_.DerivedCategory.TStructure.t.plus K')
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'))
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K')) :
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K' :=
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

The blueprint asserts that canonical comparison maps are isomorphisms; these maps need a
monoidal structure on `ν^*` compatible with the internal homs, which is not formalised, so the
existence of isomorphisms is stated, and the identification of evaluations and double-dual maps
is rendered as clause 3. Clauses 2 and 3 are stated whenever the exceptional inverse image
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
    ∀ [HasCompactification aX] [Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) aX],
      Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) aX) ≅
        ProEtale.dualizingComplex (ModuleCat.{u + 1} Λ) aX) ∧
      ∀ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj
            ((Etale.verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ≅
          (ProEtale.verdierDual (ModuleCat.{u + 1} Λ) aX).obj
            (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))) ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K ≅
          (ProEtale.verdierDual (ModuleCat.{u + 1} Λ) aX).obj
            (op ((ProEtale.verdierDual (ModuleCat.{u + 1} Λ) aX).obj
              (op (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K))))) :=
  sorry

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
