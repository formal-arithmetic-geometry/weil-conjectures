/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationGeneric
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineSepClosed
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.StrictLocalizationStalk

/-!
# Geometric stalks of the direct images of `Λ(1)` from `𝔸¹` and `𝔾ₘ`

Let `B` be a scheme over a field `k`, `Λ` a finite ring whose exponent is invertible on `B`, and
`Λ(1) = μₙ ⊗ Λ` the Tate twist. For the projection `p : 𝔸¹_B ⟶ B` and the complement
`π : G ⟶ 𝔸¹_B ⟶ B` of the zero section, the stalks of `Rᵠp_* Λ(1)` and `Rᵠπ_* Λ(1)` at the
geometric point `x̄` of `B` over `x ∈ B` are the cohomology groups of `𝔸¹` and `𝔾ₘ` over the
strict henselization `𝒪^{sh}_{B,x̄}`
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_tateObject`).
This strict henselization maps to the strict henselization of `Spec k`, a separably closed field,
over which these cohomology groups are known
(`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineSepClosed`). Hence
`Rᵠp_* Λ(1)` has zero stalks for `q ≠ 0` and stalks of the cardinality of `Λ` for `q = 0`, and
`Rᵠπ_* Λ(1)` has zero stalks for `q ∉ {0, 1}` and stalks of the cardinality of `Λ` for
`q ∈ {0, 1}`. This is the reduction to a geometric fibre of the proof of `sk-prop-a1-kummer`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- The strict localization of a scheme `B` over a field `k` at a geometric point maps to the
spectrum of a separably closed field over `k`: the strict localization of `Spec k` at the image
point. -/
theorem Scheme.exists_isSepClosed_hom_strictLocalization {k : Type u} [Field k]
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of k)) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    ∃ (K : Type u) (_ : Field K) (_ : IsSepClosed K),
      Nonempty (strictLocalization s ⟶ Spec (.of K)) ∧ Nonempty (Spec (.of K) ⟶ Spec (.of k)) := by
  obtain ⟨φ, -⟩ := exists_strictHenselizationSchemeMap (g := aB) (s := s ≫ aB) (t := s) rfl
  obtain ⟨K, hK, hK', ⟨e⟩⟩ := exists_isSepClosed_strictLocalization_iso (s := s ≫ aB)
    (Ideal.eq_bot_of_prime _)
  exact ⟨K, hK, hK', ⟨φ ≫ e.hom⟩, ⟨e.inv ≫ strictLocalizationToBase _⟩⟩

/-- The complement of the zero section of `𝔸¹_S` is affine if `S` is: it is the basic open
`D(t)` of the coordinate. -/
lemma AffineSpace.isAffine_of_range_eq_compl_zeroSection' {S G : Scheme.{u}} [IsAffine S]
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); S)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ) :
    IsAffine G := by
  have : IsAffine (𝔸(ULift.{u} (Fin 1); S).basicOpen (AffineSpace.lineCoord S)) :=
    (isAffineOpen_top _).basicOpen _
  exact .of_isIso (IsOpenImmersion.isoOfRangeEq j
    (𝔸(ULift.{u} (Fin 1); S).basicOpen (AffineSpace.lineCoord S)).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (AffineSpace.opensRange_eq_basicOpen_lineCoord j hj))).hom

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]

/-- **Stalks of the direct image of `Λ(1)`.** For `f : Y ⟶ B` quasi-compact and quasi-separated,
a geometric point `s` of `B`, a cartesian square exhibiting `X₀ = Y ×_B B_(s)` with `X₀`
quasi-compact and quasi-separated, and a morphism from the strict localization `B_(s)` to the
spectrum of a separably closed field, the stalk at `s` of `Rᵠf_* Λ(1)` is `Hᵠ(X₀, Λ)`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_tateObject
    {Y B : Scheme.{u}} (f : Y ⟶ B) [QuasiCompact f] [QuasiSeparated f]
    [HasInvertibleExponent Λ Y] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ Y) (f₀ : X₀ ⟶ strictLocalization s)
    (sq : IsPullback p₀ f₀ f (strictLocalizationToBase s)) [CompactSpace X₀]
    [QuasiSeparatedSpace X₀] {K : Type u} [Field K] [IsSepClosed K]
    [HasInvertibleExponent Λ (Spec (.of K))] (g : strictLocalization s ⟶ Spec (.of K)) (q : ℕ) :
    Nonempty (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y 1))) ≃+
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((cohomology (ModuleCat.{u + 1} Λ) X₀ q).obj (constantComplex Λ X₀))) := by
  have : HasInvertibleExponent Λ X₀ := .of_hom p₀
  obtain ⟨L, -, -, ⟨eT⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) Y 1
  obtain ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isPullback f s
    p₀ f₀ sq L q
  obtain ⟨b⟩ := nonempty_cohomology_singleFunctor_iso_sheafH Λ X₀
    ((p₀)^*[ModuleCat.{u + 1} Λ].obj L) q
  obtain ⟨c⟩ := nonempty_tateTwistObject_one_iso_constantComplex_of_isSepClosed Λ (f₀ ≫ g)
  let d : (_root_.DerivedCategory.singleFunctor _ 0).obj ((p₀)^*[ModuleCat.{u + 1} Λ].obj L) ≅
      constantComplex Λ X₀ :=
    ((singleFunctorCompLeftDerivedUpperStarIso _ p₀).app L).symm ≪≫
      (L((p₀)^*[ModuleCat.{u + 1} Λ])).mapIso eT.symm ≪≫ leftDerivedUpperStarTateObjectIso p₀ 1 ≪≫ c
  let e₀ := ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso eT))
  exact ⟨e₀.toLinearEquiv.toAddEquiv.trans (a.trans (b.addCommGroupIsoToAddEquiv.symm.trans
    ((forget₂ _ _).mapIso ((cohomology _ X₀ q).mapIso d)).addCommGroupIsoToAddEquiv))⟩

/-- A `Λ`-module additively equivalent to the underlying group of a zero module is zero. -/
lemma isZero_of_addEquiv_forget₂ {M N : ModuleCat.{u + 1} Λ}
    (e : M ≃+ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N) (hN : IsZero N) :
    IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at hN ⊢
  exact e.toEquiv.subsingleton

/-- A `Λ`-module additively equivalent to the underlying group of `Λ` is finite of the
cardinality of `Λ`. -/
lemma finite_and_natCard_of_addEquiv_forget₂ {M N : ModuleCat.{u + 1} Λ}
    (e : M ≃+ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N)
    (eN : N ≅ ModuleCat.of Λ Λ) : Finite M ∧ Nat.card M = Nat.card Λ := by
  let e' : M ≃ Λ := e.toEquiv.trans eN.toLinearEquiv.toEquiv
  exact ⟨Finite.of_equiv _ e'.symm, Nat.card_congr e'⟩

variable {k : Type u} [Field k] {B : Scheme.{u}} (aB : B ⟶ Spec (.of k))
  [HasInvertibleExponent Λ B]

include aB in
/-- **The stalks of `Rᵠp_* Λ(1)` for the affine line `p : 𝔸¹_B ⟶ B`.** At every geometric point
`x̄` of `B`, the stalk of `Rᵠp_* Λ(1)` vanishes for `q ≠ 0`, and is finite of the cardinality of
`Λ` for `q = 0`. -/
theorem sheafFiber_homology_rightDerivedLowerStar_tateObject_affineLine (x : B) :
    (∀ q : ℕ, q ≠ 0 → IsZero (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) ∧
    (Finite (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
      Nat.card (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
          ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) = Nat.card Λ) := by
  let s := B.algClosurePoint x
  have : Nonempty B := ⟨x⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aB
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  obtain ⟨K, _, _, ⟨g⟩, ⟨c⟩⟩ := exists_isSepClosed_hom_strictLocalization aB s
  have : HasInvertibleExponent Λ (Spec (.of K)) := .of_hom c
  have key (q : ℕ) := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_tateObject Λ
    (𝔸(ULift.{u} (Fin 1); B) ↘ B) s _ _
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (strictLocalizationToBase s)) g q
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · obtain ⟨e⟩ := key q
    obtain ⟨e'⟩ := nonempty_cohomology_affineLine_iso Λ (A := ↑(strictHenselization s)) g q
    exact isZero_of_addEquiv_forget₂ Λ e
      ((isZero_cohomology_affineLine_of_isSepClosed Λ q (by exact_mod_cast hq)).of_iso e')
  · obtain ⟨e⟩ := key 0
    obtain ⟨e'⟩ := nonempty_cohomology_affineLine_iso Λ (A := ↑(strictHenselization s)) g 0
    exact finite_and_natCard_of_addEquiv_forget₂ Λ e
      (e' ≪≫ (nonempty_iso_cohomology_zero_affineLine_of_isSepClosed Λ (K := K)).some)

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); B)) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)

include aB hj in
/-- **The stalks of `Rᵠπ_* Λ(1)` for the complement `π : G ⟶ 𝔸¹_B ⟶ B` of the zero section.**
At every geometric point `x̄` of `B`, the stalk of `Rᵠπ_* Λ(1)` vanishes for `q ∉ {0, 1}`, and is
finite of the cardinality of `Λ` for `q ∈ {0, 1}`. -/
theorem sheafFiber_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup
    [HasInvertibleExponent Λ G] [QuasiCompact j] (x : B) :
    (∀ q : ℕ, q ≠ 0 → q ≠ 1 → IsZero (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ G 1))))) ∧
    (∀ q : ℕ, q ≤ 1 → Finite (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ G 1)))) ∧
      Nat.card (((pointSmallEtale (B.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((R((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ G 1)))) = Nat.card Λ) := by
  let s := B.algClosurePoint x
  let S' := strictLocalization s
  have : Nonempty B := ⟨x⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) := .of_hom_of_nonempty aB
  obtain ⟨K, _, _, ⟨g⟩, ⟨c⟩⟩ := exists_isSepClosed_hom_strictLocalization aB s
  have : HasInvertibleExponent Λ (Spec (.of K)) := .of_hom c
  let jK := (𝔸(ULift.{u} (Fin 1); Spec (.of K)).basicOpen
    (AffineSpace.coord (Spec (.of K)) (ULift.up 0))).ι
  have hjK := AffineSpace.range_basicOpen_ι_coord (Spec (.of K))
  let j' := pullback.snd j (AffineSpace.map (ULift.{u} (Fin 1)) (strictLocalizationToBase s))
  have hj' := AffineSpace.range_pullback_snd_map (strictLocalizationToBase s) j hj
  have : IsAffine (pullback j (AffineSpace.map (ULift.{u} (Fin 1))
      (strictLocalizationToBase s))) :=
    AffineSpace.isAffine_of_range_eq_compl_zeroSection' j' hj'
  have key (q : ℕ) := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_tateObject Λ
    (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) s _ _
    (AffineSpace.isPullback_complementMap_over (strictLocalizationToBase s) j j' hj hj') g q
  have hcoh (q : ℕ) := nonempty_cohomology_complement_iso Λ (A := ↑(strictHenselization s)) g
    jK hjK j' hj' q
  refine ⟨fun q hq₀ hq₁ ↦ ?_, fun q hq ↦ ?_⟩
  · obtain ⟨e⟩ := key q
    obtain ⟨e'⟩ := hcoh q
    exact isZero_of_addEquiv_forget₂ Λ e
      ((isZero_cohomology_multiplicativeGroup_of_isSepClosed Λ jK hjK q
        (by exact_mod_cast hq₀) (by exact_mod_cast hq₁)).of_iso e')
  · obtain ⟨e⟩ := key q
    obtain ⟨e'⟩ := hcoh q
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of K)) :=
      .of_hom (𝔸(ULift.{u} (Fin 1); Spec (.of K)) ↘ Spec (.of K))
    have : HasInvertibleExponent Λ (𝔸(ULift.{u} (Fin 1); Spec (.of K)).basicOpen
        (AffineSpace.coord (Spec (.of K)) (ULift.up 0))) := .of_hom jK
    obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact finite_and_natCard_of_addEquiv_forget₂ Λ e
        (e' ≪≫ (nonempty_iso_cohomology_zero_multiplicativeGroup_of_isSepClosed Λ jK hjK).some)
    · exact finite_and_natCard_of_addEquiv_forget₂ Λ e
        (e' ≪≫ (nonempty_iso_cohomology_one_multiplicativeGroup_of_isSepClosed Λ jK hjK).some)

end Etale

end AlgebraicGeometry
