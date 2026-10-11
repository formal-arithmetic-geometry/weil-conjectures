/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# Stability of `Dctf`: direct image and internal hom

For torsion coefficients `Λ` with invertible exponent and schemes of finite type over a field,
this file proves that the direct image `Rf_*`, the compactly supported direct image `Rf_!` and
the internal hom preserve the bounded constructible complexes, with the shifts of the Tor
amplitude recorded by the blueprint.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Torsion coefficients with invertible exponent

The statements of this section are the ones of `sk-thm-sf-direct-image-tor-amplitude`,
`sk-thm-sf-hom-ctf`, `sk-prop-sf-rf-shriek-preservation` (ii)–(iv) and
`sk-thm-sf-ctf-stability` (iii), (v), (vi) whose content is a bound on étale cohomological
dimension, a constructibility theorem for direct images or purity. They are made in the setting
of `sk-def-sf-setting`: the coefficients are a finite ring `Λ` whose exponent is invertible on
the schemes in sight, and the schemes are of finite type over a field `k`. Neither hypothesis
can be dropped: for `Λ = 𝔽_p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite (Artin–Schreier),
so `Rf_*` of the constant sheaf along `𝔸¹ ⟶ Spec 𝔽̄_p` is not constructible; and over a
general Noetherian base étale cohomology need not vanish above twice the dimension. -/

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-! #### Direct image -/

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes, and let `K` be a bounded constructible
complex on `X_ét` killed by an integer `N` invertible on `Y`. Then `Rf_* K` is bounded
constructible on `Y_ét`. The coefficients are noetherian: subobjects of finitely generated
objects of `A` are finitely generated (`CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`,
which holds for `ModuleCat Λ` with `Λ` noetherian).

Each hypothesis is needed. Without torsion the statement fails, `H³(ℙ¹, ℤ)` containing
`ℚ_ℓ/ℤ_ℓ`; without the noetherian hypothesis it fails for a rank-one local system on `𝔾_m` with
stalk `𝔽_ℓ[x, y₁, y₂, …]/(xˡ, x yᵢ)` and monodromy `1 + x`, whose `H⁰` is the non-finitely
generated annihilator of `x`; and for `N = p` on `𝔸¹` over `𝔽̄_p`, `H¹(𝔸¹, 𝔽_p)` is infinite
(Artin–Schreier). -/
theorem boundedConstructible_rightDerivedLowerStar [ConcreteCategory.FinitelyGeneratedOfMono A]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (N : ℕ) [NeZero N]
    (hN : N • 𝟙 K = 0) (hNY : IsUnit (N : Γ(Y, ⊤))) (hbc : boundedConstructible A X K) :
    boundedConstructible A Y ((R((f)_*[A])).obj K) :=
  sorry

/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude.

Let `f : X ⟶ Y` be a separated morphism of finite-type `k`-schemes with `dim X ≤ d`, and let `K`
be a bounded constructible complex on `X_ét` of Tor amplitude in `[a, b]`, killed by an integer
`N` invertible on `Y`. Then `Rf_* K` has Tor amplitude in `[a, b + 2d]`. The shift `2d` is the
uniform vanishing of `Rᵖf_*` above twice the dimension of the source. The coefficients are as in
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`. -/
theorem torAmplitudeIn_rightDerivedLowerStar [ConcreteCategory.FinitelyGeneratedOfMono A]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
    [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (N : ℕ) [NeZero N]
    (hN : N • 𝟙 K = 0) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hbc : boundedConstructible A X K) (hta : torAmplitudeIn A X a b K) :
    torAmplitudeIn A Y a (b + 2 * (d : ℤ)) ((R((f)_*[A])).obj K) :=
  sorry

omit [Finite Λ] in
/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility.

For a finite `Λ` whose exponent is invertible on `Y` and a morphism `f : X ⟶ Y` of finite-type
`k`-schemes, `Rf_*` preserves bounded constructibility. This is the finite-coefficient case of
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`, and is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
once `f` is known to be quasi-compact. -/
theorem boundedConstructible_rightDerivedLowerStar_of_finite [Finite Λ] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hbc : boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    boundedConstructible (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : QuasiCompact f := by
    subst hf
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    exact QuasiCompact.of_comp f aY
  have : HasInvertibleExponent Λ X := HasInvertibleExponent.of_hom f
  exact boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ f aX aY hf K hbc

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iii): `Rf_* : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` is defined for every separated morphism of
finite-type `k`-schemes, for a finite `Λ` whose exponent is invertible on `Y`. It is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_finite` together with
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`, a finite-type `k`-scheme being
finite dimensional. -/
theorem constructibleFiniteTor_rightDerivedLowerStar {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hbc, a, b, hta⟩ := hK
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  obtain ⟨N, hN0, hNΛ, hNY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := Y)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ K
  have : IsNoetherianRing Λ := inferInstance
  exact ⟨boundedConstructible_rightDerivedLowerStar_of_finite Λ aX aY f hf hbc, a, b + 2 * (d : ℤ),
    torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N hN hNY hbc hta⟩

/-- Blueprint `sk-thm-sf-ctf-stability`: Stability of the constructible finite-Tor
subcategories.

Clause (iv): `Rf_! : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` is defined for every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, for a finite `Λ` whose exponent
is invertible on `Y`. For the chosen compactification `X ⟶[j] Z ⟶[g] Y` of `f`, `Rf_!` is
`Rg_* ∘ j_!`; extension by zero preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`)
and so does the direct image along the proper `g`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`).

Some finiteness hypothesis on `Y` is needed: for `f : ⊔ₙ ℙⁿ_ℂ ⟶ ⊔ₙ Spec ℂ`, which is proper,
`Rf_! Λ` has `H²ⁿ ≠ 0` on the `n`-th point, so it is not bounded. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  let c := HasCompactification.compactification f
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨hbc, a, b, hta⟩ := hK
  have h := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ c.i a b
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
  exact constructibleFiniteTor_rightDerivedLowerStar Λ (c.g ≫ aY) aY c.g rfl ⟨h.1.1, a, b, h.2⟩

/-! #### Internal hom -/

omit [Finite Λ] in
/-- Constructibility of a sheaf of modules is local for a finite open cover of a scheme whose
underlying space is noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.isConstructibleSheaf_of_openCover :
    ∀ (n : ℕ) {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : Fin n → X.Opens) (_ : ∀ x, ∃ i, x ∈ U i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    (∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj F)) →
      IsConstructibleSheaf F := by
  intro n
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := ⟨fun x ↦ by obtain ⟨i, -⟩ := hU x; exact i.elim0⟩
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  | succ n ih =>
    intro X _ U hU F h
    have : TopologicalSpace.NoetherianSpace (U 0) :=
      (U 0).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact (U 0).ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    rw [Scheme.isConstructibleSheaf_iff_upperStar (U 0).ι (U 0).closedComplement (by simp)]
    refine ⟨h 0, ?_⟩
    let i := (U 0).closedComplement
    have : TopologicalSpace.NoetherianSpace _ := i.isClosedEmbedding.isInducing.noetherianSpace
    refine ih (fun k ↦ i ⁻¹ᵁ U k.succ) (fun z ↦ ?_) _ (fun k ↦ ?_)
    · have hz : i.base z ∉ U 0 := by
        have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
        rwa [(U 0).range_closedComplement] at this
      obtain ⟨k, hk⟩ := hU (i.base z)
      obtain ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k |>.resolve_left (by rintro rfl; exact hz hk)
      exact ⟨k, hk⟩
    · have := h k.succ
      have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) (i ∣_ U k.succ)).obj F) :=
        IsConstructibleSheaf.upperStar (i ∣_ U k.succ)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U k.succ).ι).obj F)
      exact IsConstructibleSheaf.of_iso
        (((Etale.upperStarComp _ (i ∣_ U k.succ) (U k.succ).ι).app F).symm ≪≫
          eqToIso (by rw [morphismRestrict_ι]) ≪≫
          (Etale.upperStarComp _ (i ⁻¹ᵁ U k.succ).ι i).app F)

open ZeroObject in
omit [Finite Λ] in
/-- A bounded complex whose restrictions to the members of a finite open cover of a noetherian
space are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openCover {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, boundedConstructible (ModuleCat.{u + 1} Λ) (U i)
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X R := by
  -- homology commutes with the restrictions
  have e (i : Fin n) (q : ℤ) :=
    ((((U i).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app R
  refine ⟨?_, fun q ↦ ?_⟩
  · choose c d hcd using fun i ↦
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 (h i).1
    -- a zero sheaf is detected on the cover
    have hz (q : ℤ) (hq : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R))) :
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj R) := by
      have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
        (ι := ULift.{u} (Fin n)) (fun i ↦ (U i.down).ι)
        (fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
        (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0) (fun i ↦
          isIso_of_source_target_iso_zero _ ((hq i.down).of_iso (e i.down q)).isoZero
            (Functor.map_isZero _ (isZero_zero _)).isoZero)
      exact (isZero_zero _).of_iso
        (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj R ⟶ 0))
    refine (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded R).1
      ⟨-∑ i, |c i|, ∑ i, |d i|, ?_, ?_⟩
    · refine (_root_.DerivedCategory.isGE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isGE_iff _ (c i)).1 (hcd i).1 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |c i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := neg_abs_le (c i)
      omega
    · refine (_root_.DerivedCategory.isLE_iff R _).2 fun q hq ↦ hz q fun i ↦
        (_root_.DerivedCategory.isLE_iff _ (d i)).1 (hcd i).2 q ?_
      have := Finset.single_le_sum (f := fun i ↦ |d i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)
      have := le_abs_self (d i)
      omega
  · refine Scheme.isConstructibleSheaf_of_openCover Λ n U hU _ fun i ↦ ?_
    have : IsConstructibleSheaf ((D(((U i).ι)^*[ModuleCat.{u + 1} Λ]) ⋙
        _root_.DerivedCategory.homologyFunctor _ q).obj R) := (h i).2 q
    exact IsConstructibleSheaf.of_iso (e i q).symm

omit [Finite Λ] in
/-- A complex of finite Tor amplitude with bounded constructible homology restricts to one along
a pullback. -/
lemma constructibleFiniteTor_mapDerivedCategory_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (D((f)^*[ModuleCat.{u + 1} Λ]).obj N) := by
  obtain ⟨hbc, c, d, hcd⟩ := hN
  exact ⟨hbc.mapDerivedCategory_upperStar f, c, d,
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app N)
      (torAmplitudeIn_leftDerivedUpperStar _ f c d hcd)⟩

section DerivedHom

variable {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X] (m : ℕ) (hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
  (a b c d : ℤ)
  {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}

include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

For `X` of finite type over `k`, a finite `Λ` whose exponent is invertible on `X` and bounded
constructible `K` and `M` on `X_ét` of finite Tor amplitude, the internal hom `RHom(K, M)` is
bounded constructible. -/
theorem boundedConstructible_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact boundedConstructible_of_openCover Λ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine boundedConstructible_of_openCover Λ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  exact (boundedConstructible _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_verdierDual _ aU
      (constructibleFiniteTor_verdierDual Λ aU) (nonempty_iso_verdierDual_verdierDual Λ aU)
      (constructibleFiniteTor_tensor Λ _)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hK, a, b, hKt⟩)
      (constructibleFiniteTor_mapDerivedCategory_upperStar Λ _ ⟨hM, c, d, hMt⟩)).1

include aX hm in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If `K` and `M` have Tor amplitude in `[a, b]` and `[c, d]` and `dim X ≤ m`, then `RHom(K, M)`
has Tor amplitude in `[c - b - 2m, d - a + 2m]`. The blueprint derives this from
`RHom(K, M) ≅ 𝔻_X (K ⊗ᴸ 𝔻_X M)`, the dualizing complex having cohomology in `[-2m, 0]`. The
statement is local on `X`, and on the separated affine opens it is
`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_isSeparated`
(`cor-weil-finite-constructible-hom`). -/
theorem torAmplitudeIn_derivedHom
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  by_cases hX : IsEmpty X
  · exact torAmplitudeIn_of_openCover _ (n := 0) Fin.elim0
      (fun x ↦ (hX.false x).elim) _ (fun i ↦ i.elim0)
  rw [not_isEmpty_iff] at hX
  have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
  -- a finite cover by affine opens
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens ↦ (V : Set X))
    (fun V ↦ V.1.isOpen) (fun x _ ↦ by
      obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let U : Fin t.card → X.Opens := fun i ↦ (t.equivFin.symm i).1.1
  refine torAmplitudeIn_of_openCover _ U (fun x ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨V, hV⟩, by simpa [U] using hx⟩
  have : IsAffine (U i) := (t.equivFin.symm i).1.2
  let aU := (U i).ι ≫ aX
  have hmU : topologicalKrullDim (U i) ≤ (m : WithBot ℕ∞) :=
    ((U i).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hm
  obtain ⟨e⟩ := nonempty_iso_mapDerivedCategory_upperStar_derivedHom _ (U i).ι K M
  have hKt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) a b).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app K)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι a b hKt)
  have hMt' : torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d
      (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj M) :=
    (torAmplitudeIn (ModuleCat.{u + 1} Λ) (U i) c d).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ (U i).ι).app M)
      (torAmplitudeIn_leftDerivedUpperStar _ (U i).ι c d hMt)
  exact (torAmplitudeIn _ _ _ _).prop_of_iso e.symm
    (constructibleFiniteTor_derivedHom_of_isSeparated (Λ := Λ) (a := aU) m hmU
      (hK.mapDerivedCategory_upperStar (U i).ι) hKt'
      (hM.mapDerivedCategory_upperStar (U i).ι) hMt').2

-- `aX` and the coefficient hypotheses are part of the blueprint setting, unused by the proof
set_option linter.unusedSectionVars false in
include aX in
/-- Blueprint `sk-thm-sf-hom-ctf`: Internal Hom with finite Tor amplitude.

If moreover `K` is dualizable, the sharper interval `[c - b, d - a]` holds, from the local
identification `RHom(K, M) ≅ K^∨ ⊗ᴸ M`. It genuinely fails in general: for the origin
`i : {0} ⟶ 𝔸¹` both `i_* Λ` and `Λ` have Tor amplitude `[0, 0]` while
`RHom(i_* Λ, Λ) = i_* Λ(-1)[-2]`. -/
theorem torAmplitudeIn_derivedHom_of_isDualizable
    (_hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (_hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M)
    (hMt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X c d M) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (c - b) (d - a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) :=
  torAmplitudeIn_derivedHom_of_isDualizable_aux _ hKt hKd hMt

include aX in
/-- Blueprint `lem-sf-ext-sheaf-constructible`: Constructible internal Hom with a site-perfect
first variable.

If `K ∈ Dctf(X, Λ)` is site-perfect, that is dualizable, and `M` is bounded constructible, then
`RHom(K, M)` is bounded constructible; in particular every cohomology sheaf of `RHom(K, M)` is
constructible. Indeed `RHom(K, M) ≅ K^∨ ⊗ᴸ M`, where the coefficient dual `K^∨ = RHom(K, Λ)` is
bounded constructible (`AlgebraicGeometry.Etale.boundedConstructible_derivedHom`) of Tor
amplitude `[-b, -a]`, and the tensor product of two bounded constructible complexes, one of
them of finite Tor amplitude, is bounded constructible. -/
theorem boundedConstructible_derivedHom_of_isDualizable
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj M) := by
  -- the unit `Λ_X` is bounded constructible of Tor amplitude `[0, 0]`
  have hU : boundedConstructible (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
    (boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0)
  have hUt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0 (𝟙_ _) :=
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  have hD : boundedConstructible (ModuleCat.{u + 1} Λ) X ((coefficientDual _ X).obj (op K)) :=
    boundedConstructible_derivedHom Λ aX a b 0 0 hK hKt hU hUt
  obtain ⟨_⟩ := hKd
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  have hDt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b) (-a)
      ((coefficientDual _ X).obj (op K)) :=
    (torAmplitudeIn _ X _ _).prop_of_iso (coefficientDualIsoOfExactPairing Kᘁ K).symm
      (_root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt)
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor (isDualizable_of_hasRightDual K) M
  -- `K^∨ ⊗ᴸ M` is bounded, `K^∨` having finite Tor amplitude, with constructible homology
  obtain ⟨c', d', hcd⟩ :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded M).2 hM.1
  have : IsNoetherianRing Λ := inferInstance
  have hb : _root_.DerivedCategory.TStructure.t.bounded
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((coefficientDual _ X).obj (op K))).obj M) :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
      ⟨_, _,
        _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hDt hcd⟩
  have hc := constructibleHomology_derivedTensor _ (fun F G hF hG n ↦ by
      have := (Etale.constructibleSheaf_iff _ _ _).mp hF
      have := (Etale.constructibleSheaf_iff _ _ _).mp hG
      exact (Etale.constructibleSheaf_iff _ _ _).mpr
        (isConstructibleSheaf_homology_tensor_singleFunctor Λ F G n)) hD hM
  exact (boundedConstructible _ X).prop_of_iso e ⟨hb, hc⟩

omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- If `K` is dualizable of Tor amplitude in `[a, b]`, then `RHom(K, G[0]) ≅ K^∨ ⊗ᴸ G[0]` is
concentrated in `[-b, -a]` for every sheaf `G`, the dual `K^∨` having Tor amplitude in
`[-b, -a]`. -/
theorem homologyConcentratedIn_derivedHom_singleFunctor_of_isDualizable
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (hKd : IsDualizable K)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    _root_.DerivedCategory.homologyConcentratedIn (-b) (-a)
      (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  have h : _root_.DerivedCategory.homologyConcentratedIn (-b) (-a)
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((coefficientDual _ X).obj (op K))).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
    obtain ⟨_⟩ := hKd
    obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
    have := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := Kᘁ) hKt
    exact (torAmplitudeIn _ X _ _).prop_of_iso
      (coefficientDualIsoOfExactPairing Kᘁ K).symm this G
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hKd
    ((_root_.DerivedCategory.singleFunctor _ 0).obj G)
  exact homologyConcentratedIn_of_iso _ e h

include aX in
/-- Blueprint `lem-sf-ext-sheaf-constructible`: Constructible internal Hom with a site-perfect
first variable.

For a finite locally free sheaf `F`, that is a constructible flat sheaf which is dualizable in
`D(X_ét, Λ)`, and a constructible sheaf `G`, the sheaves `𝓔xtʳ(F, G) = Hʳ RHom(F, G)` vanish
for `r ≠ 0`, and `𝓗om(F, G) = H⁰ RHom(F, G)` is constructible: `RHom(F, G)` is bounded
constructible and concentrated in degree `0`. Indeed `RHom(F, G) ≅ F^∨ ⊗ᴸ G` with `F^∨` of Tor
amplitude `[0, 0]`. -/
theorem boundedConstructible_derivedHom_singleFunctor_of_isDualizable
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] (hF : ObjectProperty.flat F)
    (hFd : IsDualizable ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 0
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  have hFt := _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hF
  refine ⟨boundedConstructible_derivedHom_of_isDualizable Λ aX 0 0
    (boundedConstructible_singleFunctor_obj F 0) hFt hFd
    (boundedConstructible_singleFunctor_obj G 0), ?_⟩
  exact homologyConcentratedIn_derivedHom_singleFunctor_of_isDualizable Λ 0 0 hFt hFd G

end DerivedHom

end Torsion

end Etale

end AlgebraicGeometry
