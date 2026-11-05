/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne

/-!
# Finiteness of direct images

`Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound in
terms of the fibre dimension (`sk-prop-sf-finiteness`). Here `Λ` is a finite coefficient ring
whose exponent is invertible on the schemes in question
(`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a field:
without the invertibility the Artin–Schreier sequence already defeats constructibility of
`R¹f_*` in characteristic `p`.

The proofs follow the blueprint: the finiteness of `Rf_*` is the theorem
`thm-dg-finite-type-constructibility`, that of `Rf_! = Rg_* ∘ j_!` follows from it for the
proper `g` of a compactification together with the constructibility of extensions by zero, and
the vanishing of `Rᵠf_!` above twice the fibre dimension is read off the sheaf case
`sbc-thm-finiteness-finite-type` by a dévissage along the truncation triangles. The open case
`cor-fin-deligne-open-finite-coefficients` is the sheaf case
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field`
(`cor-fin-deligne-open-over-field`) extended to complexes by
`AlgebraicGeometry.Etale.boundedConstructible_obj_of_forall_singleFunctor`. The vanishing clause
of `sbc-thm-finiteness-finite-type` is `lem-dg-compact-support-amplitude`.

The sources of these inputs (blueprint `rem-exc-direct-image-input-sources`): the finiteness
clause is the classical finiteness theorem (SGA 4, XIV, 1.1; Stacks, Tag 0GL0), proved here by
Deligne's finite-boundary induction, with the proper case the comparison `obl-fin-comparison`;
the cohomological-dimension clause is the bound for finite-type schemes over a separably closed
field (Stacks, Tags 0F0V and 0F0P), proved from the affine bound `thm-sc-affine-torsion-cd`.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek`
- `thm-fin-open-immersion`, both in the namespace `AlgebraicGeometry.Etale`:
  `boundedConstructible_rightDerivedLowerStar_singleFunctor_of_isOpenImmersion` and
  `isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Finiteness

variable [Finite Λ] {k : Type u} [Field k]

/-! ### Inputs from the blueprint subsection `sk-prop-sf-cbc` -/

/-- Blueprint `cor-fin-deligne-open-finite-coefficients`: Open direct images with arbitrary
finite allowable coefficients.

Let `Λ` be a finite ring annihilated by an integer invertible in the field `k`, and let
`j : X ⟶ Y` be an open immersion of finite-type `k`-schemes (`X` is of finite type over `k` as
soon as `Y` is, `Y` being noetherian). Then `Rj_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`.

The sheaf case is `cor-fin-deligne-open-over-field`, stated for every finite `Λ` whose exponent is
invertible, so no dévissage from `𝔽_ℓ` to `Λ` is needed; complexes follow by truncation. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    [HasInvertibleExponent Λ (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  boundedConstructible_obj_of_forall_singleFunctor Λ _
    (fun F _ ↦ boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_of_field Λ aY j F) hK

/-- The separated case of `thm-dg-finite-type-constructibility`: for a separated morphism
`f : X ⟶ Y` of finite-type `k`-schemes, factor `f` through a compactification
`X ⟶[c.i] Z ⟶[c.g] Y` (Nagata); then `Rf_* = Rc.g_* ∘ Rc.i_*`, where the open direct image
`Rc.i_*` preserves bounded constructibility (`cor-fin-deligne-open-finite-coefficients`) and so
does the proper direct image `Rc.g_*` (`lem-fin-proper-bounded-constructible`). -/
lemma boundedConstructible_rightDerivedLowerStar_of_isSeparated
    [HasInvertibleExponent Λ (Spec (.of k))] (f : X ⟶ Y) [IsSeparated f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aX
      __ := QuasiCompact.compactSpace_of_compactSpace aX }
  have : IsNoetherian Y :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aY
      __ := QuasiCompact.compactSpace_of_compactSpace aY }
  have : LocallyOfFiniteType f := by
    subst hf
    exact locallyOfFiniteType_of_comp f aY
  let c := HasCompactification.compactification f
  have h₁ := boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion Λ (c.g ≫ aY) c.i K hK
  exact ObjectProperty.prop_of_iso _
    ((rightDerivedLowerStarComp _ c.i c.g).app K ≪≫
      (rightDerivedLowerStarCongr _ c.comm.symm).app K)
    (boundedConstructible_rightDerivedLowerStar_of_isProper aY c.g h₁)

open Pretriangulated in
/-- The induction step of `thm-dg-finite-type-constructibility`, on the number `n` of affine opens
needed to cover the source. For an affine open `j : U ⟶ X` of the cover, with closed complement
`i : Z ⟶ X`, complete the unit to a distinguished triangle `K ⟶ Rj_* j^* K ⟶ C ⟶ K[1]`. The
middle term is bounded constructible (`cor-fin-deligne-open-finite-coefficients`), and so is its
direct image `R(jf)_* j^* K`, `j ≫ f` being separated. The cone `C` is bounded constructible and
vanishes on `U`, so `C ≅ Ri_* i^* C` and `Rf_* C ≅ R(if)_* i^* C`, which is bounded constructible
by induction, `Z` being covered by the `n - 1` affine opens `i⁻¹ V`, `V ≠ U`. -/
lemma boundedConstructible_rightDerivedLowerStar_of_card_le
    [HasInvertibleExponent Λ (Spec (.of k))] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (n : ℕ) :
    ∀ (W : Scheme.{u}) (aW : W ⟶ Spec (.of k)) [LocallyOfFiniteType aW] [QuasiCompact aW]
      (s : Finset W.Opens), (∀ U ∈ s, IsAffineOpen U) → (∀ x : W, ∃ U ∈ s, x ∈ U) →
      s.card ≤ n → ∀ (f : W ⟶ Y), f ≫ aY = aW →
      ∀ K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W K →
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have hempty (W : Scheme.{u}) (s : Finset W.Opens) (hcov : ∀ x : W, ∃ U ∈ s, x ∈ U)
      (hs : s = ∅) (f : W ⟶ Y) (K) : DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} Λ) Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
    have : IsEmpty W := ⟨fun x ↦ by obtain ⟨U, hU, -⟩ := hcov x; simp [hs] at hU⟩
    exact boundedConstructible_of_isZero Λ
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero (isZero_derivedCategory_of_isEmpty _ W K))
  induction n with
  | zero =>
    intro W aW _ _ s _ hcov hn f _ K _
    exact hempty W s hcov (Finset.card_eq_zero.1 (Nat.le_zero.1 hn)) f K
  | succ n ih =>
    intro W aW _ _ s hs hcov hn f hf K hK
    obtain rfl | ⟨U, hU⟩ := s.eq_empty_or_nonempty
    · exact hempty W ∅ hcov rfl f K
    let P := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) W
    let Q := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
    let j := U.ι
    let i := U.closedComplement
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      rw [U.range_closedComplement, Scheme.Opens.range_ι]
    let adj := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j
    obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app K)
    -- the middle term `Rj_* j^* K` and its direct image `R(jf)_* j^* K`
    have hjK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K) :=
      hK.mapDerivedCategory_upperStar j
    have h₂ : P ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K)) :=
      boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion Λ aW j _ hjK
    have : IsAffine U := hs U hU
    have h₂' : Q ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K))) :=
      Q.prop_of_iso ((rightDerivedLowerStarComp _ j f).app _).symm
        (boundedConstructible_rightDerivedLowerStar_of_isSeparated Λ (j ≫ f) (j ≫ aW) aY
          (by simp [hf]) _ hjK)
    -- the cone `C` is bounded constructible and vanishes on `U`
    have hC : P C := P.ext_of_isTriangulatedClosed₃ _ hT hK h₂
    have hCU : IsZero ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj C) := by
      refine (Triangle.isZero₃_iff_isIso₁ _
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.map_distinguished _ hT)).2 ?_
      change IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.map
        (adj.unit.app K))
      have : IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.map
          (adj.unit.app K) ≫ adj.counit.app _) := by
        rw [adj.left_triangle_components K]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    -- hence `C ≅ Ri_* i^* C`
    obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij C
    have hu : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app C) :=
      (Triangle.isZero₁_iff_isIso₂ _ hw).1 (Functor.map_isZero _ hCU)
    -- the closed complement is covered by fewer affine opens
    classical
    let s' := (s.erase U).image fun V ↦ i ⁻¹ᵁ V
    have hs' : ∀ V ∈ s', IsAffineOpen V := by
      simp only [s', Finset.mem_image]
      rintro _ ⟨V, hV, rfl⟩
      exact (hs V (Finset.mem_of_mem_erase hV)).preimage i
    have hcov' : ∀ z, ∃ V ∈ s', z ∈ V := by
      intro z
      obtain ⟨V, hV, hz⟩ := hcov (i z)
      have hiz : i z ∉ U := by
        have : i z ∈ Set.range i.base := ⟨z, rfl⟩
        rw [hij, Scheme.Opens.range_ι] at this
        exact this
      exact ⟨i ⁻¹ᵁ V, Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨by rintro rfl; exact hiz hz,
        hV⟩), hz⟩
    have hcard : s'.card ≤ n := Finset.card_image_le.trans (by
      rw [Finset.card_erase_of_mem hU]
      lia)
    have hZ := ih _ (i ≫ aW) s' hs' hcov' hcard (i ≫ f) (by simp [hf]) _
      (hC.mapDerivedCategory_upperStar i)
    have h₃ : Q ((R((f)_*[ModuleCat.{u + 1} Λ])).obj C) :=
      Q.prop_of_iso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso (asIso
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app C)) ≪≫
          (rightDerivedLowerStarComp _ i f).app _).symm hZ
    exact Q.ext_of_isTriangulatedClosed₁ _
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT) h₂' h₃

/-- Blueprint `thm-dg-finite-type-constructibility`: Bounded constructibility of every
finite-type direct image.

Let `f : X ⟶ Y` be a morphism between finite-type schemes over a field `k`, and let `Λ` be a
finite ring annihilated by an integer invertible in `k`. Then `Rf_*` carries `D^b_c(X, Λ)` into
`D^b_c(Y, Λ)`. The morphism `f` need not be separated.

The blueprint uses a finite alternating Čech resolution; we induct instead on the number of
affine opens covering `X` (`boundedConstructible_rightDerivedLowerStar_of_card_le`), along the
triangle `K ⟶ Rj_* j^* K ⟶ C` for one affine open `j`, whose cone `C` lives on the closed
complement. Affine pieces are handled through a compactification
(`boundedConstructible_rightDerivedLowerStar_of_isSeparated`): an open immersion followed by a
proper morphism, as in the blueprint. -/
theorem boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType
    [HasInvertibleExponent Λ (Spec (.of k))] (f : X ⟶ Y) (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have hcov : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : Set X) := fun x ↦ by
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X, TopologicalSpace.Opens.mem_iSup] at hx
    exact hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ Set.mem_iUnion.2 (hcov x)
  refine boundedConstructible_rightDerivedLowerStar_of_card_le Λ aY _ X aX
    (t.image Subtype.val) ?_ (fun x ↦ ?_) le_rfl f hf K hK
  · simp only [Finset.mem_image]
    rintro _ ⟨U, -, rfl⟩
    exact U.2
  · obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨U, Finset.mem_image_of_mem _ hU, hx⟩

/-- Blueprint `sbc-thm-finiteness-finite-type`: Finiteness of higher direct images of
finite-type morphisms, the vanishing clause.

Let `f : X ⟶ Y` be a separated finite-type morphism (here: one admitting a compactification)
between finite-type schemes over a field `k`, let `Λ` be a finite ring whose exponent is
invertible on `Y` and let `𝓕` be a sheaf of `Λ`-modules on `X_ét`. If the geometric fibres of
`f` have dimension at most `e`, then `Rᵠf_! 𝓕 = 0` for `q > 2e`. Constructibility of `𝓕` is
not needed: the bound only uses the dimensions of the original fibres (blueprint
`lem-dg-compact-support-amplitude`).

This is a node of the blueprint subsection `sk-prop-sf-cbc`, where it is proved. Its other
clauses, the bounded constructibility of `Rf_* 𝓕` and of `Rf_! 𝓕`, are the sheaf cases of
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` and
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`. The vanishing is
`lem-dg-compact-support-amplitude`, which bounds `Rf_!` by the dimension of the original fibres. -/
theorem isZero_homology_rightDerivedLowerShriek_singleFunctor
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX) (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
  isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt Λ f aX aY hf e he F q hq

/-! ### Auxiliary lemmas -/

omit [Finite Λ] [CommRing Λ] in
/-- The source of a morphism admitting a compactification, to a quasi-compact scheme locally of
finite type over a field, is a noetherian space: it is open in the compactification, which is
of finite type over the field. -/
lemma noetherianSpace_of_hasCompactification (f : X ⟶ Y) [HasCompactification f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    TopologicalSpace.NoetherianSpace X := by
  let c := HasCompactification.compactification f
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY)
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aY)
  have : IsNoetherian c.Z := ⟨⟩
  exact c.i.isOpenEmbedding.isInducing.noetherianSpace

/-! ### Open immersions -/

/-! ### Finiteness of `Rf_*` and `Rf_!` -/

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring whose exponent is invertible on `X`
and let `f : X ⟶ Y` be a quasi-compact morphism between `k`-schemes locally of finite type, with
`Y` quasi-compact. Then `Rf_*` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`; separatedness of `f` is
not needed. This is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType`
(`thm-dg-finite-type-constructibility`): `X` is quasi-compact since `f` and `Y` are, and the
exponent of `Λ` is invertible in `k` as soon as `X` is nonempty.

Some finiteness hypothesis on `Y` is needed: for `f : ⊔ₙ ℙⁿ_k ⟶ ⊔ₙ Spec k`, which is proper,
`Rf_* Λ` has `H²ⁿ ≠ 0` on the `n`-th point, so it is not bounded.

The cohomological-dimension bound of the blueprint statement is
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt` (`thm-sc-finite-type-torsion-cd`),
and its special case for the spectrum of a separably closed field is
`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed` (`lem-kun-cd-sep-closed-point`). -/
theorem boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (f : X ⟶ Y)
    [QuasiCompact f] [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    exact boundedConstructible_of_isZero Λ
      ((R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero (isZero_derivedCategory_of_isEmpty _ X K))
  | inr hX =>
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    have : QuasiCompact aX := hf ▸ inferInstance
    exact boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType Λ f aX aY hf K hK

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images.** For `f : X ⟶ Y` admitting a
compactification, between `k`-schemes locally of finite type with `Y` quasi-compact, `Rf_!`
carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`. For the chosen compactification `X ⟶[j] Z ⟶[g] Y`,
`Rf_! = Rg_* ∘ j_!`: extension by zero preserves constructibility, and `Rg_*` preserves bounded
constructibility by
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`.

As for `Rf_*`, some finiteness hypothesis on `Y` is needed. -/
theorem boundedConstructible_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] [QuasiCompact aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  subst hf
  cases isEmpty_or_nonempty X with
  | inl hX =>
    exact boundedConstructible_of_isZero Λ
      ((R(f)_![ModuleCat.{u + 1} Λ]).map_isZero (isZero_derivedCategory_of_isEmpty _ X K))
  | inr hX =>
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) (f ≫ aY)
    let c := HasCompactification.compactification f
    have : HasInvertibleExponent Λ c.Z := HasInvertibleExponent.of_hom (c.g ≫ aY)
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
    have : IsNoetherian c.Z := { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY) }
    have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
    exact boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent Λ c.g (c.g ≫ aY) aY
      rfl _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek Λ c.i hK)

end Finiteness

end Etale

end AlgebraicGeometry
