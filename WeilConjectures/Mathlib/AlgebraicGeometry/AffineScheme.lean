/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.PrincipalIdealDomain
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

For an arbitrary scheme `X` and a global section `x`, the basic open `X_x` maps canonically
to `Spec Γ(X, ⊤)_x`. We record this morphism and the induced map on global sections:

- `AlgebraicGeometry.Scheme.toSpecAway` — the morphism `X_x ⟶ Spec Γ(X, ⊤)_x`;
- `AlgebraicGeometry.Scheme.awayToBasicOpen` — the induced ring map
  `Γ(X, ⊤)_x ⟶ Γ(X_x, ⊤)`, which sends `a / x` to `AlgebraicGeometry.Scheme.divBasicOpen`;
- `AlgebraicGeometry.mk'_eq_divBasicOpen_pow` — the fraction `a / x ^ N` in `Γ(X_x, ⊤)`, for
  affine `X`, written in terms of `AlgebraicGeometry.Scheme.divBasicOpen`.

We also show that an affine scheme `V` equipped with a morphism `g : V ⟶ S` is covered by
finitely many basic opens, each of which lands in an affine open of `S`.

We also record that, for a morphism `f : X ⟶ Y`, the affine opens of `X` contained in the
preimage of an affine open of `Y` form a basis of the topology of `X`
(`AlgebraicGeometry.isBasis_affineOpens_le_preimage`).

Finally, every open subscheme of the spectrum of a principal ideal ring is affine
(`AlgebraicGeometry.isAffineOpen_of_isPrincipalIdealRing`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

section Away

variable (X : Scheme.{u}) (x : Γ(X, ⊤))

/-- The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)_x` from the locus where a global section does
not vanish to the spectrum of the localization of the global sections away from it. -/
noncomputable def Scheme.toSpecAway :
    (X.basicOpen x : Scheme.{u}) ⟶ Spec (.of <| Localization.Away x) :=
  X.toSpecΓ.resLE _ (X.basicOpen x) (X.toSpecΓ_preimage_basicOpen x).ge ≫
    (basicOpenIsoSpecAway x).hom

@[reassoc]
lemma Scheme.toSpecAway_SpecMap_algebraMap :
    X.toSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  rw [Scheme.toSpecAway, Category.assoc]
  exact resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap X x

/-- The canonical map `Γ(X, ⊤)_x ⟶ Γ(X_x, ⊤)` from the localization of the global sections
away from `x` to the sections over the basic open `X_x`. -/
noncomputable def Scheme.awayToBasicOpen :
    CommRingCat.of (Localization.Away x) ⟶ Γ((X.basicOpen x : Scheme.{u}), ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (X.toSpecAway x).appTop

lemma Scheme.awayToBasicOpen_apply (y : Localization.Away x) :
    X.awayToBasicOpen x y = (X.toSpecAway x).appTop ((Scheme.ΓSpecIso _).inv y) :=
  rfl

lemma Scheme.algebraMap_comp_awayToBasicOpen :
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)) ≫ X.awayToBasicOpen x =
      (X.basicOpen x).ι.appTop := by
  rw [Scheme.awayToBasicOpen, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecAway_SpecMap_algebraMap, Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.toSpecΓ_appTop]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) : Type u))).inv ≫
    (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ from Iso.inv_hom_id _, Category.id_comp]

@[simp]
lemma Scheme.awayToBasicOpen_algebraMap (a : Γ(X, ⊤)) :
    X.awayToBasicOpen x (algebraMap Γ(X, ⊤) (Localization.Away x) a) =
      (X.basicOpen x).ι.appTop a := by
  conv_rhs => rw [← Scheme.algebraMap_comp_awayToBasicOpen X x]
  rfl

@[simp]
lemma Scheme.awayToBasicOpen_mk' (a : Γ(X, ⊤)) (h : x ∈ Submonoid.powers x) :
    X.awayToBasicOpen x (IsLocalization.mk' (Localization.Away x) a ⟨x, h⟩) =
      X.divBasicOpen a x := by
  refine X.eq_divBasicOpen ?_
  rw [← X.awayToBasicOpen_algebraMap x x, ← X.awayToBasicOpen_algebraMap x a, ← map_mul,
    IsLocalization.mk'_spec]

/-- The fraction `a / x ^ N` in the sections over a basic open `X_x` of an affine scheme,
written in terms of `AlgebraicGeometry.Scheme.divBasicOpen`. -/
lemma mk'_eq_divBasicOpen_pow [IsAffine X] (a : Γ(X, ⊤)) (N : ℕ)
    (h : x ^ N ∈ Submonoid.powers x) :
    IsLocalization.mk' Γ((X.basicOpen x : Scheme.{u}), ⊤) a ⟨x ^ N, h⟩ =
      X.divBasicOpen 1 x ^ N * X.divBasicOpen (a * x) x := by
  have e₁ : X.divBasicOpen (a * x) x = (X.basicOpen x).ι.appTop a :=
    (X.isUnit_ι_appTop_basicOpen x).mul_right_cancel
      ((X.divBasicOpen_mul_self _ _).trans (map_mul _ _ _))
  have e₂ : X.divBasicOpen 1 x * (X.basicOpen x).ι.appTop x = 1 :=
    (X.divBasicOpen_mul_self _ _).trans (map_one _)
  refine (IsLocalization.eq_mk'_iff_mul_eq.mpr ?_).symm
  change _ * (X.basicOpen x).ι.appTop (x ^ N) = (X.basicOpen x).ι.appTop a
  rw [map_pow, e₁, mul_right_comm, ← mul_pow, e₂, one_pow, one_mul]

end Away

/-- If `V` is an affine scheme and `g : V ⟶ S` is any morphism of schemes, then `V` is covered
by finitely many basic opens `V.basicOpen (b l)`, each of which is contained in the preimage of
an affine open `W l` of `S`. -/
theorem exists_finite_basicOpen_cover_le_preimage_isAffineOpen
    {V S : Scheme.{u}} [IsAffine V] (g : V ⟶ S) :
    ∃ (Λ : Type u) (_ : Finite Λ) (b : Λ → Γ(V, ⊤)) (W : Λ → S.Opens),
      (∀ l, IsAffineOpen (W l)) ∧
      (∀ l, V.basicOpen (b l) ≤ g ⁻¹ᵁ W l) ∧
      ⨆ l, V.basicOpen (b l) = ⊤ := by
  set T : Set Γ(V, ⊤) := {b | ∃ W : S.Opens, IsAffineOpen W ∧ V.basicOpen b ≤ g ⁻¹ᵁ W}
  have hcov : (Set.univ : Set V) ⊆ ⋃ b ∈ T, (V.basicOpen b : Set V) := by
    intro v _
    obtain ⟨W, hW, hvW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens S) (U := ⊤) (x := g.base v) trivial
    obtain ⟨-, ⟨b, rfl⟩, hvb, hbW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (isBasis_basicOpen V) (U := g ⁻¹ᵁ W) (x := v) hvW
    exact Set.mem_biUnion (show b ∈ T from ⟨W, hW, hbW⟩) hvb
  obtain ⟨t, htT, htfin, htcov⟩ :=
    isCompact_univ.elim_finite_subcover_image (fun b _ ↦ (V.basicOpen b).isOpen) hcov
  have h : ∀ l : t, ∃ W : S.Opens, IsAffineOpen W ∧ V.basicOpen (l : Γ(V, ⊤)) ≤ g ⁻¹ᵁ W :=
    fun l ↦ htT l.2
  choose W hW hWle using h
  refine ⟨t, htfin.to_subtype, Subtype.val, W, hW, hWle, eq_top_iff.mpr fun v _ ↦ ?_⟩
  obtain ⟨b, hb, hv⟩ := Set.mem_iUnion₂.mp (htcov (Set.mem_univ v))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hb⟩, hv⟩

/-- The version of `AlgebraicGeometry.exists_finite_basicOpen_cover_le_preimage_isAffineOpen`
phrased via the span of the chosen sections: the sections `b l` generate the unit ideal of
`Γ(V, ⊤)`. -/
theorem exists_finite_span_range_eq_top_le_preimage_isAffineOpen
    {V S : Scheme.{u}} [IsAffine V] (g : V ⟶ S) :
    ∃ (Λ : Type u) (_ : Finite Λ) (b : Λ → Γ(V, ⊤)) (W : Λ → S.Opens),
      (∀ l, IsAffineOpen (W l)) ∧
      (∀ l, V.basicOpen (b l) ≤ g ⁻¹ᵁ W l) ∧
      Ideal.span (Set.range b) = ⊤ := by
  obtain ⟨Λ, hΛ, b, W, hW, hWle, hcov⟩ := exists_finite_basicOpen_cover_le_preimage_isAffineOpen g
  refine ⟨Λ, hΛ, b, W, hW, hWle, ?_⟩
  rw [← (isAffineOpen_top V).iSup_basicOpen_eq_self_iff, iSup_range']
  exact hcov

/-- A quasi-compact open contained in an affine open `V` of a scheme is a finite union of
basic opens of sections over `V`. -/
theorem IsAffineOpen.exists_finset_basicOpen_eq {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {W : X.Opens} (hW : IsCompact (W : Set X)) (hWV : W ≤ V) :
    ∃ s : Finset Γ(X, V), W = ⨆ f ∈ s, X.basicOpen f := by
  classical
  have : IsAffine V.toScheme := hV
  have hW' : IsCompact ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Set V.toScheme) :=
    V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW
      (by rw [Scheme.Opens.range_ι]; exact hWV)
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_basicOpen V.toScheme).exists_finite_of_isCompact hW'
  have := hUsfin.fintype
  choose g hg using fun u : Us ↦ hUsB u.2
  refine ⟨Finset.univ.image fun u : Us ↦ V.topIso.hom (g u), ?_⟩
  calc W = V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.mpr hWV]
    _ = ⨆ u : Us, V.ι ''ᵁ (u : V.toScheme.Opens) := by
        rw [hUs, sSup_eq_iSup', Scheme.Hom.image_iSup]
    _ = ⨆ f ∈ Finset.univ.image fun u : Us ↦ V.topIso.hom (g u), X.basicOpen f := by
        rw [Finset.iSup_finset_image]
        simp only [Finset.mem_univ, iSup_pos]
        refine iSup_congr fun u ↦ ?_
        rw [← hg u]
        conv_lhs => rw [← Iso.hom_inv_id_apply V.topIso (g u)]
        exact Scheme.Opens.ι_image_basicOpen_topIso_inv _ _

/-- The affine opens of `X` that are contained in the preimage of an affine open of `Y` form a
basis of the topology of `X`. -/
lemma isBasis_affineOpens_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopologicalSpace.Opens.IsBasis {W : X.Opens | IsAffineOpen W ∧
      ∃ V : Y.Opens, IsAffineOpen V ∧ W ≤ f ⁻¹ᵁ V} := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (x := f.base x) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := U ⊓ f ⁻¹ᵁ V) ⟨hxU, hxV⟩
  exact ⟨W, ⟨hW, V, hV, hWU.trans inf_le_right⟩, hxW, hWU.trans inf_le_left⟩

/-- A quasi-compact open of an affine scheme is a finite union of basic opens. -/
lemma exists_finite_basicOpen_cover [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (_ : ∀ i, X.basicOpen (u i) ≤ U),
      U = ⨆ i, X.basicOpen (u i) := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} ↦ (X.basicOpen a.1 : Set X))
    (fun a ↦ (X.basicOpen a.1).2) (by
      intro x hx
      obtain ⟨a, ha1, ha2⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
      exact Set.mem_iUnion.mpr ⟨⟨a, ha1⟩, ha2⟩)
  refine ⟨{a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} // a ∈ t}, inferInstance,
    fun a ↦ a.1.1, fun a ↦ a.1.2, le_antisymm ?_ (iSup_le fun a ↦ a.1.2)⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

/-- Every open subscheme of the spectrum of a principal ideal ring is affine: it is the
complement of the zero locus of an ideal, hence of a single element, so it is a basic open. -/
theorem isAffineOpen_of_isPrincipalIdealRing {R : CommRingCat.{u}} [IsPrincipalIdealRing R]
    (U : (Spec R).Opens) : IsAffineOpen U := by
  obtain ⟨s, hs⟩ :=
    (PrimeSpectrum.isOpen_iff (show Set (PrimeSpectrum R) from (U : Set (Spec R)))).1 U.isOpen
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span s)).principal
  have : U = (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv g) := by
    rw [basicOpen_eq_of_affine]
    ext x
    have hx := congrArg (x ∈ ·) hs
    simp only [eq_iff_iff] at hx
    change x ∈ U ↔ g ∉ x.asIdeal
    rw [← not_iff_not, not_not]
    refine hx.trans ((PrimeSpectrum.mem_zeroLocus (x : PrimeSpectrum R) s).trans ?_)
    rw [← Ideal.span_le, hg, Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
  rw [this]
  exact (isAffineOpen_top (Spec R)).basicOpen _

/-- A scheme with an open immersion into the spectrum of a principal ideal ring is affine. -/
theorem isAffine_of_isOpenImmersion_of_isPrincipalIdealRing {X : Scheme.{u}}
    {R : CommRingCat.{u}} [IsPrincipalIdealRing R] (f : X ⟶ Spec R) [IsOpenImmersion f] :
    IsAffine X :=
  have : IsAffine f.opensRange := isAffineOpen_of_isPrincipalIdealRing f.opensRange
  .of_isIso f.isoOpensRange.hom

/-- **Prime avoidance in `Spec R`.** A finite set of points of an open subset `O` of
`PrimeSpectrum R` is contained in a basic open `D(r) ⊆ O`. -/
theorem _root_.PrimeSpectrum.exists_basicOpen_le_of_finite {R : Type*} [CommRing R]
    {O : Set (PrimeSpectrum R)} (hO : IsOpen O) {t : Set (PrimeSpectrum R)} (ht : t.Finite)
    (htO : t ⊆ O) :
    ∃ r : R, t ⊆ PrimeSpectrum.basicOpen r ∧ (PrimeSpectrum.basicOpen r : Set _) ⊆ O := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Oᶜ).mp hO.isClosed_compl
  have hJt : ¬ (J : Set R) ⊆ ⋃ I ∈ PrimeSpectrum.asIdeal '' t, ((id I : Ideal R) : Set R) := by
    rw [Ideal.subset_union_prime_finite (ht.image _) (f := id) ⊥ ⊥
      (by grind [PrimeSpectrum.isPrime])]
    rintro ⟨_, ⟨p, hp, rfl⟩, hle⟩
    have : p ∈ Oᶜ := hJ ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr hle
    exact this (htO hp)
  obtain ⟨r, hrJ, hr⟩ := Set.not_subset.mp hJt
  refine ⟨r, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_image, id] at hr
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h ↦ hr ⟨_, ⟨p, hp, rfl⟩, h⟩
  · by_contra h
    have : p ∈ PrimeSpectrum.zeroLocus (J : Set R) := hJ ▸ h
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hp (this hrJ)

/-- **Prime avoidance for affine opens.** A finite set of points of an open `O` contained in an
affine open `U` lies in a basic open `D(r) ⊆ O` of `U`. -/
theorem IsAffineOpen.exists_basicOpen_le_of_finite {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {O : X.Opens} (hO : O ≤ U) {s : Set X} (hs : s.Finite)
    (hsO : s ⊆ O) : ∃ r : Γ(X, U), s ⊆ X.basicOpen r ∧ X.basicOpen r ≤ O := by
  obtain ⟨r, hsr, hrO⟩ := PrimeSpectrum.exists_basicOpen_le_of_finite
    (hU.fromSpec ⁻¹ᵁ O).isOpen (hs.preimage hU.fromSpec.isOpenEmbedding.injective.injOn)
    (Set.preimage_mono hsO)
  refine ⟨r, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hO (hsO hx)
    rw [SetLike.mem_coe, ← Scheme.Hom.mem_preimage, hU.fromSpec_preimage_basicOpen]
    exact hsr hx
  · rw [← hU.fromSpec_image_basicOpen]
    rintro _ ⟨y, hy, rfl⟩
    exact hrO hy

end AlgebraicGeometry
