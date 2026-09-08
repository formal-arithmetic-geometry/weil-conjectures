/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Zero
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

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
- `AlgebraicGeometry.Scheme.mk'_eq_divBasicOpen_pow` — the fraction `a / x ^ N` in
  `Γ(X_x, ⊤)`, for affine `X`, written in terms of `AlgebraicGeometry.Scheme.divBasicOpen`.

We also show that an affine scheme `V` equipped with a morphism `g : V ⟶ S` is covered by
finitely many basic opens, each of which lands in an affine open of `S`.

Finally, we relate the generic points of the irreducible components of a scheme `X` lying in an
affine open `U` to the minimal primes of `Γ(X, U)`
(`AlgebraicGeometry.IsAffineOpen.primeIdealOf_mem_minimalPrimes`) and deduce the scheme-theoretic
form of Stacks Project Tag 00EV
(`AlgebraicGeometry.IsAffineOpen.exists_mem_basicOpen_and_disjoint`).
-/

@[expose] public section

universe u

open CategoryTheory Topology

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

/-- The algebra map from the global sections of `X` to the global sections of a basic open
`X_b`, viewed as a scheme, is the pullback along the inclusion of `X_b`. -/
lemma algebraMap_appTop_basicOpen_eq (b : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) Γ((X.basicOpen b : Scheme.{u}), ⊤) = (X.basicOpen b).ι.appTop.hom :=
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
  have hid : (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) : Type u))).inv ≫
      (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := Iso.inv_hom_id _
  rw [Scheme.awayToBasicOpen, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecAway_SpecMap_algebraMap, Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.toSpecΓ_appTop, hid, Category.id_comp]

@[simp]
lemma Scheme.awayToBasicOpen_algebraMap (a : Γ(X, ⊤)) :
    X.awayToBasicOpen x (algebraMap Γ(X, ⊤) (Localization.Away x) a) =
      (X.basicOpen x).ι.appTop a := by
  conv_rhs => rw [← Scheme.algebraMap_comp_awayToBasicOpen X x]
  rfl

@[simp]
lemma Scheme.awayToBasicOpen_mk' (a : Γ(X, ⊤))
    (h : x ∈ Submonoid.powers x := Submonoid.mem_powers x) :
    X.awayToBasicOpen x (IsLocalization.mk' (Localization.Away x) a ⟨x, h⟩) =
      X.divBasicOpen a x := by
  refine X.eq_divBasicOpen ?_
  rw [← X.awayToBasicOpen_algebraMap x x, ← X.awayToBasicOpen_algebraMap x a, ← map_mul,
    IsLocalization.mk'_spec]

/-- The fraction `a / x ^ N` in the sections over a basic open `X_x` of an affine scheme,
written in terms of `AlgebraicGeometry.Scheme.divBasicOpen`. -/
lemma Scheme.mk'_eq_divBasicOpen_pow [IsAffine X] (a : Γ(X, ⊤)) (N : ℕ)
    (h : x ^ N ∈ Submonoid.powers x := ⟨N, rfl⟩) :
    IsLocalization.mk' Γ((X.basicOpen x : Scheme.{u}), ⊤) a ⟨x ^ N, h⟩ =
      X.divBasicOpen 1 x ^ N * X.divBasicOpen (a * x) x := by
  have e₁ : X.divBasicOpen (a * x) x = (X.basicOpen x).ι.appTop a :=
    (X.isUnit_ι_appTop_basicOpen x).mul_right_cancel
      ((X.divBasicOpen_mul_self _ _).trans (map_mul _ _ _))
  have e₂ : X.divBasicOpen 1 x * (X.basicOpen x).ι.appTop x = 1 :=
    (X.divBasicOpen_mul_self _ _).trans (map_one _)
  refine (IsLocalization.eq_mk'_iff_mul_eq.mpr ?_).symm
  rw [algebraMap_appTop_basicOpen_eq, map_pow, e₁, mul_right_comm, ← mul_pow, e₂, one_pow,
    one_mul]

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
  let T : Set Γ(V, ⊤) := {b | ∃ W : S.Opens, IsAffineOpen W ∧ V.basicOpen b ≤ g ⁻¹ᵁ W}
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

/-- A point of an affine open `U` of `X` that is the generic point of an irreducible component
of `X` corresponds to a minimal prime of `Γ(X, U)`. -/
lemma IsAffineOpen.primeIdealOf_mem_minimalPrimes {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ genericPoints X) (hxU : x ∈ U) :
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U) := by
  rw [← PrimeSpectrum.mem_genericPoints_iff]
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have h : hU.fromSpec.base ⁻¹' closure {x} ∈ irreducibleComponents (Spec Γ(X, U)) :=
    preimage_mem_irreducibleComponents hx hoe
      ⟨x, subset_closure rfl, by
        rw [hU.range_fromSpec]
        exact hxU⟩
  rw [hoe.isOpenMap.preimage_closure_eq_closure_preimage hoe.continuous] at h
  have : hU.fromSpec.base ⁻¹' {x} = {hU.primeIdealOf ⟨x, hxU⟩} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hU.fromSpec_primeIdealOf ⟨x, hxU⟩, fun y hy ↦ ?_⟩
    exact hoe.injective (hy.trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm)
  rwa [this] at h

/-- Let `U` be an affine open of `X` and let `x ∈ U` be the generic point of an irreducible
component of `X`. Any quasi-compact open `W ⊆ U` not containing `x` can be separated from `x`
by a standard open: there is `f ∈ Γ(X, U)` with `x ∈ D(f)` and `D(f) ∩ W = ∅`. -/
@[stacks 00EV]
lemma IsAffineOpen.exists_mem_basicOpen_and_disjoint {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ genericPoints X) (hxU : x ∈ U) {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W)
    (hWU : W ⊆ (U : Set X)) (hxW : x ∉ W) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ Disjoint (X.basicOpen f : Set X) W := by
  have hoe : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have hrange : Set.range hU.fromSpec.base = (U : Set X) := hU.range_fromSpec
  obtain ⟨f, hf, hdisj⟩ := PrimeSpectrum.exists_notMem_and_disjoint_basicOpen_of_mem_minimalPrimes
    (hU.primeIdealOf_mem_minimalPrimes hx hxU) (hWo.preimage hU.fromSpec.continuous)
    (hoe.isInducing.isCompact_preimage' hWc (hrange ▸ hWU))
    (by simpa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] using hxW)
  have hmem (y : Spec Γ(X, U)) :
      hU.fromSpec.base y ∈ X.basicOpen f ↔ y ∈ PrimeSpectrum.basicOpen f :=
    congr(y ∈ $(hU.fromSpec_preimage_basicOpen f)).to_iff
  refine ⟨f, ?_, Set.disjoint_left.mpr fun y hy hyW ↦ ?_⟩
  · have h := (hmem (hU.primeIdealOf ⟨x, hxU⟩)).mpr hf
    rwa [hU.fromSpec_primeIdealOf ⟨x, hxU⟩] at h
  · obtain ⟨z, rfl⟩ : y ∈ Set.range hU.fromSpec.base := hrange ▸ X.basicOpen_le f hy
    exact Set.disjoint_left.mp hdisj ((hmem z).mp hy) hyW

end AlgebraicGeometry
