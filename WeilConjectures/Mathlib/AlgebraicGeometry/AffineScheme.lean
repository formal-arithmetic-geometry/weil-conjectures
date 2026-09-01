/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
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
  `Γ(X, ⊤)_x ⟶ Γ(X_x, ⊤)`, which sends `a / x` to `AlgebraicGeometry.Scheme.divBasicOpen`.

We also show that an affine scheme `V` equipped with a morphism `g : V ⟶ S` is covered by
finitely many basic opens, each of which lands in an affine open of `S`.
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

end AlgebraicGeometry
