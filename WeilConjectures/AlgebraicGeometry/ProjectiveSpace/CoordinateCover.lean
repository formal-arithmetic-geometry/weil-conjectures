/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Coordinate covers: line bundles with trivialising sections

A *coordinate cover* of a scheme `X`, indexed by `ι`, is an open cover `(Uᵢ)` of `X` together
with functions `tᵢⱼ ∈ Γ(X, Uᵢ)`, thought of as the ratios `Tⱼ / Tᵢ` of sections `Tᵢ` of an
invertible module `L` with `Uᵢ = X_{Tᵢ}`, subject to `tᵢᵢ = 1`, `D(tᵢⱼ) = Uᵢ ∩ Uⱼ` and the
cocycle condition `tᵢₗ = tᵢⱼ tⱼₗ` on `Uᵢ ∩ Uⱼ`. A morphism `X ⟶ ℙ(ι; S)` gives a coordinate cover
by pulling back the standard charts, and conversely a coordinate cover glues to a morphism
`X ⟶ ℙ(ι; S)`.

A *section of degree `n`* of a coordinate cover is a family `sᵢ ∈ Γ(X, Uᵢ)` with
`sᵢ = tᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`, i.e. a section `s = sᵢ Tᵢⁿ` of `L^{⊗ n}` written in the
trivialisations. Families of sections of the same degree that generate the unit ideal on every
`Uᵢ` define morphisms to projective space (`AlgebraicGeometry.Scheme.CoordinateCover.hom`).

The main technical result is the extension lemma
`AlgebraicGeometry.Scheme.CoordinateCover.exists_section`: on a coordinate cover by quasi-compact
quasi-separated opens, every function `h` on a chart `U_{i₀}` is, after multiplication by a power
of `T_{i₀}`, the restriction of a section, which can moreover be chosen to vanish outside `U_{i₀}`.
This is the standard fact (Stacks, Tag 01PW) that sections of powers of `L` over `X_s` extend
after multiplication by a power of `s`.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover`: a coordinate cover.
- `AlgebraicGeometry.Scheme.CoordinateCover.Section`: sections of degree `n`.
- `AlgebraicGeometry.Scheme.CoordinateCover.hom`: the morphism to projective space defined by a
  family of sections.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.preimage_hom_standardOpen`: the preimage of the
  standard open `D₊(Tₐ)` under the morphism defined by sections `σ` is the locus `X_{σₐ}`.
- `AlgebraicGeometry.Scheme.CoordinateCover.exists_section`: the extension lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

lemma Scheme.homOfLE_appTop_topIso_inv {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V)
    (x : Γ(X, V)) : (X.homOfLE e).appTop (V.topIso.inv x) =
      U.topIso.inv (X.presheaf.map (homOfLE e).op x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x = (X.presheaf.map _ ≫ X.presheaf.map _) x
  rw [← Functor.map_comp]
  erw [← Functor.map_comp]
  rfl

lemma Scheme.presheaf_map_map {X : Scheme.{u}} {U V W : X.Opens} (e₁ : V ≤ U) (e₂ : W ≤ V)
    (x : Γ(X, U)) : X.presheaf.map (homOfLE e₂).op (X.presheaf.map (homOfLE e₁).op x) =
      X.presheaf.map (homOfLE (e₂.trans e₁)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma Scheme.isUnit_map_of_le_basicOpen {X : Scheme.{u}} {U V : X.Opens} (f : Γ(X, U))
    (h : V ≤ X.basicOpen f) :
    IsUnit (X.presheaf.map (homOfLE (h.trans (X.basicOpen_le f))).op f) := by
  have := (RingedSpace.isUnit_res_basicOpen X.toRingedSpace f).map
    (X.presheaf.map (homOfLE h).op).hom
  exact (X.presheaf_map_map (X.basicOpen_le f) h f) ▸ this

lemma Scheme.eq_of_map_eq_of_eq {X : Scheme.{u}} {U V : X.Opens} (e : V = U) {x y : Γ(X, U)}
    (h : X.presheaf.map (homOfLE e.le).op x = X.presheaf.map (homOfLE e.le).op y) : x = y := by
  subst e
  simpa using h

/-- A *coordinate cover* of a scheme `X` indexed by `ι`: an open cover `(Uᵢ)` with functions
`tᵢⱼ ∈ Γ(X, Uᵢ)` (the ratios `Tⱼ / Tᵢ` of trivialising sections of an invertible module) such
that `tᵢᵢ = 1`, `D(tᵢⱼ) = Uᵢ ∩ Uⱼ` and `tᵢₗ = tᵢⱼ tⱼₗ` on `Uᵢ ∩ Uⱼ`. -/
structure Scheme.CoordinateCover (X : Scheme.{u}) (ι : Type u) where
  /-- The charts. -/
  U : ι → X.Opens
  /-- The ratio `Tⱼ / Tᵢ`, a function on the chart `Uᵢ`. -/
  ratio (i j : ι) : Γ(X, U i)
  ratio_self (i : ι) : ratio i i = 1
  basicOpen_ratio (i j : ι) : X.basicOpen (ratio i j) = U i ⊓ U j
  ratio_mul (i j l : ι) :
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i l) =
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i j) *
        X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (ratio j l)
  iSup_U : ⨆ i, U i = ⊤

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι)

lemma isUnit_ratio_map (i j : ι) :
    IsUnit (X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (𝒟.ratio i j)) :=
  X.isUnit_map_of_le_basicOpen _ (𝒟.basicOpen_ratio i j).ge

/-- A *section of degree `n`* of a coordinate cover: functions `sᵢ ∈ Γ(X, Uᵢ)` with
`sᵢ = tᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`, i.e. the section `sᵢ Tᵢⁿ` of the `n`-th power of the underlying
invertible module. -/
@[ext]
structure Section (n : ℕ) where
  /-- The section on the chart `Uᵢ`, written in the trivialisation `Tᵢⁿ`. -/
  s (i : ι) : Γ(X, 𝒟.U i)
  s_eq (i j : ι) :
    X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (s i) =
      X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (𝒟.ratio i j) ^ n *
        X.presheaf.map (homOfLE (inf_le_right : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U j)).op (s j)

variable {𝒟}

namespace Section

/-- The product of sections of degrees `m` and `n`, a section of degree `m + n`. -/
def mul {m n : ℕ} (σ : 𝒟.Section m) (τ : 𝒟.Section n) : 𝒟.Section (m + n) where
  s i := σ.s i * τ.s i
  s_eq i j := by
    rw [map_mul, map_mul, σ.s_eq i j, τ.s_eq i j, pow_add]
    ring

@[simp]
lemma mul_s {m n : ℕ} (σ : 𝒟.Section m) (τ : 𝒟.Section n) (i : ι) :
    (σ.mul τ).s i = σ.s i * τ.s i := rfl

/-- The locus `X_σ` where a section does not vanish. -/
def nonvanishing {n : ℕ} (σ : 𝒟.Section n) : X.Opens :=
  ⨆ i, X.basicOpen (σ.s i)

lemma basicOpen_inf_le {n : ℕ} (σ : 𝒟.Section n) (i j : ι) :
    X.basicOpen (σ.s i) ⊓ 𝒟.U j ≤ X.basicOpen (σ.s j) := by
  have h := congrArg X.basicOpen (σ.s_eq i j)
  rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    X.basicOpen_of_isUnit ((𝒟.isUnit_ratio_map i j).pow n)] at h
  intro x ⟨hxi, hxj⟩
  have hx : x ∈ (𝒟.U i ⊓ 𝒟.U j) ⊓ X.basicOpen (σ.s i) := ⟨⟨X.basicOpen_le _ hxi, hxj⟩, hxi⟩
  rw [h] at hx
  exact hx.2.2

/-- On the chart `Uⱼ`, the locus where `σ` does not vanish is the basic open of `σⱼ`. -/
lemma nonvanishing_inf {n : ℕ} (σ : 𝒟.Section n) (j : ι) :
    σ.nonvanishing ⊓ 𝒟.U j = X.basicOpen (σ.s j) := by
  refine le_antisymm ?_ (le_inf (le_iSup (fun i ↦ X.basicOpen (σ.s i)) j) (X.basicOpen_le _))
  rw [nonvanishing, iSup_inf_eq]
  exact iSup_le fun i ↦ σ.basicOpen_inf_le i j

end Section

/-- The coordinate section `Tₗ`, of degree one. -/
def coord (l : ι) : 𝒟.Section 1 where
  s i := 𝒟.ratio i l
  s_eq i j := by rw [pow_one, 𝒟.ratio_mul]

@[simp]
lemma coord_s (l i : ι) : (𝒟.coord l).s i = 𝒟.ratio i l := rfl

/-- The `n`-th power `Tₗⁿ` of a coordinate section. -/
def coordPow (l : ι) : (n : ℕ) → 𝒟.Section n
  | 0 => ⟨fun _ ↦ 1, fun i j ↦ by simp⟩
  | n + 1 => (coordPow l n).mul (𝒟.coord l)

@[simp]
lemma coordPow_s (l : ι) (n : ℕ) (i : ι) : (𝒟.coordPow l n).s i = 𝒟.ratio i l ^ n := by
  induction n with
  | zero => simp [coordPow]
  | succ n ih => simp [coordPow, ih, pow_succ]

section Hom

variable {α : Type u} {N : ℕ} (σ : α → 𝒟.Section N)
  (hσ : ∀ i, Ideal.span (Set.range fun a ↦ (σ a).s i) = ⊤) {S : Scheme.{u}} (g : X ⟶ S)

include hσ in
lemma span_topIso_inv (i : ι) :
    Ideal.span (Set.range fun a ↦ (𝒟.U i).topIso.inv ((σ a).s i)) = ⊤ := by
  have := Ideal.map_span (𝒟.U i).topIso.inv.hom (Set.range fun a ↦ (σ a).s i)
  rw [hσ i, Ideal.map_top, ← Set.range_comp] at this
  exact this.symm

/-- The morphism on the chart `Uᵢ` defined by the sections `σ`. -/
def localHom (i : ι) : (𝒟.U i).toScheme ⟶ ℙ(α; S) :=
  ProjectiveSpace.homOfSections ((𝒟.U i).ι ≫ g) (fun a ↦ (𝒟.U i).topIso.inv ((σ a).s i))
    (span_topIso_inv σ hσ i)

lemma homOfLE_localHom {V : X.Opens} (i : ι) (h : V ≤ 𝒟.U i) :
    X.homOfLE h ≫ localHom σ hσ g i = ProjectiveSpace.homOfSections (V.ι ≫ g)
      (fun a ↦ V.topIso.inv (X.presheaf.map (homOfLE h).op ((σ a).s i)))
      (by
        have := ProjectiveSpace.span_range_appTop_eq_top (X.homOfLE h) (span_topIso_inv σ hσ i)
        simp only [Scheme.homOfLE_appTop_topIso_inv] at this
        exact this) := by
  rw [localHom, ProjectiveSpace.comp_homOfSections]
  congr 1
  · simp
  · funext a
    exact Scheme.homOfLE_appTop_topIso_inv _ _

lemma localHom_compat (i j : ι) :
    X.homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i) ≫ localHom σ hσ g i =
      X.homOfLE (inf_le_right : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U j) ≫ localHom σ hσ g j := by
  rw [homOfLE_localHom, homOfLE_localHom]
  obtain ⟨u, hu⟩ := (𝒟.isUnit_ratio_map i j).pow N
  refine (ProjectiveSpace.homOfSections_eq_of_unit_mul _
    ((Units.map (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom.toMonoidHom u)⁻¹) _ _ fun a ↦ ?_)
  rw [Units.eq_inv_mul_iff_mul_eq, Units.coe_map]
  change (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _ * (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _ =
    (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _
  rw [← map_mul, hu, ← (σ a).s_eq]

/-- **The morphism to projective space defined by sections.** A family `σ` of sections of the
same degree of a coordinate cover, generating the unit ideal on every chart, defines a morphism
`X ⟶ ℙ(α; S)` over `g`, given on the chart `Uᵢ` by the functions `σₐ,ᵢ`. -/
def hom : X ⟶ ℙ(α; S) :=
  Scheme.Opens.glueMorphismsOfTop 𝒟.U 𝒟.iSup_U (localHom σ hσ g) (localHom_compat σ hσ g)

@[reassoc (attr := simp)]
lemma ι_hom (i : ι) : (𝒟.U i).ι ≫ hom σ hσ g = localHom σ hσ g i :=
  Scheme.Opens.ι_glueMorphismsOfTop _ _ _ _ i

@[reassoc (attr := simp)]
lemma hom_over : hom σ hσ g ≫ ℙ(α; S) ↘ S = g :=
  Scheme.Opens.hom_ext_of_iSup_eq_top 𝒟.U 𝒟.iSup_U _ _ fun i ↦ by
    rw [ι_hom_assoc, localHom, ProjectiveSpace.homOfSections_over]

/-- The preimage of the standard open `D₊(Tₐ)` under the morphism defined by the sections `σ` is
the locus where `σₐ` does not vanish. -/
lemma preimage_hom_standardOpen (a : α) :
    hom σ hσ g ⁻¹ᵁ ProjectiveSpace.standardOpen α S a = (σ a).nonvanishing := by
  have key (i : ι) : (𝒟.U i).ι ''ᵁ ((𝒟.U i).ι ⁻¹ᵁ (hom σ hσ g ⁻¹ᵁ
      ProjectiveSpace.standardOpen α S a)) = X.basicOpen ((σ a).s i) := by
    rw [← Scheme.Hom.comp_preimage, ι_hom, localHom,
      ProjectiveSpace.homOfSections_preimage_standardOpen,
      Scheme.Opens.ι_image_basicOpen_topIso_inv]
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (𝒟.iSup_U.ge (Set.mem_univ x))
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [← key i]
    exact ⟨⟨x, hi⟩, hx, rfl⟩
  · refine iSup_le fun i ↦ ?_
    rw [← key i]
    exact Scheme.Hom.image_preimage_le _ _

end Hom

end Scheme.CoordinateCover

end AlgebraicGeometry
