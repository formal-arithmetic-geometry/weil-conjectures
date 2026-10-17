/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Vector bundles and their zero sections

A *vector bundle of constant rank `c`* over a scheme `Z` is a morphism `p : E ⟶ Z` with a section
`z : Z ⟶ E` which is Zariski-locally on `Z` isomorphic to `(𝔸^c_U ⟶ U, 0)`, the coordinates of two
charts being related by linear substitutions with coefficients in `𝒪_Z`
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas`). This is the geometric vector bundle of
Hartshorne (Exercise II.5.18): the sheaf `ℰ` of fibrewise linear functions on `E` (locally spanned
by the coordinates of a chart) is locally free of rank `c` and `E ≅ Spec_Z (Sym^• ℰ)` over `Z`,
the zero section being defined by the augmentation `Sym^• ℰ ⟶ 𝒪_Z`, which kills the
coordinates. The pinned Mathlib has no relative `Spec` of a quasi-coherent algebra and no
symmetric algebra of a sheaf of modules, so the bundle is described through its linear charts.

A *trivialization* of `E` (`AlgebraicGeometry.Scheme.Hom.VectorBundleTrivialization`) is an étale
`Z' ⟶ Z` with an isomorphism `E ×_Z Z' ≅ 𝔸^c_{Z'}` over `Z'`; the charts of an atlas are
trivializations (`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas.exists_trivialization`), and the
zero section is a closed immersion
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas.isClosedImmersion_zeroSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {E Z : Scheme.{u}}

namespace Scheme.Hom

/-- The `l`-th coordinate function of a chart `φ : p⁻¹(U) ≅ 𝔸^c_U` of `p : E ⟶ Z`, as a section of
`𝒪_E` over `p⁻¹(U)`. -/
noncomputable def chartCoord (p : E ⟶ Z) {U : Z.Opens} {c : ℕ}
    (φ : (p ⁻¹ᵁ U).toScheme ≅ 𝔸(ULift.{u} (Fin c); U)) (l : Fin c) : Γ(E, p ⁻¹ᵁ U) :=
  (p ⁻¹ᵁ U).topIso.hom (φ.hom.appTop (AffineSpace.coord U (ULift.up l)))

/-- Blueprint `def-pur-vector-bundle-zero-section`: Vector bundle with zero section

A *linear atlas of rank `c`* of `p : E ⟶ Z` with section `z`: an open cover `(U_i)` of `Z` with
isomorphisms `φ_i : p⁻¹(U_i) ≅ 𝔸^c_{U_i}` over `U_i` carrying `z` to the zero section, such that
on `U_i ∩ U_j` every coordinate of the chart `φ_j` is a linear combination, with coefficients in
`Γ(U_i ∩ U_j, 𝒪_Z)`, of the coordinates of `φ_i`. -/
structure VectorBundleAtlas (c : ℕ) (p : E ⟶ Z) (z : Z ⟶ E) where
  /-- The index set of the charts. -/
  ι : Type u
  /-- The opens of `Z` over which the bundle is trivialized. -/
  U : ι → Z.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The charts `p⁻¹(U_i) ≅ 𝔸^c_{U_i}`. -/
  chart (i : ι) : (p ⁻¹ᵁ U i).toScheme ≅ 𝔸(ULift.{u} (Fin c); U i)
  chart_hom_over (i : ι) : (chart i).hom ≫ 𝔸(ULift.{u} (Fin c); U i) ↘ U i = p ∣_ U i
  /-- In the charts the section `z` is the zero section, defined by the augmentation. -/
  zeroSection_chart (i : ι) : z ∣_ (p ⁻¹ᵁ U i) ≫ (chart i).hom =
    z ∣_ (p ⁻¹ᵁ U i) ≫ p ∣_ U i ≫ AffineSpace.zeroSection (ULift.{u} (Fin c)) (U i)
  /-- The transition functions are linear. -/
  linear (i j : ι) (k : Fin c) : ∃ a : Fin c → Γ(Z, U i ⊓ U j),
    E.presheaf.map (homOfLE (p.preimage_mono inf_le_right)).op (chartCoord p (chart j) k) =
      ∑ l, p.app (U i ⊓ U j) (a l) *
        E.presheaf.map (homOfLE (p.preimage_mono inf_le_left)).op (chartCoord p (chart i) l)

/-- Blueprint `def-pur-vector-bundle-zero-section`: Vector bundle with zero section

`p : E ⟶ Z` is a *vector bundle of constant rank `c`* with *zero section* `z` if `z` is a section
of `p` and `(p, z)` admits a linear atlas of rank `c`
(`AlgebraicGeometry.Scheme.Hom.VectorBundleAtlas`): Zariski-locally on `Z`, `(E, z)` is
`(𝔸^c, 0)` with linear transition functions, i.e. `E ≅ Spec_Z (Sym^• ℰ)` for the locally free
sheaf `ℰ` of rank `c` of fibrewise linear functions, `z` being given by the augmentation. -/
structure IsVectorBundle (c : ℕ) (p : E ⟶ Z) (z : Z ⟶ E) : Prop where
  zeroSection_comp : z ≫ p = 𝟙 Z
  nonempty_atlas : Nonempty (VectorBundleAtlas c p z)

/-- Blueprint `def-pur-vector-bundle-zero-section`: Vector bundle with zero section

A *trivialization* of `p : E ⟶ Z`: an étale open `v : Z' ⟶ Z` together with an isomorphism
`E ×_Z Z' ≅ 𝔸^c_{Z'}` over `Z'`. -/
structure VectorBundleTrivialization (c : ℕ) (p : E ⟶ Z) where
  /-- The étale open `Z'`. -/
  base : Scheme.{u}
  /-- The étale morphism `Z' ⟶ Z`. -/
  map : base ⟶ Z
  etale_map : Etale map
  /-- The isomorphism `E ×_Z Z' ≅ 𝔸^c_{Z'}`. -/
  iso : pullback p map ≅ 𝔸(ULift.{u} (Fin c); base)
  iso_hom_over : iso.hom ≫ 𝔸(ULift.{u} (Fin c); base) ↘ base = pullback.snd p map

namespace VectorBundleAtlas

variable {c : ℕ} {p : E ⟶ Z} {z : Z ⟶ E}

/-- The chart `p⁻¹(U_i) ≅ 𝔸^c_{U_i}` of an atlas, as a trivialization over the open immersion
`U_i ⟶ Z`. -/
noncomputable def trivialization (A : VectorBundleAtlas c p z) (i : A.ι) :
    VectorBundleTrivialization c p where
  base := A.U i
  map := (A.U i).ι
  etale_map := inferInstance
  iso := pullbackRestrictIsoRestrict p (A.U i) ≪≫ A.chart i
  iso_hom_over := by
    simp [A.chart_hom_over, pullbackRestrictIsoRestrict_hom_morphismRestrict]

/-- Every point of `Z` lies in the image of a trivialization coming from the atlas. -/
lemma exists_trivialization (A : VectorBundleAtlas c p z) (x : Z) :
    ∃ τ : VectorBundleTrivialization c p, x ∈ Set.range τ.map := by
  have hx : x ∈ (⨆ i, A.U i : Z.Opens) := by rw [A.iSup_eq_top]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨A.trivialization i, ⟨⟨x, hi⟩, rfl⟩⟩

end VectorBundleAtlas

/-- Blueprint `def-pur-vector-bundle-zero-section`: Vector bundle with zero section

The zero section of a vector bundle is a closed immersion: in each chart it is the zero section of
`𝔸^c_{U_i}`. -/
theorem IsVectorBundle.isClosedImmersion_zeroSection {c : ℕ} {p : E ⟶ Z} {z : Z ⟶ E}
    (h : IsVectorBundle c p z) : IsClosedImmersion z := by
  obtain ⟨A⟩ := h.nonempty_atlas
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i ↦ p ⁻¹ᵁ A.U i) ?_ fun i ↦ ?_
  · rw [← Scheme.Hom.preimage_iSup, A.iSup_eq_top, Scheme.Hom.preimage_top]
  · have : IsIso (z ≫ p) := by rw [h.zeroSection_comp]; infer_instance
    have hs : IsIso (z ∣_ (p ⁻¹ᵁ A.U i) ≫ p ∣_ A.U i) := by
      rw [← morphismRestrict_comp]; infer_instance
    have : z ∣_ (p ⁻¹ᵁ A.U i) = (z ∣_ (p ⁻¹ᵁ A.U i) ≫ p ∣_ A.U i) ≫
        AffineSpace.zeroSection (ULift.{u} (Fin c)) (A.U i) ≫ (A.chart i).inv := by
      calc z ∣_ (p ⁻¹ᵁ A.U i) = (z ∣_ (p ⁻¹ᵁ A.U i) ≫ (A.chart i).hom) ≫ (A.chart i).inv := by
            simp
        _ = _ := by rw [A.zeroSection_chart i]; simp only [Category.assoc]
    rw [this]
    infer_instance

end Scheme.Hom

end AlgebraicGeometry
