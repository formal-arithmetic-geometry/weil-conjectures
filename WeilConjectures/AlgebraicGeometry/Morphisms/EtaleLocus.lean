/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# The étale locus of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y`, `AlgebraicGeometry.Scheme.Hom.etaleLocus f` is the union
of the opens `U ⊆ X` such that `U ⟶ X ⟶ Y` is étale, that is, the open set of points of `X` at
which `f` is étale in a neighbourhood.

If `f` is integral (hence a closed map), the set of points of `Y` over which `f` is étale at
every point of the fibre is stable under generization
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_of_specializes`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The étale locus of `f : X ⟶ Y`: the union of the opens `U ⊆ X` such that the restriction
`U ⟶ Y` of `f` is étale. -/
def etaleLocus : X.Opens := ⨆ (U : X.Opens) (_ : Etale (U.ι ≫ f)), U

variable {f}

lemma mem_etaleLocus {x : X} :
    x ∈ f.etaleLocus ↔ ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  simp only [etaleLocus, TopologicalSpace.Opens.mem_iSup]
  exact ⟨fun ⟨U, hU, hx⟩ ↦ ⟨U, hx, hU⟩, fun ⟨U, hx, hU⟩ ↦ ⟨U, hU, hx⟩⟩

lemma le_etaleLocus {U : X.Opens} (hU : Etale (U.ι ≫ f)) : U ≤ f.etaleLocus :=
  fun _ hx ↦ mem_etaleLocus.2 ⟨U, hx, hU⟩

/-- A morphism whose étale locus is everything is étale. -/
lemma etale_of_etaleLocus_eq_top (h : f.etaleLocus = ⊤) : Etale f := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun U : {U : X.Opens // Etale (U.ι ≫ f)} ↦ U.1) (top_unique fun x _ ↦ ?_) fun U ↦ U.2
  obtain ⟨U, hxU, hU⟩ := mem_etaleLocus.1 (h.ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩

/-- A morphism is étale on every open contained in its étale locus. -/
lemma etale_of_le_etaleLocus {U : X.Opens} (hU : U ≤ f.etaleLocus) : Etale (U.ι ≫ f) := by
  refine etale_of_etaleLocus_eq_top (top_unique fun x _ ↦ ?_)
  obtain ⟨V, hxV, hV⟩ := mem_etaleLocus.1 (hU x.2)
  refine mem_etaleLocus.2 ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  have hr : Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact y.2
  let g := IsOpenImmersion.lift V.ι _ hr
  have hg : g ≫ V.ι = (U.ι ⁻¹ᵁ V).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion g := by
    have : IsOpenImmersion (g ≫ V.ι) := by rw [hg]; infer_instance
    exact IsOpenImmersion.of_comp g V.ι
  rw [← Category.assoc, ← hg, Category.assoc]
  infer_instance

/-- The étale locus of an étale morphism is everything. -/
lemma etaleLocus_eq_top [Etale f] : f.etaleLocus = ⊤ :=
  top_unique fun _ _ ↦ mem_etaleLocus.2 ⟨⊤, trivial, inferInstance⟩

/-- Over an integral morphism, the set of points of the target over which `f` is étale at every
point of the fibre is stable under generization: the image of the closed complement of the étale
locus is closed. -/
lemma mem_etaleLocus_of_specializes [IsIntegralHom f] {y y' : Y} (h : y' ⤳ y)
    (H : ∀ x : X, f x = y → x ∈ f.etaleLocus) (x' : X) (hx' : f x' = y') :
    x' ∈ f.etaleLocus := by
  by_contra hx
  have hcl : IsClosed (f.base '' (f.etaleLocus : Set X)ᶜ) :=
    f.isClosedMap _ f.etaleLocus.isOpen.isClosed_compl
  obtain ⟨x, hx, rfl⟩ := h.mem_closed hcl ⟨x', hx, hx'⟩
  exact hx (H x rfl)

end AlgebraicGeometry.Scheme.Hom
