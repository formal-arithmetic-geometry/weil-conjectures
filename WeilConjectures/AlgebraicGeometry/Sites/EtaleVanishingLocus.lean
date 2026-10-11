/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections

/-!
# The vanishing locus of a section of an étale sheaf

Let `F` be an abelian sheaf on the small étale site of a scheme `X`, `U` an étale `X`-scheme and
`s` a section of `F` over `U`. The *vanishing locus* of `s` is the set of points `x` of `U` at
which `s` vanishes étale locally: there is an étale `V ⟶ U` whose image contains `x` and on
which `s` restricts to zero. It is open, since étale morphisms are open, and `s = 0` if and only
if its vanishing locus is all of `U`.

For a morphism `t : T ⟶ R` and the pullback `t^* G` of an abelian sheaf `G` on `R`, a section
`g` of `G` over `U` whose pullback `φ^* g` along `φ : V ⟶ U` (over `t`) vanishes, vanishes near
the image of `φ` (`AlgebraicGeometry.Etale.range_subset_vanishingLocus_of_pullSection_eq_zero`).
Consequently, if every nonempty closed subset of `U` meets the image of `φ`, then `φ^* g = 0`
forces `g = 0` (`AlgebraicGeometry.Etale.eq_zero_of_pullSection_eq_zero`): this is the
injectivity half of the comparison of sections over a proper scheme over a henselian pair with
sections over its closed fibre.

## Main definitions

- `AlgebraicGeometry.Etale.vanishingLocus`: the vanishing locus of a section.

## Main statements

- `AlgebraicGeometry.Etale.isOpen_vanishingLocus`: the vanishing locus is open.
- `AlgebraicGeometry.Etale.eq_zero_iff_vanishingLocus_eq_univ`: a section vanishes if and only
  if its vanishing locus is everything.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section VanishingLocus

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The **vanishing locus** of a section `s` of an abelian étale sheaf `F` over an étale
`X`-scheme `U`: the points `x` of `U` such that `s` restricts to zero on some étale `V ⟶ U`
whose image contains `x`. -/
def vanishingLocus {U : X.Etale} (s : F.obj.obj (op U)) : Set U.left :=
  {x | ∃ (V : X.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧ F.obj.map a.op s = 0}

variable {F}

lemma mem_vanishingLocus_of_map_eq_zero {U V : X.Etale} (a : V ⟶ U) {s : F.obj.obj (op U)}
    (hs : F.obj.map a.op s = 0) (v : V.left) : a.left v ∈ vanishingLocus F s :=
  ⟨V, a, ⟨v, rfl⟩, hs⟩

/-- The vanishing locus of a section is open: it is the union of the images of the étale
morphisms on which the section vanishes. -/
lemma isOpen_vanishingLocus {U : X.Etale} (s : F.obj.obj (op U)) :
    IsOpen (vanishingLocus F s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨V, a, hx, hs⟩
  refine ⟨Set.range a.left, ?_, a.left.isOpenMap.isOpen_range, hx⟩
  rintro _ ⟨v, rfl⟩
  exact mem_vanishingLocus_of_map_eq_zero a hs v

lemma vanishingLocus_zero {U : X.Etale} : vanishingLocus F (0 : F.obj.obj (op U)) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ ⟨U, 𝟙 U, ⟨x, rfl⟩, map_zero _⟩

/-- A section vanishes if and only if its vanishing locus is everything. -/
lemma eq_zero_iff_vanishingLocus_eq_univ {U : X.Etale} (s : F.obj.obj (op U)) :
    s = 0 ↔ vanishingLocus F s = Set.univ := by
  refine ⟨fun h ↦ h ▸ vanishingLocus_zero, fun h ↦ ?_⟩
  have hx : ∀ x : U.left, ∃ (V : X.Etale) (a : V ⟶ U), x ∈ Set.range a.left ∧
      F.obj.map a.op s = 0 := fun x ↦ by
    change x ∈ vanishingLocus F s
    rw [h]
    trivial
  choose V a ha hs using hx
  exact eq_zero_of_forall_map_eq_zero F a (fun x ↦ ⟨x, ha x⟩) s hs

lemma eq_zero_of_forall_mem_vanishingLocus {U : X.Etale} {s : F.obj.obj (op U)}
    (h : ∀ x, x ∈ vanishingLocus F s) : s = 0 :=
  (eq_zero_iff_vanishingLocus_eq_univ s).2 (Set.eq_univ_of_forall h)

/-- The vanishing locus of the restriction of `s` along `a : V ⟶ U` is the preimage of the
vanishing locus of `s`. -/
lemma vanishingLocus_map {U V : X.Etale} (a : V ⟶ U) (s : F.obj.obj (op U)) :
    vanishingLocus F (F.obj.map a.op s) = a.left ⁻¹' vanishingLocus F s := by
  ext v
  refine ⟨fun ⟨W, b, ⟨w, hw⟩, hs⟩ ↦ ?_, fun ⟨W, b, ⟨w, hw⟩, hs⟩ ↦ ?_⟩
  · refine ⟨W, b ≫ a, ⟨w, by simp [hw]⟩, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs]
  · -- the point `(v, w)` of `V ×_U W`
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback v w (hw.symm)
    refine ⟨overlap a b, overlapFst a b, ⟨z, by simpa using hz₁⟩, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      show overlapFst a b ≫ a = overlapSnd a b ≫ b from
        MorphismProperty.Over.Hom.ext (by simp [pullback.condition]),
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]

lemma vanishingLocus_neg {U : X.Etale} (s : F.obj.obj (op U)) :
    vanishingLocus F (-s) = vanishingLocus F s := by
  ext x
  refine ⟨fun ⟨V, a, hx, hs⟩ ↦ ⟨V, a, hx, ?_⟩, fun ⟨V, a, hx, hs⟩ ↦ ⟨V, a, hx, ?_⟩⟩
  · simpa using hs
  · simp [hs]

/-- The vanishing locus of a sum contains the intersection of the vanishing loci. -/
lemma inter_vanishingLocus_subset_add {U : X.Etale} (s₁ s₂ : F.obj.obj (op U)) :
    vanishingLocus F s₁ ∩ vanishingLocus F s₂ ⊆ vanishingLocus F (s₁ + s₂) := by
  rintro x ⟨⟨V₁, a₁, ⟨v₁, hv₁⟩, hs₁⟩, ⟨V₂, a₂, ⟨v₂, hv₂⟩, hs₂⟩⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback v₁ v₂ (hv₁.trans hv₂.symm)
  refine ⟨overlap a₁ a₂, overlapFst a₁ a₂ ≫ a₁, ⟨z, by simp [hz₁, hv₁]⟩, ?_⟩
  have e : overlapFst a₁ a₂ ≫ a₁ = overlapSnd a₁ a₂ ≫ a₂ :=
    MorphismProperty.Over.Hom.ext (by simp [pullback.condition])
  rw [map_add]
  nth_rw 2 [e]
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs₁, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply, hs₂, map_zero, map_zero, add_zero]

lemma inter_vanishingLocus_subset_sub {U : X.Etale} (s₁ s₂ : F.obj.obj (op U)) :
    vanishingLocus F s₁ ∩ vanishingLocus F s₂ ⊆ vanishingLocus F (s₁ - s₂) := by
  rw [sub_eq_add_neg, ← vanishingLocus_neg s₂]
  exact inter_vanishingLocus_subset_add _ _

end VanishingLocus

section PullSection

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- If the pullback `φ^* g` of a section `g` of `G` over `U` along `φ : V ⟶ U` (over `t`)
vanishes, then `g` vanishes near the image of `φ`. -/
lemma range_subset_vanishingLocus_of_pullSection_eq_zero {V : T.Etale} {U : R.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U))
    (h : pullSection t G φ hφ g = 0) : Set.range φ ⊆ vanishingLocus G g := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨V', a, U', b, φ', -, ⟨x', hx'⟩, hfac, hg⟩ :=
    exists_of_pullSection_eq_zero t G φ hφ g h x
  refine ⟨U', b, ⟨φ' x', ?_⟩, hg⟩
  rw [← hx', ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]

/-- **Injectivity of pullback of sections.** If every nonempty closed subset of `U` meets the
image of `φ : V ⟶ U` (over `t`), then a section `g` of `G` over `U` with `φ^* g = 0` vanishes.
For a proper scheme over a henselian pair and its closed fibre, this is the injectivity of
the restriction of sections to the closed fibre. -/
lemma eq_zero_of_pullSection_eq_zero {V : T.Etale} {U : R.Etale}
    (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t)
    (hC : ∀ C : Set U.left, IsClosed C → C.Nonempty → (C ∩ Set.range φ).Nonempty)
    (g : G.obj.obj (op U)) (h : pullSection t G φ hφ g = 0) : g = 0 := by
  have h₁ := range_subset_vanishingLocus_of_pullSection_eq_zero t G φ hφ g h
  refine eq_zero_of_forall_mem_vanishingLocus fun x ↦ ?_
  by_contra hx
  obtain ⟨y, hy, hyφ⟩ := hC _ (isOpen_vanishingLocus g).isClosed_compl ⟨x, hx⟩
  exact hy (h₁ hyφ)

end PullSection

end AlgebraicGeometry.Etale
