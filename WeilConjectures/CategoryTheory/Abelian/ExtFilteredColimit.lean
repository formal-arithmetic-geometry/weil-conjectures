/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# `Ext` out of a fixed object and filtered colimits

Let `C` be an abelian category with exact filtered colimits of shape `J` and `G` an object of
`C`. We show that the functors `Extᵠ(G, -)` commute with colimits of shape `J`, in the
elementwise sense of `CategoryTheory.Abelian.Ext.CommutesWithColimit`, provided

* `Hom(G, -) = Ext⁰(G, -)` commutes with colimits of shape `J`, and
* a colimit of a `J`-diagram of injective objects has no higher `Ext` out of `G`.

The proof is by dimension shifting along a short exact sequence of diagrams `0 → D → I → Q → 0`,
where `I` is the diagram `j ↦ ∏_{j ⟶ k} I(D_k)` of injective objects built from injective
hulls `D_k ⟶ I(D_k)` (`CategoryTheory.Abelian.Ext.injectiveDiagram`). Taking the colimit is
exact, and the long exact `Ext`-sequences together with the induction hypothesis for `I` and
`Q` give the result.

## Main definitions

- `CategoryTheory.Abelian.Ext.CommutesWithColimit`: every class in `Extᵠ(G, colim D)` comes from
  some `Extᵠ(G, D_j)`, and a class in `Extᵠ(G, D_j)` which vanishes in `Extᵠ(G, colim D)`
  vanishes in some `Extᵠ(G, D_k)`, `j ⟶ k`.

## Main statements

- `CategoryTheory.Abelian.Ext.commutesWithColimit_of_isFiltered`: the dimension shifting
  argument.
-/

@[expose] public section

universe w t v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C]

/-- `Extᵠ(G, -)` commutes with the colimit of the cocone `c`, elementwise: every class in
`Extᵠ(G, c.pt)` comes from some `Extᵠ(G, D_j)`, and a class in `Extᵠ(G, D_j)` which vanishes in
`Extᵠ(G, c.pt)` already vanishes in some `Extᵠ(G, D_k)`, `j ⟶ k`. -/
def CommutesWithColimit [Abelian C] [HasExt.{w} C] (G : C) (q : ℕ) {J : Type*} [Category J]
    {D : J ⥤ C} (c : Cocone D) :
    Prop :=
  (∀ x : Ext.{w} G c.pt q, ∃ (j : J) (y : Ext.{w} G (D.obj j) q),
    y.comp (mk₀ (c.ι.app j)) (add_zero q) = x) ∧
  ∀ (j : J) (y : Ext.{w} G (D.obj j) q), y.comp (mk₀ (c.ι.app j)) (add_zero q) = 0 →
    ∃ (k : J) (φ : j ⟶ k), y.comp (mk₀ (D.map φ)) (add_zero q) = 0

/-- A product of injective objects, over an index type in any universe, is injective. -/
lemma injective_piObj {β : Type*} (f : β → C) [HasProduct f] [∀ b, Injective (f b)] :
    Injective (∏ᶜ f) where
  factors g h _ := ⟨Pi.lift fun b ↦ Injective.factorThru (g ≫ Pi.π f b) h, by
    refine Pi.hom_ext _ _ fun b ↦ ?_
    simp⟩

variable [Abelian C]

section Diagram

variable [EnoughInjectives C] {J : Type t} [SmallCategory J] [HasProducts.{t} C]

/-- The diagram `j ↦ ∏_{j ⟶ k} I(D_k)` of injective objects, where `D_k ⟶ I(D_k)` is the
chosen injective hull. -/
@[simps]
noncomputable def injectiveDiagram (D : J ⥤ C) : J ⥤ C where
  obj j := ∏ᶜ fun p : Σ k, j ⟶ k ↦ Injective.under (D.obj p.1)
  map {j j'} f := Pi.lift fun p ↦ Pi.π (fun p : Σ k, j ⟶ k ↦ Injective.under (D.obj p.1))
    ⟨p.1, f ≫ p.2⟩
  map_id j := Pi.hom_ext _ _ fun p ↦ by
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    rw [Category.id_comp, Category.id_comp]
  map_comp f g := Pi.hom_ext _ _ fun p ↦ by
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.assoc]
    rw [Category.assoc]

instance (D : J ⥤ C) (j : J) : Injective ((injectiveDiagram D).obj j) :=
  injective_piObj _

/-- The embedding of a diagram into its diagram of injective objects. -/
@[simps]
noncomputable def toInjectiveDiagram (D : J ⥤ C) : D ⟶ injectiveDiagram D where
  app j := Pi.lift fun p ↦ D.map p.2 ≫ Injective.ι (D.obj p.1)
  naturality j j' f := Pi.hom_ext _ _ fun p ↦ by simp

instance (D : J ⥤ C) : Mono (toInjectiveDiagram D) := by
  have (j : J) : Mono ((toInjectiveDiagram D).app j) := by
    have : Mono ((toInjectiveDiagram D).app j ≫
        Pi.π (fun p : Σ k, j ⟶ k ↦ Injective.under (D.obj p.1)) ⟨j, 𝟙 j⟩) := by
      simp only [toInjectiveDiagram_app, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
      infer_instance
    exact mono_of_mono _ (Pi.π (fun p : Σ k, j ⟶ k ↦ Injective.under (D.obj p.1)) ⟨j, 𝟙 j⟩)
  exact NatTrans.mono_of_mono_app _

/-- The short exact sequence of diagrams `0 → D → I → Q → 0`, where `I` is
`CategoryTheory.Abelian.Ext.injectiveDiagram D`. -/
noncomputable abbrev injectiveDiagramShortComplex (D : J ⥤ C) : ShortComplex (J ⥤ C) :=
  ShortComplex.mk (toInjectiveDiagram D) (cokernel.π _) (cokernel.condition _)

lemma shortExact_injectiveDiagramShortComplex (D : J ⥤ C) :
    (injectiveDiagramShortComplex D).ShortExact :=
  .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

end Diagram

section Main

variable [EnoughInjectives C] {J : Type t} [SmallCategory J] [HasProducts.{t} C]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- The colimit `0 → c.pt → colim I → colim Q → 0` of the short exact sequence of diagrams
`CategoryTheory.Abelian.Ext.injectiveDiagramShortComplex D`, for a colimit cocone `c` of `D`. -/
noncomputable abbrev colimitShortComplex {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    ShortComplex C :=
  ShortComplex.mk (hc.desc (Cocone.mk _ (toInjectiveDiagram D ≫ (colimit.cocone _).ι)))
    (colim.map (cokernel.π (toInjectiveDiagram D))) (hc.hom_ext fun j ↦ by
      rw [hc.fac_assoc, Limits.comp_zero]
      simp only [colimit.cocone_x, NatTrans.comp_app, colimit.cocone_ι, Category.assoc, colim_map,
        ι_colimMap]
      rw [← Category.assoc, ← NatTrans.comp_app, cokernel.condition, NatTrans.app_zero,
        Limits.zero_comp])

lemma shortExact_colimitShortComplex {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    (colimitShortComplex hc).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    ((shortExact_injectiveDiagramShortComplex D).map_of_exact colim)
  refine ShortComplex.isoMk ((colimit.isColimit D).coconePointUniqueUpToIso hc) (Iso.refl _)
    (Iso.refl _) (colimit.hom_ext fun j ↦ ?_) (by simp)
  simp

/-- The morphism from the `j`-th member of the short exact sequence of diagrams to its
colimit. -/
noncomputable def toColimitShortComplex {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) (j : J) :
    (injectiveDiagramShortComplex D).map ((evaluation J C).obj j) ⟶ colimitShortComplex hc :=
  ShortComplex.homMk (c.ι.app j) (colimit.ι (injectiveDiagram D) j)
    (colimit.ι (cokernel (toInjectiveDiagram D)) j) (by simp) (by simp)

/-- The transition morphisms of the short exact sequence of diagrams. -/
noncomputable def injectiveDiagramShortComplexMap (D : J ⥤ C) {j k : J} (f : j ⟶ k) :
    (injectiveDiagramShortComplex D).map ((evaluation J C).obj j) ⟶
      (injectiveDiagramShortComplex D).map ((evaluation J C).obj k) :=
  ShortComplex.homMk (D.map f) ((injectiveDiagram D).map f)
    ((cokernel (toInjectiveDiagram D)).map f) ((toInjectiveDiagram D).naturality f)
    ((cokernel.π (toInjectiveDiagram D)).naturality f)

variable [IsFiltered J] [HasExt.{w} C]

/-- **`Ext` out of a fixed object commutes with filtered colimits.** Let `C` be an abelian
category with exact colimits of the filtered shape `J`, and `G` an object of `C`. Suppose that
`Hom(G, -) = Ext⁰(G, -)` commutes with colimits of shape `J`, and that colimits of `J`-diagrams
of injective objects have no higher `Ext` out of `G`. Then every `Extᵠ(G, -)` commutes with
colimits of shape `J`.

This is proven by induction on `q`, dimension shifting along the short exact sequence of
diagrams `0 → D → I → Q → 0` of `CategoryTheory.Abelian.Ext.injectiveDiagramShortComplex`. -/
theorem commutesWithColimit_of_isFiltered (G : C)
    (h₀ : ∀ (D : J ⥤ C) (c : Cocone D), IsColimit c → CommutesWithColimit.{w} G 0 c)
    (hI : ∀ (D : J ⥤ C) (c : Cocone D), IsColimit c → (∀ j, Injective (D.obj j)) →
      ∀ (q : ℕ) (x : Ext.{w} G c.pt (q + 1)), x = 0) (q : ℕ) :
    ∀ (D : J ⥤ C) (c : Cocone D), IsColimit c → CommutesWithColimit.{w} G q c := by
  induction q with
  | zero => exact h₀
  | succ q ih =>
  intro D c hc
  let S := injectiveDiagramShortComplex D
  have hS := shortExact_injectiveDiagramShortComplex D
  have hSj (j : J) : (S.map ((evaluation J C).obj j)).ShortExact := hS.map_of_exact _
  have hS' : (colimitShortComplex hc).ShortExact := shortExact_colimitShortComplex hc
  have hIQ := ih _ _ (colimit.isColimit (cokernel (toInjectiveDiagram D)))
  have hII := ih _ _ (colimit.isColimit (injectiveDiagram D))
  -- naturality of the connecting morphisms
  have nat (j : J) (z : Ext.{w} G ((cokernel (toInjectiveDiagram D)).obj j) q) :
      (z.comp (hSj j).extClass rfl).comp (mk₀ (c.ι.app j)) (add_zero _) =
        (z.comp (mk₀ (colimit.ι _ j)) (add_zero q)).comp hS'.extClass rfl := by
    have := (hSj j).extClass_naturality hS' (toColimitShortComplex hc j)
    rw [comp_assoc_of_third_deg_zero, comp_assoc_of_second_deg_zero]
    exact congrArg (fun e ↦ z.comp e rfl) this
  have nat' {j k : J} (f : j ⟶ k) (z : Ext.{w} G ((cokernel (toInjectiveDiagram D)).obj j) q) :
      (z.comp (hSj j).extClass rfl).comp (mk₀ (D.map f)) (add_zero _) =
        (z.comp (mk₀ ((cokernel (toInjectiveDiagram D)).map f)) (add_zero q)).comp
          (hSj k).extClass rfl := by
    have := (hSj j).extClass_naturality (hSj k) (injectiveDiagramShortComplexMap D f)
    rw [comp_assoc_of_third_deg_zero, comp_assoc_of_second_deg_zero]
    exact congrArg (fun e ↦ z.comp e rfl) this
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ G hS' x
      (hI _ _ (colimit.isColimit _) (fun j ↦ inferInstance) q _) rfl
    obtain ⟨j, z, rfl⟩ := hIQ.1 y
    exact ⟨j, z.comp (hSj j).extClass rfl, nat j z⟩
  · have : Injective ((S.map ((evaluation J C).obj j)).X₂) :=
      inferInstanceAs (Injective ((injectiveDiagram D).obj j))
    obtain ⟨z, rfl⟩ := covariant_sequence_exact₁ G (hSj j) y (eq_zero_of_injective _) rfl
    rw [nat] at hy
    obtain ⟨w', hw⟩ := covariant_sequence_exact₃ G hS' _ rfl hy
    obtain ⟨k, w, rfl⟩ := hII.1 w'
    let l := IsFiltered.max j k
    let a : j ⟶ l := IsFiltered.leftToMax j k
    let b : k ⟶ l := IsFiltered.rightToMax j k
    let t := z.comp (mk₀ ((cokernel (toInjectiveDiagram D)).map a)) (add_zero q) -
      w.comp (mk₀ ((injectiveDiagram D).map b ≫ (cokernel.π (toInjectiveDiagram D)).app l))
        (add_zero q)
    have ht : t.comp (mk₀ (colimit.ι _ l)) (add_zero q) = 0 := by
      simp only [t, sub_eq_add_neg, add_comp, neg_comp, comp_assoc_of_third_deg_zero,
        mk₀_comp_mk₀, colimit.w]
      rw [← sub_eq_add_neg, sub_eq_zero, ← hw]
      simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
      congr 2
      simp only [colim_map, colimit.cocone_ι, ι_colimMap]
      rw [Category.assoc, NatTrans.naturality_assoc, colimit.w]
    obtain ⟨m, φ, hφ⟩ := hIQ.2 l t ht
    refine ⟨m, a ≫ φ, ?_⟩
    rw [nat']
    have e : z.comp (mk₀ ((cokernel (toInjectiveDiagram D)).map (a ≫ φ))) (add_zero q) =
        t.comp (mk₀ ((cokernel (toInjectiveDiagram D)).map φ)) (add_zero q) +
          (w.comp (mk₀ ((injectiveDiagram D).map b ≫ (injectiveDiagram D).map φ))
            (add_zero q)).comp (mk₀ ((cokernel.π (toInjectiveDiagram D)).app m)) (add_zero q) := by
      simp only [t, sub_eq_add_neg, add_comp, neg_comp, comp_assoc_of_third_deg_zero,
        mk₀_comp_mk₀, Functor.map_comp,
        Category.assoc, NatTrans.naturality, NatTrans.naturality_assoc]
      abel
    rw [e, hφ, zero_add, comp_assoc_of_second_deg_zero]
    erw [(hSj m).comp_extClass]
    rw [comp_zero]

end Main

end CategoryTheory.Abelian.Ext
