/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Source Hom as the double colimit of numerators

Source: Stacks Project, Derived Categories, Tag 0FND, first three equalities
(blueprint: lem-pc-derived-adjunction-source-colimit).
-/

@[expose] public section

universe u v u' v' uE vE

namespace CategoryTheory

/-- The double colimit of numerators maps bijectively to Hom into the ind value.
No adjunction or pro value is required.

Source: Stacks Project, Derived Categories, Tag 0FND, first three equalities
(blueprint: lem-pc-derived-adjunction-source-colimit).

Proof: The displayed formula is a cocone on the product diagram: incoming triangles
preserve right fractions, and outgoing triangles commute with the chosen cocone.
Descend it to ColimitType. For surjectivity, choose the section at s₀ and represent
h followed by that section by a right fraction. Its composite with p at s₀ is h.
For injectivity, choose representatives (s,t,f) and (s',t',g) with equal images. Apply
the factorization clause at s and s'. Choose a common later stage of the two resulting
stages, then coequalize the two induced arrows from s₀. At this final stage both
transitions factor through their cocone legs, the same section, and the same transition
from s₀. The assumed equality therefore implies equality of the transported right
fractions. The right fraction equality criterion supplies a common incoming denominator
with equal numerators. These two triangles identify the original elements of the
product ColimitType. The representative formula holds by construction. -/
theorem derivedAdjunction_source_colimit
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type uE} [Category.{vE} E]
    (W : MorphismProperty C) (W' : MorphismProperty D)
    [W'.HasRightCalculusOfFractions] (Q : D ⥤ E) [Q.IsLocalization W']
    (F : C ⥤ D) (K : C) (M : D) (V : E) :
    let R := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ F ⋙ Q
    IsEssentiallyConstantIndDiagram R V →
    ∀ p : R ⟶ (Functor.const _).obj V,
      (∃ (s₀ : W.Under ⊤ K) (a : V ⟶ R.obj s₀),
        a ≫ p.app s₀ = 𝟙 V ∧
          ∀ s, ∃ (s₁ : W.Under ⊤ K) (b : s₀ ⟶ s₁) (c : s ⟶ s₁),
            R.map c = p.app s ≫ a ≫ R.map b) →
      ∃ φ : (derivedAdjunctionHomDiagram W W' F K M).ColimitType → (Q.obj M ⟶ V),
        Function.Bijective φ ∧
          ∀ (s : W.Under ⊤ K) (t : W'.Over ⊤ M) (f : t.left ⟶ F.obj s.right),
            φ ((derivedAdjunctionHomDiagram W W' F K M).ιColimitType
              (s, Opposite.op t) f) =
              (MorphismProperty.RightFraction.mk t.hom t.prop f).map Q
                (Localization.inverts Q W') ≫ p.app s := by
  classical
  intro R h p hp
  have : IsFiltered (W.Under ⊤ K) := h.1
  obtain ⟨s₀, a, ha, hfac⟩ := hp
  let H := derivedAdjunctionHomDiagram W W' F K M
  let c : H.CoconeTypes := {
    pt := Q.obj M ⟶ V
    ι j f := (MorphismProperty.RightFraction.mk j.2.unop.hom j.2.unop.prop f).map
      Q (Localization.inverts Q W') ≫ p.app j.1
    ι_naturality := by
      intro j j' b
      funext f
      change j.2.unop.left ⟶ F.obj j.1.right at f
      have ht := Localization.inverts Q W' j.2.unop.hom j.2.unop.prop
      have ht' := Localization.inverts Q W' j'.2.unop.hom j'.2.unop.prop
      have hb : inv (Q.map j'.2.unop.hom) ≫ Q.map b.2.unop.left =
          inv (Q.map j.2.unop.hom) := by
        apply (cancel_mono (Q.map j.2.unop.hom)).1
        rw [Category.assoc, ← Q.map_comp, MorphismProperty.Over.w b.2.unop]
        simp
      dsimp [H, derivedAdjunctionHomDiagram]
      simp only [MorphismProperty.RightFraction.map, Functor.map_comp, Category.assoc]
      rw [← Category.assoc (inv (Q.map j'.2.unop.hom)), hb]
      have hp : Q.map (F.map b.1.right) ≫ p.app j'.1 = p.app j.1 := by
        exact (p.naturality b.1).trans (Category.comp_id _)
      with_unfolding_all rw [hp]
    }
  refine ⟨H.descColimitType c, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨⟨s, t⟩, f, rfl⟩ := H.ιColimitType_jointly_surjective x
    obtain ⟨⟨s', t'⟩, g, rfl⟩ := H.ιColimitType_jointly_surjective y
    obtain ⟨i, b, d, hd⟩ := hfac s
    obtain ⟨j, b', d', hd'⟩ := hfac s'
    obtain ⟨z, q, q', _⟩ := IsFilteredOrEmpty.cocone_objs i j
    obtain ⟨w, v, hv⟩ := IsFilteredOrEmpty.cocone_maps (b ≫ q) (b' ≫ q')
    let ds : s ⟶ w := d ≫ q ≫ v
    let ds' : s' ⟶ w := d' ≫ q' ≫ v
    let bs : s₀ ⟶ w := b ≫ q ≫ v
    have hds : R.map ds = p.app s ≫ a ≫ R.map bs := by
      dsimp [ds, bs]
      simp only [Functor.map_comp, hd, Category.assoc]
    have hds' : R.map ds' = p.app s' ≫ a ≫ R.map bs := by
      dsimp [ds', bs]
      rw [Functor.map_comp, hd']
      have he : R.map (b' ≫ q' ≫ v) = R.map (b ≫ q ≫ v) := by
        simpa only [Category.assoc] using congrArg R.map hv.symm
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z => p.app s' ≫ a ≫ z) he
    let ft : t.unop.left ⟶ F.obj w.right := f ≫ F.map ds.right
    let gt : t'.unop.left ⟶ F.obj w.right := g ≫ F.map ds'.right
    have hfrac : (MorphismProperty.RightFraction.mk t.unop.hom t.unop.prop ft).map
        Q (Localization.inverts Q W') =
        (MorphismProperty.RightFraction.mk t'.unop.hom t'.unop.prop gt).map
          Q (Localization.inverts Q W') := by
      change c.ι (s, t) f = c.ι (s', t') g at hxy
      change Q.map (F.map ds.right) = p.app s ≫ a ≫ R.map bs at hds
      change Q.map (F.map ds'.right) = p.app s' ≫ a ≫ R.map bs at hds'
      have he := congrArg (fun z => z ≫ a ≫ R.map bs) hxy
      dsimp [c] at he
      rw [← Category.assoc _ a, ← Category.assoc _ a] at he
      simpa only [ft, gt, MorphismProperty.RightFraction.map, Functor.map_comp,
        Category.assoc, hds, hds'] using he
    obtain ⟨P, q₁, q₂, hs, hf, hw⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff Q W' _ _).mp hfrac
    let t'' : W'.Over ⊤ M := MorphismProperty.Over.mk ⊤ (q₁ ≫ t.unop.hom) hw
    let bt : t'' ⟶ t.unop := MorphismProperty.Over.homMk q₁ rfl
    let bt' : t'' ⟶ t'.unop := MorphismProperty.Over.homMk q₂ hs.symm
    apply H.ιColimitType_eq_of_map_eq_map f g
      (k := (w, Opposite.op t'')) (ds, bt.op) (ds', bt'.op)
    exact hf
  · intro h
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q W' (h ≫ a)
    let t : W'.Over ⊤ M := MorphismProperty.Over.mk ⊤ φ.s φ.hs
    refine ⟨H.ιColimitType (s₀, Opposite.op t) φ.f, ?_⟩
    change φ.map Q (Localization.inverts Q W') ≫ p.app s₀ = h
    rw [← hφ, Category.assoc, ha, Category.comp_id]
  · intro s t f
    rfl

end CategoryTheory
