/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Target Hom as the double colimit of numerators

Source: Stacks Project, Derived Categories, Tag 0FND, last three equalities
(blueprint: lem-pc-derived-adjunction-target-colimit).
-/

@[expose] public section

universe u v u' v' uE vE

namespace CategoryTheory

/-- Transposing numerators identifies their double colimit with Hom out of the pro value.
No localized right functor or ind value is required.

Source: Stacks Project, Derived Categories, Tag 0FND, last three equalities
(blueprint: lem-pc-derived-adjunction-target-colimit).

Proof: Transpose each numerator by the adjunction and take its left fraction, preceded
by the chosen cone leg. Adjunction naturality and the commuting denominator triangles
make this a cocone on the product diagram, which descends to ColimitType. For
surjectivity, choose the retraction at t₀ and represent that retraction followed by h
as a left fraction. The adjunction takes its numerator back to an element of the
original diagram, and the splitting equation makes its image h. For injectivity,
choose representatives (s,t,f) and (s',t',g) with equal images. Cofilteredness supplies
a common earlier stage of t and t'. Apply the factorization clause at that stage.
Both resulting transitions factor through the same retraction and the respective
cone legs. Precomposing the assumed equality gives equality of the transported left
fractions. The left fraction equality criterion supplies a common outgoing denominator
with equal transposed numerators. Injectivity and naturality of the adjunction then
identify the original numerators at this common product stage, hence their ColimitType
elements. The representative formula holds by construction. -/
theorem derivedAdjunction_target_colimit
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type uE} [Category.{vE} E]
    (W : MorphismProperty C) (W' : MorphismProperty D)
    [W.HasLeftCalculusOfFractions] (Q : C ⥤ E) [Q.IsLocalization W]
    (F : C ⥤ D) (G : D ⥤ C) (adj : G ⊣ F) (K : C) (M : D) (U : E) :
    let L := MorphismProperty.Over.forget W' ⊤ M ⋙ Over.forget M ⋙ G ⋙ Q
    IsEssentiallyConstantProDiagram L U →
    ∀ u : (Functor.const _).obj U ⟶ L,
      (∃ (t₀ : W'.Over ⊤ M) (a : L.obj t₀ ⟶ U),
        u.app t₀ ≫ a = 𝟙 U ∧
          ∀ t, ∃ (t₁ : W'.Over ⊤ M) (b : t₁ ⟶ t₀) (c : t₁ ⟶ t),
            L.map c = L.map b ≫ a ≫ u.app t) →
      ∃ φ : (derivedAdjunctionHomDiagram W W' F K M).ColimitType → (U ⟶ Q.obj K),
        Function.Bijective φ ∧
          ∀ (s : W.Under ⊤ K) (t : W'.Over ⊤ M) (f : t.left ⟶ F.obj s.right),
            φ ((derivedAdjunctionHomDiagram W W' F K M).ιColimitType
              (s, Opposite.op t) f) =
              u.app t ≫ (MorphismProperty.LeftFraction.mk
                ((adj.homEquiv t.left s.right).symm f) s.hom s.prop).map Q
                (Localization.inverts Q W) := by
  classical
  intro L h u hu
  have : IsCofiltered (W'.Over ⊤ M) := h.1
  obtain ⟨t₀, a, ha, hfac⟩ := hu
  let H := derivedAdjunctionHomDiagram W W' F K M
  let c : H.CoconeTypes := {
    pt := U ⟶ Q.obj K
    ι j f := u.app j.2.unop ≫
      (MorphismProperty.LeftFraction.mk ((adj.homEquiv _ _).symm f) j.1.hom j.1.prop).map
        Q (Localization.inverts Q W)
    ι_naturality := by
      intro j j' b
      funext f
      change j.2.unop.left ⟶ F.obj j.1.right at f
      have hs := Localization.inverts Q W j.1.hom j.1.prop
      have hs' := Localization.inverts Q W j'.1.hom j'.1.prop
      have hb : Q.map b.1.right ≫ inv (Q.map j'.1.hom) = inv (Q.map j.1.hom) := by
        apply (cancel_epi (Q.map j.1.hom)).1
        rw [← Category.assoc, ← Q.map_comp, MorphismProperty.Under.w b.1]
        simp
      have ht : u.app j'.2.unop ≫ Q.map (G.map b.2.unop.left) = u.app j.2.unop := by
        exact (u.naturality b.2.unop).symm.trans (Category.id_comp _)
      dsimp [H, derivedAdjunctionHomDiagram]
      rw [← Category.assoc, adj.homEquiv_naturality_right_symm,
        adj.homEquiv_naturality_left_symm]
      simp only [MorphismProperty.LeftFraction.map, Functor.map_comp, Category.assoc]
      with_unfolding_all rw [hb, ← Category.assoc, ht]
    }
  refine ⟨H.descColimitType c, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨⟨s, t⟩, f, rfl⟩ := H.ιColimitType_jointly_surjective x
    obtain ⟨⟨s', t'⟩, g, rfl⟩ := H.ιColimitType_jointly_surjective y
    obtain ⟨v, q, q', _⟩ := IsCofilteredOrEmpty.cone_objs t.unop t'.unop
    obtain ⟨w, b, d, hd⟩ := hfac v
    let dt : w ⟶ t.unop := d ≫ q
    let dt' : w ⟶ t'.unop := d ≫ q'
    have hdt : L.map dt = L.map b ≫ a ≫ u.app t.unop := by
      dsimp [dt]
      rw [Functor.map_comp, hd]
      simp only [Category.assoc]
      have hn : u.app v ≫ L.map q = u.app t.unop := by
        exact (u.naturality q).symm.trans (Category.id_comp _)
      rw [hn]
    have hdt' : L.map dt' = L.map b ≫ a ≫ u.app t'.unop := by
      dsimp [dt']
      rw [Functor.map_comp, hd]
      simp only [Category.assoc]
      have hn : u.app v ≫ L.map q' = u.app t'.unop := by
        exact (u.naturality q').symm.trans (Category.id_comp _)
      rw [hn]
    let ft : G.obj w.left ⟶ s.right :=
      G.map dt.left ≫ (adj.homEquiv t.unop.left s.right).symm f
    let gt : G.obj w.left ⟶ s'.right :=
      G.map dt'.left ≫ (adj.homEquiv t'.unop.left s'.right).symm g
    have hfrac : (MorphismProperty.LeftFraction.mk ft s.hom s.prop).map
        Q (Localization.inverts Q W) =
        (MorphismProperty.LeftFraction.mk gt s'.hom s'.prop).map
          Q (Localization.inverts Q W) := by
      change c.ι (s, t) f = c.ι (s', t') g at hxy
      change Q.map (G.map dt.left) = L.map b ≫ a ≫ u.app t.unop at hdt
      change Q.map (G.map dt'.left) = L.map b ≫ a ≫ u.app t'.unop at hdt'
      have he := congrArg (fun z => L.map b ≫ a ≫ z) hxy
      dsimp [c] at he
      simpa only [ft, gt, MorphismProperty.LeftFraction.map, Functor.map_comp,
        hdt, hdt', Category.assoc] using he
    obtain ⟨I, q₁, q₂, hs, hf, hw⟩ :=
      (MorphismProperty.LeftFraction.map_eq_iff Q W _ _).mp hfrac
    let s'' : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ (s.hom ≫ q₁) hw
    let bs : s ⟶ s'' := MorphismProperty.Under.homMk q₁ rfl
    let bs' : s' ⟶ s'' := MorphismProperty.Under.homMk q₂ hs.symm
    apply H.ιColimitType_eq_of_map_eq_map f g
      (k := (s'', Opposite.op w)) (bs, dt.op) (bs', dt'.op)
    apply (adj.homEquiv w.left s''.right).symm.injective
    change (adj.homEquiv w.left s''.right).symm
        (dt.left ≫ f ≫ F.map bs.right) =
      (adj.homEquiv w.left s''.right).symm (dt'.left ≫ g ≫ F.map bs'.right)
    dsimp [s'', bs, bs']
    rw [← Category.assoc, adj.homEquiv_naturality_right_symm,
      adj.homEquiv_naturality_left_symm, ← Category.assoc,
      adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_left_symm]
    exact hf
  · intro h
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q W (a ≫ h)
    let s : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ φ.s φ.hs
    refine ⟨H.ιColimitType (s, Opposite.op t₀) ((adj.homEquiv _ _ ) φ.f), ?_⟩
    change u.app t₀ ≫ (MorphismProperty.LeftFraction.mk
      ((adj.homEquiv _ _).symm ((adj.homEquiv _ _) φ.f)) s.hom s.prop).map
      Q (Localization.inverts Q W) = h
    rw [Equiv.symm_apply_apply]
    change u.app t₀ ≫ φ.map Q (Localization.inverts Q W) = h
    rw [← hφ, ← Category.assoc, ha]
    exact Category.id_comp h
  · intro s t f
    rfl

end CategoryTheory
