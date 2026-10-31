/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import WeilConjectures.CategoryTheory.FilteredTwoColimitModel

/-! # The concrete directed category colimit and comparison

Source: blueprint main-20261015, filtered 2-colimit model
(blueprint: det-def-sfb-filtered-two-colimit-model).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : Type u'} [Category.{v'} D]

namespace FilteredTwoColimit

variable (c : CoherentCategoryCocone (C := C) (D := D))

private theorem normalized_transport {A B E : Type*} [Category A] [Category B]
    [Category E] (F : E ⥤ E) (hF : F = 𝟭 E) (P : A ⥤ E) (Q : B ⥤ E)
    (eP : P ⋙ F ≅ P) (eQ : Q ⋙ F ≅ Q)
    (hP : HEq eP (Iso.refl P)) (hQ : HEq eQ (Iso.refl Q))
    (x : A) (y : B) (g : P.obj x ⟶ Q.obj y) :
    eP.inv.app x ≫ F.map g ≫ eQ.hom.app y = g := by
  subst F
  have hP' := eq_of_heq hP
  have hQ' := eq_of_heq hQ
  rw [hP', hQ']
  simp

/-- The colimit cocone, lifting stage Hom types into the colimit's universe. Source: blueprint
model, Hom colimit (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homCocone (a b : Object c) :
    Limits.Cocone (homDiagram c a b ⋙ uliftFunctor.{w, v}) where
  pt := HomSet c a b
  ι :=
    { app k := TypeCat.ofHom (fun g => homClass c k g.down)
      naturality {_ _} h := ConcreteCategory.hom_ext _ _
        (fun g => homClass_transition c (leOfHom h) g.down) }

/-- Source: blueprint model proof, set-colimit universal property. A compatible family on the
lifted Hom diagram factors by sending [k,g] to its value on ULift.up g. Compatibility respects
the quotient relation; uniqueness follows because every class has a representative. This is
exactly the universal property of the recorded category-colimit dependency.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homCocone_isColimit (a b : Object c) :
    Nonempty (Limits.IsColimit (homCocone c a b)) := by
  refine ⟨{
    desc := fun s ↦ TypeCat.ofHom (Quot.lift
      (fun f ↦ s.ι.app f.1 ⟨f.2⟩) (by
        rintro ⟨k, f⟩ ⟨l, g⟩ ⟨h, e⟩
        dsimp only at h e ⊢
        rw [e]
        exact (ConcreteCategory.congr_hom (s.w h) ⟨f⟩).symm))
    fac := ?_
    uniq := ?_ }⟩
  · intro s k
    ext g
    rfl
  · intro s m hm
    apply ConcreteCategory.hom_ext
    intro x
    induction x using Quot.inductionOn with
    | h f => exact ConcreteCategory.congr_hom (hm f.1) ⟨f.2⟩

variable [IsDirected I (· ≤ ·)] [Nonempty I]

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem homTransition_product {a b d : Object c} {k l : I}
    (ha : a.1 ≤ k) (hb : b.1 ≤ k) (hd : d.1 ≤ k) (h : k ≤ l)
    (f : (c.T ha).obj a.2 ⟶ (c.T hb).obj b.2)
    (g : (c.T hb).obj b.2 ⟶ (c.T hd).obj d.2) :
    homTransition c (k := ⟨k, ha, hd⟩) (l := ⟨l, ha.trans h, hd.trans h⟩) h (f ≫ g) =
      homTransition c (a := a) (b := b) (k := ⟨k, ha, hb⟩)
          (l := ⟨l, ha.trans h, hb.trans h⟩) h f ≫
        homTransition c (a := b) (b := d) (k := ⟨k, hb, hd⟩)
          (l := ⟨l, hb.trans h, hd.trans h⟩) h g := by
  simp [homTransition, Functor.map_comp, Category.assoc]

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem compAt_transition {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d)
    (m n : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) (h : m ≤ n) :
    compAt c f g m hf hg = compAt c f g n (hf.trans h) (hg.trans h) := by
  unfold compAt
  rw [← homClass_transition c
    (k := ⟨m, f.1.2.1.trans hf, g.1.2.2.trans hg⟩)
    (l := ⟨n, f.1.2.1.trans (hf.trans h), g.1.2.2.trans (hg.trans h)⟩) h]
  congr 1
  rw [homTransition_product c _ (f.1.2.2.trans hf), homTransition_comp,
    homTransition_comp]

/-- Source: blueprint model proof, identity laws. At a common stage, the identity class becomes
an identity by normalization and functoriality; apply the stage's left identity law.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem identity_comp {a b : Object c} (f : HomSet c a b) :
    compHom c (identityHom c a) f = f := by
  induction f using Quot.inductionOn with
  | h f =>
    rcases f with ⟨k, f⟩
    change compRepresentative c ⟨⟨a.1, le_refl _, le_refl _⟩, 𝟙 _⟩ ⟨k, f⟩ =
      homClass c k f
    rw [compRepresentative_eq_compAt c _ _ k.1 k.2.1 (le_refl _)]
    dsimp only [compAt]
    rw [homTransition_id]
    simp [homTransition]
    rfl

/-- Source: blueprint model proof, identity laws. Transport to one stage, where the normalized
identity represents the identity and the right identity law applies.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem comp_identity {a b : Object c} (f : HomSet c a b) :
    compHom c f (identityHom c b) = f := by
  induction f using Quot.inductionOn with
  | h f =>
    rcases f with ⟨k, f⟩
    change compRepresentative c ⟨k, f⟩ ⟨⟨b.1, le_refl _, le_refl _⟩, 𝟙 _⟩ =
      homClass c k f
    rw [compRepresentative_eq_compAt c _ _ k.1 (le_refl _) k.2.2]
    dsimp only [compAt]
    rw [homTransition_id]
    simp [homTransition]
    rfl

private theorem compHom_same {a b d : Object c} (m : I)
    (ha : a.1 ≤ m) (hb : b.1 ≤ m) (hd : d.1 ≤ m)
    (f : (c.T ha).obj a.2 ⟶ (c.T hb).obj b.2)
    (g : (c.T hb).obj b.2 ⟶ (c.T hd).obj d.2) :
    compHom c (homClass c ⟨m, ha, hb⟩ f) (homClass c ⟨m, hb, hd⟩ g) =
      homClass c ⟨m, ha, hd⟩ (f ≫ g) := by
  change compRepresentative c ⟨⟨m, ha, hb⟩, f⟩ ⟨⟨m, hb, hd⟩, g⟩ = _
  rw [compRepresentative_eq_compAt c _ _ m (le_refl _) (le_refl _)]
  simp only [compAt, homTransition_id]

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
private theorem mapHomRepresentative_transition {a b : Object c}
    {k l : CommonStage a.1 b.1} (h : k ≤ l) (f : HomAt c a b k) :
    mapHomRepresentative c ⟨l, homTransition c h f⟩ =
      mapHomRepresentative c ⟨k, f⟩ := by
  have ha : (c.iso (k.2.1.trans h)).inv.app a.2 =
      (c.iso k.2.1).inv.app a.2 ≫ (c.iso h).inv.app ((c.T k.2.1).obj a.2) ≫
        (c.Φ l.1).map ((c.tau k.2.1 h).hom.app a.2) := by
    have he : (c.iso (k.2.1.trans h)).app a.2 =
        (c.Φ l.1).mapIso ((c.tau k.2.1 h).app a.2).symm ≪≫
          (c.iso h).app ((c.T k.2.1).obj a.2) ≪≫ (c.iso k.2.1).app a.2 :=
      Iso.ext (c.compatibility k.2.1 h a.2)
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
      Iso.app_hom, Category.assoc] using congrArg Iso.inv he
  dsimp only [mapHomRepresentative]
  rw [ha, c.compatibility k.2.2 h b.2]
  simp only [homTransition, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  have hn := (c.iso h).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((c.Φ l.1).map ((c.T h).map f)), hn]
  simp

/-- Source: blueprint model proof, comparison identity. Normalization makes theta_ii identity;
Phi_i preserves identity, giving the stated identity morphism.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem mapHom_identity (a : Object c) : mapHom c (identityHom c a) = 𝟙 _ := by
  change mapHomRepresentative c ⟨⟨a.1, le_refl _, le_refl _⟩, 𝟙 _⟩ = _
  simp [mapHomRepresentative]

end FilteredTwoColimit
end CategoryTheory
