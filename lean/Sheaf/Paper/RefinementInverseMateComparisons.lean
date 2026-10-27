/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.NatIso

/-! # Inverse refinement mates and common-refinement comparisons

Source: Stacks Project, Tags 0F7C, 0F7J and 0ATU; the abstract inverse-compositor
and parallel-arrow cancellation argument
(blueprint: lem-pur-refinement-inverse-mate-comparisons).

The helper data package contains exactly the supplied functors, compositors and mates.
Only restriction to the specified full subcategory is inverted. No comparison on a
non-refinement square, or equality-detecting evaluation functor, is supplied.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

set_option linter.checkUnivs false in
/-- The data supplied in the inverse-refinement-mate assertion. The compositor accepts
an explicitly named composite and its equality, so equal proper maps need no silent casts.
The identity mate is normalized using the supplied proper identity isomorphism.
Source: Stacks 0F7C, 0F7J, abstract hypotheses
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
structure RefinementInverseMateData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The categories assigned to the schemes. -/
  D : Scheme.{u} → Type w
  /-- Category structures, with one fixed morphism universe. -/
  [category (W : Scheme.{u}) : Category.{v} (D W)]
  /-- The supplied proper functors. -/
  R {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] : D W ⥤ D V
  /-- Proper identity normalization. -/
  rId (W : Scheme.{u}) : R (𝟙 W) ≅ 𝟭 (D W)
  /-- The compositor in the direction used in the node. -/
  comp {W V T : Scheme.{u}} (p : W ⟶ V) (q : V ⟶ T) (pq : W ⟶ T)
    [IsProper p] [IsProper q] [IsProper pq] (h : p ≫ q = pq) :
    R pq ≅ R p ⋙ R q
  /-- Associativity of the supplied proper compositors. -/
  assoc {W V T S : Scheme.{u}} (p : W ⟶ V) (q : V ⟶ T) (r : T ⟶ S)
    (pq : W ⟶ T) (qr : V ⟶ S) (pqr : W ⟶ S)
    [IsProper p] [IsProper q] [IsProper r]
    [IsProper pq] [IsProper qr] [IsProper pqr]
    (hpq : p ≫ q = pq) (hqr : q ≫ r = qr)
    (hl : pq ≫ r = pqr) (hr : p ≫ qr = pqr) (M : D W) :
    (comp pq r pqr hl).hom.app M ≫ (R r).map ((comp p q pq hpq).hom.app M) =
      (comp p qr pqr hr).hom.app M ≫ (comp q r qr hqr).hom.app ((R p).obj M)
  /-- The left proper unit law. -/
  left {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] (M : D W) :
    (comp (𝟙 W) p p (Category.id_comp p)).hom.app M ≫
      (R p).map ((rId W).hom.app M) = 𝟙 ((R p).obj M)
  /-- The right proper unit law. -/
  right {W V : Scheme.{u}} (p : W ⟶ V) [IsProper p] (M : D W) :
    (comp p (𝟙 V) p (Category.comp_id p)).hom.app M ≫
      (rId V).hom.app ((R p).obj M) = 𝟙 ((R p).obj M)
  /-- The functor assigned to the open part of each compactification. -/
  J (c : Compactification f) : D X ⥤ D c.Z
  /-- Refinement mates, not assumed invertible on the ambient category. -/
  gamma {c d : Compactification f} (r : c ⟶ d) : J d ⟶ J c ⋙ R r.hom
  /-- Identity normalization, with the proper unitor inserted. -/
  gammaId (c : Compactification f) (M : D X) :
    (gamma (𝟙 c)).app M ≫ (rId c.Z).hom.app ((J c).obj M) = 𝟙 ((J c).obj M)
  /-- Vertical pasting for refinement mates. -/
  gammaComp {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e) (M : D X) :
    (gamma (r ≫ s)).app M ≫
        (comp r.hom s.hom (r ≫ s).hom rfl).hom.app ((J c).obj M) =
      (gamma s).app M ≫ (R s.hom).map ((gamma r).app M)

namespace RefinementInverseMateData

attribute [instance] category

variable {X Y : Scheme.{u}} {f : X ⟶ Y}
    (T : RefinementInverseMateData.{u, v, w} f) (E : ObjectProperty (T.D X))

/-- The compactified composite restricted to precisely the given full subcategory.
Source: Stacks 0F7J, the definition of the compactified functor
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
def restricted (c : Compactification f) : E.FullSubcategory ⥤ T.D Y :=
  (E.ι ⋙ T.J c) ⋙ T.R c.g

variable (hE : ∀ {c d : Compactification f} (r : c ⟶ d) (M : E.FullSubcategory),
    IsIso ((T.gamma r).app M.obj))

/-- The restricted mate with its uniquely determined inverse. Its data is the supplied
natural transformation, inverted by Mathlib's pointwise-isomorphism construction.
Source: Stacks 0F7C, inverse naturality argument
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
noncomputable def restrictedGamma {c d : Compactification f} (r : c ⟶ d) :
    E.ι ⋙ T.J d ≅ (E.ι ⋙ T.J c) ⋙ T.R r.hom :=
  letI : ∀ M : E.FullSubcategory,
      IsIso ((Functor.whiskerLeft E.ι (T.gamma r)).app M) := hE r
  letI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft E.ι (T.gamma r))
  asIso (Functor.whiskerLeft E.ι (T.gamma r)) ≪≫ (Functor.associator _ _ _).symm

/-- The specified inverse refinement comparison: first the proper compositor, then
proper pushforward of the inverse mate. The associators only expose the whiskerings.
Source: Stacks 0F7C and 0F7J, inverse-compositor formula
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
noncomputable def theta {c d : Compactification f} (r : c ⟶ d) :
    T.restricted E c ≅ T.restricted E d :=
  Functor.isoWhiskerLeft (E.ι ⋙ T.J c) (T.comp r.hom d.g c.g r.hom_g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (T.restrictedGamma E hE r).symm (T.R d.g)

/-- Comparison computed on any supplied common refinement; no choice is made.
Source: Stacks 0F7J, independence-of-choices argument
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
noncomputable def compare {c d a : Compactification f} (r : a ⟶ c) (s : a ⟶ d) :
    T.restricted E c ≅ T.restricted E d :=
  (T.theta E hE r).symm ≪≫ T.theta E hE s

/-- The restricted mate has the original components on the full subcategory.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma gamma_hom_app {c d : Compactification f} (r : c ⟶ d)
    (M : E.FullSubcategory) :
    (T.restrictedGamma E hE r).hom.app M = (T.gamma r).app M.obj := by
  simp [restrictedGamma]

/-- The two nontrivial factors of the inverse refinement comparison.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma theta_hom_app {c d : Compactification f} (r : c ⟶ d)
    (M : E.FullSubcategory) :
    (T.theta E hE r).hom.app M =
      (T.comp r.hom d.g c.g r.hom_g).hom.app ((T.J c).obj M.obj) ≫
        (T.R d.g).map ((T.restrictedGamma E hE r).inv.app M) := by
  simp [theta]

/-- Invert the supplied vertical-pasting equation by cancellation on the left.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma gamma_inv_comp {c d e : Compactification f} (r : c ⟶ d)
    (s : d ⟶ e) (M : E.FullSubcategory) :
    (T.restrictedGamma E hE (r ≫ s)).inv.app M =
      (T.comp r.hom s.hom (r ≫ s).hom rfl).hom.app ((T.J c).obj M.obj) ≫
        (T.R s.hom).map ((T.restrictedGamma E hE r).inv.app M) ≫
        (T.restrictedGamma E hE s).inv.app M := by
  apply (cancel_epi ((T.restrictedGamma E hE (r ≫ s)).hom.app M)).1
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  rw [gamma_hom_app, T.gammaComp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← gamma_hom_app T E hE r, ← gamma_hom_app T E hE s]
  simp

/-- The proper left unit law and the normalized identity mate give the identity comparison.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma theta_id (c : Compactification f) :
    T.theta E hE (𝟙 c) = Iso.refl (T.restricted E c) := by
  apply Iso.ext
  ext M
  rw [theta_hom_app]
  have h : (T.restrictedGamma E hE (𝟙 c)).inv.app M =
      (T.rId c.Z).hom.app ((T.J c).obj M.obj) := by
    apply (cancel_epi ((T.restrictedGamma E hE (𝟙 c)).hom.app M)).1
    rw [Iso.hom_inv_id_app, gamma_hom_app]
    exact (T.gammaId c M.obj).symm
  rw [h]
  exact T.left c.g ((T.J c).obj M.obj)

/-- Push forward the inverse-pasting formula and apply compositor associativity.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma theta_four {c d e : Compactification f} (r : c ⟶ d)
    (s : d ⟶ e) (M : E.FullSubcategory) :
    (T.theta E hE (r ≫ s)).hom.app M =
      (T.comp r.hom d.g c.g r.hom_g).hom.app ((T.J c).obj M.obj) ≫
        (T.comp s.hom e.g d.g s.hom_g).hom.app
          ((T.R r.hom).obj ((T.J c).obj M.obj)) ≫
        (T.R e.g).map ((T.R s.hom).map ((T.restrictedGamma E hE r).inv.app M)) ≫
        (T.R e.g).map ((T.restrictedGamma E hE s).inv.app M) := by
  rw [theta_hom_app, gamma_inv_comp]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [T.assoc r.hom s.hom e.g (r ≫ s).hom d.g c.g rfl s.hom_g
    (r ≫ s).hom_g r.hom_g]

/-- Naturality of the proper compositor identifies the four-factor expression.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma theta_comp {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e) :
    (T.theta E hE (r ≫ s)).hom = (T.theta E hE r).hom ≫ (T.theta E hE s).hom := by
  ext M
  rw [NatTrans.comp_app, theta_four, theta_hom_app, theta_hom_app]
  have h := (T.comp s.hom e.g d.g s.hom_g).hom.naturality
    ((T.restrictedGamma E hE r).inv.app M)
  dsimp at h
  simp only [Category.assoc]
  rw [← Category.assoc ((T.R d.g).map _), h]
  simp only [Category.assoc]

/-- Functoriality expressed as equality of natural isomorphisms.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma theta_comp_iso {c d e : Compactification f} (r : c ⟶ d) (s : d ⟶ e) :
    T.theta E hE (r ≫ s) = T.theta E hE r ≪≫ T.theta E hE s := by
  apply Iso.ext
  exact theta_comp T E hE r s

/-- Further refinement inserts an isomorphism followed by its inverse.
Source: the abstract inverse-compositor argument for Stacks 0F7C and 0F7J
(blueprint: lem-pur-refinement-inverse-mate-comparisons). -/
private lemma compare_refine {c d a b : Compactification f} (r : a ⟶ c)
    (s : a ⟶ d) (t : b ⟶ a) :
    T.compare E hE (t ≫ r) (t ≫ s) = T.compare E hE r s := by
  simp only [compare, theta_comp_iso, Iso.trans_symm]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- Inverse refinement comparisons are functorial and give coherent comparisons
independent of the common refinement and both arrows.

Source: Stacks 0F7C and 0F7J, with cofilteredness as in 0ATU; the abstract
inverse-compositor argument (blueprint: lem-pur-refinement-inverse-mate-comparisons).

Proof plan:
1. Restrict to E. Naturality of gamma, multiplied by its component inverses, proves
   naturality of the inverse; proper functors carry inverse arrows to inverse arrows.
   The inverse of theta is inverse compositor followed by the non-inverted mate.
   The supplied proper unit law and gammaId give the identity normalization.
2. Write U = gamma_r, V = gamma_s, W = gamma_(r s), C = comp_(s,r).
   Pasting says W C = V R_s(U) in diagrammatic order. Inverting gives
   W⁻¹ = C R_s(U⁻¹) V⁻¹. This only uses inverses at objects of E.
3. Apply R_(p_3) and compositor associativity to this inverse formula. The result
   is the four-factor expression explicitly stated in the second conjunct below.
4. Expand theta_r followed by theta_s. Naturality of comp_(p_3,s) at U⁻¹
   identifies this expansion with the expression of step 3, proving composition.
5. For parallel a,b choose an equalizing refinement e by cofilteredness.
   Functoriality gives theta_e theta_a = theta_e theta_b; cancel theta_e.
6. Further refinement of a span inserts theta_t⁻¹ theta_t, which cancels.
7. For two spans choose a common refinement of their vertices. Their composites
   into each endpoint are parallel, so step 5 and then step 6 prove independence.
8. Refine three compactifications simultaneously. Compute all comparisons on that
   vertex and cancel the middle pair. For C_11 use the identity span. Every equality
   is in the supplied functor category, with no evaluation-detection assumption. -/
theorem refinement_inverse_mate_comparisons
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsCofiltered (Compactification f)] :
    (∀ c : Compactification f, T.theta E hE (𝟙 c) = Iso.refl (T.restricted E c)) ∧
    (∀ (c d e : Compactification f) (r : c ⟶ d) (s : d ⟶ e),
      (T.theta E hE (r ≫ s)).hom = (T.theta E hE r).hom ≫ (T.theta E hE s).hom ∧
      ∀ M : E.FullSubcategory,
        (T.theta E hE (r ≫ s)).hom.app M =
          (T.comp r.hom d.g c.g r.hom_g).hom.app ((T.J c).obj M.obj) ≫
            (T.comp s.hom e.g d.g s.hom_g).hom.app
              ((T.R r.hom).obj ((T.J c).obj M.obj)) ≫
            (T.R e.g).map ((T.R s.hom).map ((T.restrictedGamma E hE r).inv.app M)) ≫
            (T.R e.g).map ((T.restrictedGamma E hE s).inv.app M)) ∧
    (∀ (c d : Compactification f) (a b : c ⟶ d),
      (T.theta E hE a).hom = (T.theta E hE b).hom) ∧
    (∀ (c d a b : Compactification f) (r : a ⟶ c) (s : a ⟶ d)
      (r' : b ⟶ c) (s' : b ⟶ d),
      T.compare E hE r s = T.compare E hE r' s') ∧
    (∀ (c₁ c₂ c₃ a b d : Compactification f)
      (r₁ : a ⟶ c₁) (r₂ : a ⟶ c₂) (s₂ : b ⟶ c₂) (s₃ : b ⟶ c₃)
      (t₁ : d ⟶ c₁) (t₃ : d ⟶ c₃),
      (T.compare E hE r₁ r₂).hom ≫ (T.compare E hE s₂ s₃).hom =
        (T.compare E hE t₁ t₃).hom) ∧
    (∀ (c a : Compactification f) (r s : a ⟶ c),
      T.compare E hE r s = Iso.refl (T.restricted E c)) := by
  have hp : ∀ (c d : Compactification f) (a b : c ⟶ d),
      T.theta E hE a = T.theta E hE b := by
    intro c d a b
    obtain ⟨e, t, ht⟩ := IsCofilteredOrEmpty.cone_maps a b
    apply Iso.ext
    apply (cancel_epi (T.theta E hE t).hom).1
    rw [← theta_comp, ← theta_comp, ht]
  have hc : ∀ (c d a b : Compactification f) (r : a ⟶ c) (s : a ⟶ d)
      (r' : b ⟶ c) (s' : b ⟶ d), T.compare E hE r s = T.compare E hE r' s' := by
    intro c d a b r s r' s'
    obtain ⟨e, t, t', _⟩ := IsCofilteredOrEmpty.cone_objs a b
    rw [← compare_refine T E hE r s t, ← compare_refine T E hE r' s' t']
    unfold compare
    rw [hp _ _ (t ≫ r) (t' ≫ r'), hp _ _ (t ≫ s) (t' ≫ s')]
  refine ⟨theta_id T E hE, ?_, ?_, hc, ?_, ?_⟩
  · intro c d e r s
    exact ⟨theta_comp T E hE r s, theta_four T E hE r s⟩
  · intro c d a b
    exact congrArg Iso.hom (hp c d a b)
  · intro c₁ c₂ c₃ a b d r₁ r₂ s₂ s₃ t₁ t₃
    obtain ⟨e, u, v, _⟩ := IsCofilteredOrEmpty.cone_objs a b
    rw [hc _ _ _ _ r₁ r₂ (u ≫ r₁) (u ≫ r₂),
      hc _ _ _ _ s₂ s₃ (u ≫ r₂) (v ≫ s₃),
      hc _ _ _ _ t₁ t₃ (u ≫ r₁) (v ≫ s₃)]
    simp [compare, Category.assoc]
  · intro c a r s
    unfold compare
    rw [hp _ _ r s]
    exact Iso.symm_self_id _

end RefinementInverseMateData

end AlgebraicGeometry
