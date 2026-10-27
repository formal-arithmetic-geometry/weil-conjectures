/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Mathlib.CategoryTheory.Limits.Types.Coequalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Pullback of an étale relation and its quotient presheaf

Source: Stacks Project, Spaces Tag 02WT; Groupoids Tags 02V8, 02V9 and 045Z
(blueprint: lem-trf-etale-pullback-relation-presheaf).

The presheaves are the coequalizers of the two Yoneda maps. Sectionwise surjectivity
and the equality-of-classes characterizations below identify these coequalizers with
quotients by the specified equivalence relations. All schemes and maps are over `S`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem quotient_sections {C : Type*} [Category.{u} C]
    {F G : C ⥤ Type u} (f g : F ⟶ G) (X : C)
    (hrel : Equivalence (fun a b : G.obj X ↦
      ∃ r : F.obj X, f.app X r = a ∧ g.app X r = b)) :
    Function.Surjective ((coequalizer.π f g).app X) ∧
      ∀ a b : G.obj X,
        (coequalizer.π f g).app X a = (coequalizer.π f g).app X b ↔
          ∃ r : F.obj X, f.app X r = a ∧ g.app X r = b := by
  let E := (evaluation C (Type u)).obj X
  let e := (PreservesCoequalizer.iso E f g).symm ≪≫
    Types.coequalizerIso (f.app X) (g.app X)
  have he (a : G.obj X) :
      e.hom ((coequalizer.π f g).app X a) = Function.Coequalizer.mk _ _ a := by
    have h := ConcreteCategory.congr_hom (map_π_preserves_coequalizer_inv E f g) a
    change (PreservesCoequalizer.iso E f g).inv
      ((coequalizer.π f g).app X a) = _ at h
    change (Types.coequalizerIso (f.app X) (g.app X)).hom
      ((PreservesCoequalizer.iso E f g).inv ((coequalizer.π f g).app X a)) = _
    rw [h]
    exact Types.coequalizerIso_π_comp_hom_apply _ _ a
  refine ⟨?_, ?_⟩
  · exact (epi_iff_surjective _).mp
      (inferInstanceAs (Epi (E.map (coequalizer.π f g))))
  · intro a b
    rw [← e.toEquiv.injective.eq_iff]
    change e.hom ((coequalizer.π f g).app X a) =
      e.hom ((coequalizer.π f g).app X b) ↔ _
    rw [he, he]
    constructor
    · intro h
      apply hrel.eqvGen_iff.mp
      refine Relation.EqvGen.mono ?_ _ _ (Quot.eqvGen_exact h)
      rintro _ _ ⟨r⟩
      exact ⟨r, rfl, rfl⟩
    · rintro ⟨r, rfl, rfl⟩
      exact Function.Coequalizer.condition _ _ r

private theorem over_etale_fst {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Etale g.left] :
    Etale (pullback.fst f g).left := by
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback f g).flip.map (Over.forget S))
    (inferInstance : Etale g.left)

private theorem over_etale_snd {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Etale f.left] :
    Etale (pullback.snd f g).left := by
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback f g).map (Over.forget S))
    (inferInstance : Etale f.left)

/-- The iterated pullback represents triples with the given endpoints, is an étale
monomorphic equivalence relation, and induces an injective map of quotient presheaves.
The existentially named projections are fixed by the first three equalities. Thus they
are the canonical projections, not additional choices or hypotheses.

Source: Stacks Project, Spaces Tag 02WT; Groupoids Tags 02V8, 02V9 and the presheaf
calculation in Tag 045Z (blueprint: lem-trf-etale-pullback-relation-presheaf).

Proof:
1. The two pullback universal properties (def-pc-fibre-product) identify a map to
   the iterated pullback with a triple (a,r,b) satisfying a g = r s and r t = b g.
   Precomposition acts on all three coordinates. Monicity of (s,t) makes the middle
   coordinate unique once the endpoints are fixed.
2. Such a triple exists exactly when g a and g b are related. The equivalence axioms
   therefore pull back to U'. Equal endpoints give equal middle coordinates by
   step 1, and pullback extensionality proves monicity of the restricted relation.
3. The first projection is a composite of base changes of g and s. For the second,
   reassociate the pullbacks through U' ×_{g,U,t} R, obtaining a composite of base
   changes of g and t. Clause 1 of lem-weil-pbc-etale-base-change-finite-limits and
   clause 2 of lem-weil-pbc-etale-composition-cancellation prove both are étale.
   These are Mathlib's Etale base-change and composition instances.
4. A witness r remains a witness after precomposition. Hence precomposition defines
   restrictions on the quotient sets and the quotient projections are natural.
   Every class has a representative, even for an empty set of sections. The
   pointwise coequalizer is exactly this quotient because the relation is already
   an equivalence relation; equality of classes is exactly existence of a witness.
5. Send [a] to [a g]. Step 2 proves well-definedness and also injectivity: equality
   of images supplies a middle arrow r, hence a restricted-relation witness.
   Precomposition commutes with postcomposition by g, giving naturality. On each
   representative both sides of v q' = q h_g have value [a g]. -/
theorem etale_pullback_relation_presheaf {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : U' ⟶ U) [Etale s.left] [Etale t.left] [Etale g.left] :
    ∃ (s' t' : pullback (pullback.snd g s ≫ t) g ⟶ U')
      (r' : pullback (pullback.snd g s ≫ t) g ⟶ R),
      s' = pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s ∧
      t' = pullback.snd (pullback.snd g s ≫ t) g ∧
      r' = pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.snd g s ∧
      (∀ (T : Over S) (a : T ⟶ U') (r : T ⟶ R) (b : T ⟶ U'),
        (r ≫ s = a ≫ g ∧ r ≫ t = b ≫ g) ↔
          ∃! z : T ⟶ pullback (pullback.snd g s ≫ t) g,
            z ≫ s' = a ∧ z ≫ r' = r ∧ z ≫ t' = b) ∧
      (∀ (T : Over S) (a b : T ⟶ U') (r₁ r₂ : T ⟶ R),
        r₁ ≫ s = a ≫ g → r₁ ≫ t = b ≫ g →
        r₂ ≫ s = a ≫ g → r₂ ≫ t = b ≫ g → r₁ = r₂) ∧
      Mono (prod.lift s' t') ∧
      (∀ (T : Over S) (a b : T ⟶ U'),
        (∃ z : T ⟶ pullback (pullback.snd g s ≫ t) g,
          z ≫ s' = a ∧ z ≫ t' = b) ↔
        ∃ r : T ⟶ R, r ≫ s = a ≫ g ∧ r ≫ t = b ≫ g) ∧
      (∀ T : Over S, Equivalence (fun a b : T ⟶ U' ↦
        ∃ z : T ⟶ pullback (pullback.snd g s ≫ t) g,
          z ≫ s' = a ∧ z ≫ t' = b)) ∧
      Etale s'.left ∧ Etale t'.left ∧
      (∀ T : Over S,
        Function.Surjective ((coequalizer.π (yoneda.map s) (yoneda.map t)).app (op T))) ∧
      (∀ T : Over S,
        Function.Surjective ((coequalizer.π (yoneda.map s') (yoneda.map t')).app (op T))) ∧
      (∀ (T : Over S) (a b : T ⟶ U),
        (coequalizer.π (yoneda.map s) (yoneda.map t)).app (op T) a =
          (coequalizer.π (yoneda.map s) (yoneda.map t)).app (op T) b ↔
        ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) ∧
      (∀ (T : Over S) (a b : T ⟶ U'),
        (coequalizer.π (yoneda.map s') (yoneda.map t')).app (op T) a =
          (coequalizer.π (yoneda.map s') (yoneda.map t')).app (op T) b ↔
        ∃ z : T ⟶ pullback (pullback.snd g s ≫ t) g,
          z ≫ s' = a ∧ z ≫ t' = b) ∧
      ∃ v : coequalizer (yoneda.map s') (yoneda.map t') ⟶
          coequalizer (yoneda.map s) (yoneda.map t),
        (∀ (T : Over S) (a : T ⟶ U'),
          v.app (op T) ((coequalizer.π (yoneda.map s') (yoneda.map t')).app (op T) a) =
            (coequalizer.π (yoneda.map s) (yoneda.map t)).app (op T) (a ≫ g)) ∧
        (∀ T : Over S, Function.Injective (v.app (op T))) ∧
        coequalizer.π (yoneda.map s') (yoneda.map t') ≫ v =
          yoneda.map g ≫ coequalizer.π (yoneda.map s) (yoneda.map t) := by
  let p := pullback.fst (pullback.snd g s ≫ t) g
  let s' := p ≫ pullback.fst g s
  let t' := pullback.snd (pullback.snd g s ≫ t) g
  let r' := p ≫ pullback.snd g s
  have hs : r' ≫ s = s' ≫ g := by
    dsimp [r', s']
    simp only [Category.assoc, pullback.condition]
  have ht : r' ≫ t = t' ≫ g := by
    exact pullback.condition (f := pullback.snd g s ≫ t) (g := g)
  have hext {T : Over S} (z w : T ⟶ pullback (pullback.snd g s ≫ t) g)
      (ha : z ≫ s' = w ≫ s') (hr : z ≫ r' = w ≫ r')
      (hb : z ≫ t' = w ≫ t') : z = w := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa only [Category.assoc] using ha
      · simpa only [Category.assoc] using hr
    · exact hb
  have htriple (T : Over S) (a : T ⟶ U') (r : T ⟶ R) (b : T ⟶ U') :
      (r ≫ s = a ≫ g ∧ r ≫ t = b ≫ g) ↔
        ∃! z : T ⟶ pullback (pullback.snd g s ≫ t) g,
          z ≫ s' = a ∧ z ≫ r' = r ∧ z ≫ t' = b := by
    constructor
    · rintro ⟨hr, hb⟩
      let z : T ⟶ pullback (pullback.snd g s ≫ t) g :=
        pullback.lift (pullback.lift a r hr.symm) b (by simpa using hb)
      have za : z ≫ s' = a := by simp [z, s', p]
      have zr : z ≫ r' = r := by simp [z, r', p]
      have zb : z ≫ t' = b := by simp [z, t']
      refine ⟨z, ⟨za, zr, zb⟩, ?_⟩
      rintro w ⟨wa, wr, wb⟩
      exact hext w z (wa.trans za.symm) (wr.trans zr.symm) (wb.trans zb.symm)
    · rintro ⟨z, ⟨ha, hr, hb⟩, _⟩
      constructor
      · rw [← hr, Category.assoc, hs, ← Category.assoc, ha]
      · rw [← hr, Category.assoc, ht, ← Category.assoc, hb]
  have huniq (T : Over S) (a b : T ⟶ U') (r₁ r₂ : T ⟶ R)
      (h₁ : r₁ ≫ s = a ≫ g) (h₂ : r₁ ≫ t = b ≫ g)
      (h₃ : r₂ ≫ s = a ≫ g) (h₄ : r₂ ≫ t = b ≫ g) : r₁ = r₂ := by
    apply (cancel_mono (prod.lift s t)).mp
    apply prod.hom_ext <;> simp [h₁, h₂, h₃, h₄]
  have hm : Mono (prod.lift s' t') := by
    constructor
    intro T z w h
    have ha : z ≫ s' = w ≫ s' := by
      simpa using congrArg (fun k ↦ k ≫ prod.fst) h
    have hb : z ≫ t' = w ≫ t' := by
      simpa using congrArg (fun k ↦ k ≫ prod.snd) h
    apply hext z w ha ?_ hb
    apply huniq T (z ≫ s') (z ≫ t')
    · simp only [Category.assoc, hs]
    · simp only [Category.assoc, ht]
    · rw [Category.assoc, hs, ← Category.assoc, ha]
    · rw [Category.assoc, ht, ← Category.assoc, hb]
  have hiff (T : Over S) (a b : T ⟶ U') :
      (∃ z : T ⟶ pullback (pullback.snd g s ≫ t) g,
        z ≫ s' = a ∧ z ≫ t' = b) ↔
      ∃ r : T ⟶ R, r ≫ s = a ≫ g ∧ r ≫ t = b ≫ g := by
    constructor
    · rintro ⟨z, ha, hb⟩
      exact ⟨z ≫ r', by rw [Category.assoc, hs, ← Category.assoc, ha],
        by rw [Category.assoc, ht, ← Category.assoc, hb]⟩
    · rintro ⟨r, hr⟩
      obtain ⟨z, hz, _⟩ := (htriple T a r b).mp hr
      exact ⟨z, hz.1, hz.2.2⟩
  have hrel' (T : Over S) : Equivalence (fun a b : T ⟶ U' ↦
      ∃ z : T ⟶ pullback (pullback.snd g s ≫ t) g,
        z ≫ s' = a ∧ z ≫ t' = b) := by
    refine ⟨fun a ↦ (hiff T a a).mpr ((hrel T).refl _), ?_, ?_⟩
    · intro a b h
      exact (hiff T b a).mpr ((hrel T).symm ((hiff T a b).mp h))
    · intro a b c hab hbc
      exact (hiff T a c).mpr ((hrel T).trans
        ((hiff T a b).mp hab) ((hiff T b c).mp hbc))
  have hsf : Etale (pullback.fst g s).left := over_etale_fst g s
  have hsg : Etale (pullback.snd g s).left := over_etale_snd g s
  have hcomp : Etale (pullback.snd g s ≫ t).left := by
    change Etale ((pullback.snd g s).left ≫ t.left)
    infer_instance
  have hp : Etale p.left := over_etale_fst _ _
  have hs' : Etale s'.left := by
    change Etale (p.left ≫ (pullback.fst g s).left)
    infer_instance
  have ht' : Etale t'.left := over_etale_snd _ _
  have hq := fun T ↦ quotient_sections (yoneda.map s) (yoneda.map t) (op T) (hrel T)
  have hq' := fun T ↦ quotient_sections (yoneda.map s') (yoneda.map t') (op T) (hrel' T)
  refine ⟨s', t', r', rfl, rfl, rfl, htriple, huniq, hm, hiff, hrel', hs', ht',
    fun T ↦ (hq T).1, fun T ↦ (hq' T).1, fun T ↦ (hq T).2, fun T ↦ (hq' T).2, ?_⟩
  let q := coequalizer.π (yoneda.map s) (yoneda.map t)
  let q' := coequalizer.π (yoneda.map s') (yoneda.map t')
  have hw : yoneda.map s' ≫ yoneda.map g ≫ q =
      yoneda.map t' ≫ yoneda.map g ≫ q := by
    rw [← Functor.map_comp_assoc, ← hs, Functor.map_comp_assoc,
      coequalizer.condition, ← Functor.map_comp_assoc, ht, Functor.map_comp_assoc]
  let v := coequalizer.desc (yoneda.map g ≫ q) hw
  have hv : q' ≫ v = yoneda.map g ≫ q := coequalizer.π_desc _ _
  have hvapp (T : Over S) (a : T ⟶ U') :
      v.app (op T) (q'.app (op T) a) = q.app (op T) (a ≫ g) := by
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hv (op T)) a
  refine ⟨v, hvapp, ?_, hv⟩
  intro T x y h
  obtain ⟨a, rfl⟩ := (hq' T).1 x
  obtain ⟨b, rfl⟩ := (hq' T).1 y
  rw [hvapp, hvapp] at h
  exact ((hq' T).2 a b).mpr ((hiff T a b).mpr (((hq T).2 _ _).mp h))

end AlgebraicGeometry.AlgebraicSpace
