/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.CategoryTheory.ExtOneExtensionClassification
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Finite-stage presentation of an extension with fixed quotient

Source: latest blueprint, sec-six-functors-basics/sk-prop-ind-heart,
sk-prop-ind-heart-extensions.proof.md, Pullback to C_alpha and Colimit over beta-prime;
Stacks Project, Homology, Tag 010I
(blueprint: lem-sfb-ind-extension-finite-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

/-- Surjectivity of the canonical Ext-one comparison descends a fixed-quotient extension
and presents its middle object by the canonical pushouts over a filtered undercategory.
Source: latest blueprint, sk-prop-ind-heart-extensions.proof.md, Pullback to C_alpha and
Colimit over beta-prime; Stacks Project, Homology, Tag 010I
(blueprint: lem-sfb-ind-extension-finite-quotient).

`extFunctorObj C 1` is the covariant derived Ext functor; its action on a map `n` is
pushforward by `n`. The Grothendieck instance supplies its `v`-small Ext groups.
`Under.post N` sends `(j,a)` to `N(a)`. Composing with `Under.pushout f` and
`Under.forget B` gives the diagram with objects `pushout (N.map a) f` and transitions
induced by `N(h)` and the identity of `B`. The two equations on `tau.app j` characterize
exactly the specified cocone after the endpoint-fixed isomorphism to `T`.

Proof plan:
1. Take the connecting class of the given sequence. Surjectivity supplies an element of
   the Ext colimit mapping to it. The forgetful functor from abelian groups preserves
   filtered colimits, so Concrete.isColimit_exists_rep gives a representative at some i.
2. Ext-one extension classification represents this class by a short exact sequence with
   endpoints N_i and C. Push it out along n_i. Naturality of the short-exact-sequence
   triangle identifies its class with that of the given sequence. Injectivity of the
   classification gives an isomorphism with identity endpoint maps.
3. The undercategory of i is small and filtered, and its projection to I is final.
   The restricted N diagram therefore still has the given colimit. Its object (i,id)
   is initial, since its unique map to (j,a) is a.
4. Push out the descended sequence along every N(a). Each resulting sequence is short
   exact, so its middle object satisfies P by extension closure and the assumption P(C).
   Pushout uniqueness gives the transitions induced by N(h) and the identity of B,
   and proves their identity and composition laws.
5. The pushout maps to L form a cocone. To factor any other cocone, restrict it to N_j
   and to B. The first restrictions factor uniquely through N_infinity. The second
   restrictions agree by the arrows from (i,id), and give a single map from B. At
   (i,id) these two maps agree on N_i, so they factor uniquely through L. Checking on
   both pushout inclusions proves the required factorization and its uniqueness.
6. Compose this colimit cocone with the isomorphism L to T. All its stages satisfy P,
   so this is a v-small filtered presentation, precisely ObjectProperty.ind P T.
-/
theorem ind_extension_finite_quotient
    {M : Type u} [Category.{w} M] [Abelian M] [IsGrothendieckAbelian.{v} M]
    (P : ObjectProperty M) [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ M) (hN : ∀ i : I, P (N.obj i))
    (c : Cocone N) (hc : IsColimit c) (C : M) (hC : P C)
    (hsurj : Function.Surjective
      (colimit.desc (N ⋙ Abelian.extFunctorObj C 1)
        ((Abelian.extFunctorObj C 1).mapCocone c)))
    (T : M) (a : c.pt ⟶ T) (b : T ⟶ C) (z : a ≫ b = 0)
    (hT : (ShortComplex.mk a b z).ShortExact) :
    ∃ (i : I) (B : M) (f : N.obj i ⟶ B) (q : B ⟶ C) (hz : f ≫ q = 0),
      (ShortComplex.mk f q hz).ShortExact ∧
      ∃ (p : pushout (c.ι.app i) f ⟶ C)
        (hzL : pushout.inl (c.ι.app i) f ≫ p = 0),
        (ShortComplex.mk (pushout.inl (c.ι.app i) f) p hzL).ShortExact ∧
        pushout.inr (c.ι.app i) f ≫ p = q ∧
        ∃ e : pushout (c.ι.app i) f ≅ T,
          pushout.inl (c.ι.app i) f ≫ e.hom = a ∧
          e.hom ≫ b = p ∧
          IsFiltered (Under i) ∧
          (∀ j : Under i, P (pushout (N.map j.hom) f)) ∧
          ∃ tau : (Under.post (X := i) N ⋙ Under.pushout f ⋙ Under.forget B) ⟶
              (Functor.const (Under i)).obj T,
            (∀ j : Under i,
              pushout.inl (N.map j.hom) f ≫ tau.app j = c.ι.app j.right ≫ a ∧
              pushout.inr (N.map j.hom) f ≫ tau.app j =
                pushout.inr (c.ι.app i) f ≫ e.hom) ∧
            Nonempty (IsColimit (Cocone.mk T tau)) ∧ ObjectProperty.ind.{v} P T := by
  classical
  let := HasDerivedCategory.standard M
  obtain ⟨x, hx⟩ := hsurj hT.extClass
  obtain ⟨i, η, hη⟩ := Concrete.colimit_exists_rep (N ⋙ Abelian.extFunctorObj C 1) x
  have hη' : η.comp (Abelian.Ext.mk₀ (c.ι.app i)) (add_zero 1) = hT.extClass := by
    have he := ConcreteCategory.congr_hom
      (colimit.ι_desc ((Abelian.extFunctorObj C 1).mapCocone c) i) η
    calc
      _ = (colimit.desc _ ((Abelian.extFunctorObj C 1).mapCocone c))
          ((colimit.ι (N ⋙ Abelian.extFunctorObj C 1) i) η) := he.symm
      _ = _ := by rw [hη]; exact hx
  obtain ⟨B, f, q, hz, hB, hξ⟩ :=
    (ext_one_extension_classification.{v, v, max u w, max u w, w, w, u, u}
      (N.obj i) C).1 η
  let S := ShortComplex.mk f q hz
  obtain ⟨_, p, hzL, hp, _, hL, m, hm₁, hm₂, hm₃⟩ :=
    pushout_short_exact_sequence S hB (c.ι.app i)
  have heq : hL.extClass = hT.extClass := by
    have hn := hB.extClass_naturality hL m
    rw [hm₁, hm₃, hξ, Abelian.Ext.mk₀_id_comp] at hn
    exact hn.symm.trans hη'
  obtain ⟨e, he₁, he₂⟩ :=
    ((ext_one_extension_classification.{v, v, max u w, max u w, w, w, u, u}
      c.pt C).2.1 _ _ _ _ _ hL _ _ _ hT).mp heq
  have hstages : ∀ j : Under i, P (pushout (N.map j.hom) f) := by
    intro j
    obtain ⟨_, p', hz', _, _, hE, _⟩ :=
      pushout_short_exact_sequence S hB (N.map j.hom)
    exact P.prop_X₂_of_shortExact hE (hN j.right) hC
  have : IsConnected (Under i) := IsFiltered.isConnected _
  let G := Under.pushout f ⋙ Under.forget B
  let F := Under.post (X := i) N ⋙ G
  let d := G.mapCocone (c.underPost i)
  have : PreservesColimitsOfShape (Under i) G := comp_preservesColimitsOfShape _ _
  have hd : IsColimit d := isColimitOfPreserves G (hc.underPost i)
  let dT : Cocone F := d.extend e.hom
  have hdT : IsColimit dT := IsColimit.extendIso _ hd
  refine ⟨i, B, f, q, hz, hB, p, hzL, hL, hp, e, he₁, he₂,
    inferInstance, hstages, dT.ι, ?_, ⟨hdT⟩, ?_⟩
  · intro j
    constructor
    · change pushout.inl _ _ ≫ (pushout.desc _ _ _ ≫ e.hom) = _
      simp only [pushout.inl_desc_assoc]
      change (c.ι.app j.right ≫ pushout.inl (c.ι.app i) f) ≫ e.hom = _
      exact (Category.assoc _ _ _).trans
        (congrArg (fun k ↦ c.ι.app j.right ≫ k) he₁)
    · change pushout.inr _ _ ≫ (pushout.desc _ _ _ ≫ e.hom) = _
      simp only [pushout.inr_desc_assoc]
      rfl
  · exact ⟨Under i, inferInstance, inferInstance, ⟨F, dT.ι, hdT⟩, hstages⟩

end CategoryTheory
