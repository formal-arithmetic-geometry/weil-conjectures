/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentToposRepair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Quasi-compact restriction of a kernel pair

Source: literature/stacks-project/sites.tex, Tag 00W2, lemma-limit-sheaf;
the kernel-pair calculation in step 6 of lem-trf-coherent-epimorphic-quotient
(blueprint: lem-trf-kernel-pair-restriction-quasicompact).
-/

@[expose] public section

set_option autoImplicit false

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def restrictionHom
    {E : Type u} [Category.{v} E] [HasFiniteLimits E]
    {P A K L : E} (p : P ⟶ A) (k : K ⟶ P) (l : L ⟶ P) :
    pullback (k ≫ p) (l ≫ p) ⟶
      pullback (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l :=
  pullback.lift
    (pullback.lift (pullback.fst (k ≫ p) (l ≫ p))
      (pullback.lift (pullback.fst (k ≫ p) (l ≫ p) ≫ k)
        (pullback.snd (k ≫ p) (l ≫ p) ≫ l)
        (by simpa only [Category.assoc] using
          (pullback.condition (f := k ≫ p) (g := l ≫ p))))
      (by simp))
    (pullback.snd (k ≫ p) (l ≫ p)) (by simp)

private noncomputable def restrictionInv
    {E : Type u} [Category.{v} E] [HasFiniteLimits E]
    {P A K L : E} (p : P ⟶ A) (k : K ⟶ P) (l : L ⟶ P) :
    pullback (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ⟶
      pullback (k ≫ p) (l ≫ p) :=
  pullback.lift
    (pullback.fst (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ≫
      pullback.fst k (pullback.fst p p))
    (pullback.snd (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l)
    (by
      simp only [Category.assoc, pullback.condition_assoc]
      rw [← Category.assoc _ l p, ← pullback.condition]
      simp only [Category.assoc, pullback.condition]
      simpa only [Category.assoc] using
        (pullback.condition_assoc
          (f := pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) (g := l) p))

private noncomputable def restrictionIso
    {E : Type u} [Category.{v} E] [HasFiniteLimits E]
    {P A K L : E} (p : P ⟶ A) (k : K ⟶ P) (l : L ⟶ P) :
    pullback (k ≫ p) (l ≫ p) ≅
      pullback (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l where
  hom := restrictionHom p k l
  inv := restrictionInv p k l
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [restrictionHom, restrictionInv]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [restrictionHom, restrictionInv]
      · apply pullback.hom_ext
        · simp [restrictionHom, restrictionInv, pullback.condition]
        · simp [restrictionHom, restrictionInv, ← pullback.condition]
    · simp [restrictionHom, restrictionInv]

/-- Restricting a quasi-compact kernel pair over a quasi-separated object gives
quasi-compact fibre products and a canonical natural isomorphism.
Source: Stacks, Tag 00W2, lemma-limit-sheaf, and the kernel-pair calculation in
step 6 of lem-trf-coherent-epimorphic-quotient
(blueprint: lem-trf-kernel-pair-restriction-quasicompact).

The family `e` goes from K ×_A L to (K ×_P (P ×_A P)) ×_P L. Its first two
identities preserve the K and L projections. The next two specify its R coordinates
as k(x) and l(y). The following two identities say that the inverse forgets R.
In any small-site presentation, limits are sectionwise by Tag 00W2, so these
identities give precisely (x,y) ↦ (x,(k(x),l(y)),y) and its inverse.
The last identity is naturality for maps over P, using the standard pullback maps.

Proof:
1. By def-trf-coherent-topos, apply quasi-separatedness of P to the quasi-compact
   objects K and R to see that T = K ×_P R is quasi-compact.
2. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise (Stacks Tag 00W2), compute
   pullbacks on sections of a small-site presentation. A pair (x,y) on the left
   satisfies p(k(x)) = p(l(y)). Send it to (x,(k(x),l(y)),y) on the right.
   Conversely forget the R coordinate; its two entries must be k(x) and l(y).
   The resulting maps are inverse, commute with restrictions, and hence define
   inverse sheaf morphisms. Equivalently, use the universal property of pullbacks.
3. These maps preserve the K and L projections and have the asserted R coordinates.
   For maps a : K' → K and b : L' → L over P, both routes in the naturality square
   send (x',y') to (a(x'),(k(a(x')),l(b(y'))),b(y')). This proves naturality.
4. Apply quasi-separatedness of P again, now to T and L, to see that the right
   side is quasi-compact. Transport quasi-compactness across e: compose an
   epimorphic family with e, select a finite epimorphic subfamily on the right,
   and compose with e.inv. This yields quasi-compactness of K ×_A L.
No epimorphism of p, quasi-compactness of P, or coherence of the topos is used.
-/
theorem kernelPair_restriction_quasiCompact
    {E : Type u} [Category.{v} E] [HasCoproducts.{w} E] [HasFiniteLimits E]
    (hE : IsGrothendieckTopos.{w} E) {P A : E} (p : P ⟶ A)
    (hP : IsQuasiSeparatedObject.{w} P)
    (hR : IsQuasiCompactObject.{w} (pullback p p)) :
    ∃ e : ∀ (K L : E) (k : K ⟶ P) (l : L ⟶ P),
        IsQuasiCompactObject.{w} K → IsQuasiCompactObject.{w} L →
          (pullback (k ≫ p) (l ≫ p) ≅
            pullback (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l),
      ∀ (K L : E) (k : K ⟶ P) (l : L ⟶ P)
        (hK : IsQuasiCompactObject.{w} K) (hL : IsQuasiCompactObject.{w} L),
        (e K L k l hK hL).hom ≫
            pullback.fst (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ≫
              pullback.fst k (pullback.fst p p) = pullback.fst (k ≫ p) (l ≫ p) ∧
        (e K L k l hK hL).hom ≫
            pullback.snd (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l =
          pullback.snd (k ≫ p) (l ≫ p) ∧
        (e K L k l hK hL).hom ≫
            pullback.fst (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ≫
              pullback.snd k (pullback.fst p p) ≫ pullback.fst p p =
          pullback.fst (k ≫ p) (l ≫ p) ≫ k ∧
        (e K L k l hK hL).hom ≫
            pullback.fst (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ≫
              pullback.snd k (pullback.fst p p) ≫ pullback.snd p p =
          pullback.snd (k ≫ p) (l ≫ p) ≫ l ∧
        (e K L k l hK hL).inv ≫ pullback.fst (k ≫ p) (l ≫ p) =
          pullback.fst (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ≫
            pullback.fst k (pullback.fst p p) ∧
        (e K L k l hK hL).inv ≫ pullback.snd (k ≫ p) (l ≫ p) =
          pullback.snd (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l ∧
        IsQuasiCompactObject.{w} (pullback k (pullback.fst p p)) ∧
        IsQuasiCompactObject.{w} (pullback (k ≫ p) (l ≫ p)) ∧
        ∀ (K' L' : E) (k' : K' ⟶ P) (l' : L' ⟶ P)
          (hK' : IsQuasiCompactObject.{w} K') (hL' : IsQuasiCompactObject.{w} L')
          (a : K' ⟶ K) (b : L' ⟶ L) (ha : a ≫ k = k') (hb : b ≫ l = l'),
          pullback.map (k' ≫ p) (l' ≫ p) (k ≫ p) (l ≫ p) a b (𝟙 A)
              (by simp [← ha]) (by simp [← hb]) ≫ (e K L k l hK hL).hom =
            (e K' L' k' l' hK' hL').hom ≫
              pullback.map
                (pullback.snd k' (pullback.fst p p) ≫ pullback.snd p p) l'
                (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l
                (pullback.map k' (pullback.fst p p) k (pullback.fst p p)
                  a (𝟙 (pullback p p)) (𝟙 P) (by simp [← ha]) (by simp))
                b (𝟙 P) (by simp) (by simp [← hb]) := by
  have _ := hE
  refine ⟨fun K L k l _ _ ↦ restrictionIso p k l, ?_⟩
  intro K L k l hK hL
  have hT : IsQuasiCompactObject.{w} (pullback k (pullback.fst p p)) :=
    hP K (pullback p p) k (pullback.fst p p) hK hR _ _ _
      (IsPullback.of_hasPullback _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hT, ?_, ?_⟩
  · simp [restrictionIso, restrictionHom]
  · simp [restrictionIso, restrictionHom]
  · simp [restrictionIso, restrictionHom]
  · simp [restrictionIso, restrictionHom]
  · simp [restrictionIso, restrictionInv]
  · simp [restrictionIso, restrictionInv]
  · apply hP (pullback k (pullback.fst p p)) L
      (pullback.snd k (pullback.fst p p) ≫ pullback.snd p p) l hT hL
      (pullback (k ≫ p) (l ≫ p))
      ((restrictionIso p k l).hom ≫ pullback.fst _ _)
      ((restrictionIso p k l).hom ≫ pullback.snd _ _)
    exact IsPullback.of_iso_pullback
      ⟨by simp only [Category.assoc, pullback.condition]⟩ (restrictionIso p k l) rfl rfl
  · intro K' L' k' l' hK' hL' a b ha hb
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [restrictionIso, restrictionHom]
      · apply pullback.hom_ext <;>
          simp [restrictionIso, restrictionHom, Category.assoc, ha, hb]
    · simp [restrictionIso, restrictionHom]

end CategoryTheory
