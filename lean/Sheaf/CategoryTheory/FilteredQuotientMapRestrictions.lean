/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Restrictions of filtered maps to cycles and boundary quotients

Source: Stacks Project, Homology, Tag 012K, Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-map-restrictions).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem restriction {D : Type u} [Category.{v} D] [Abelian D]
    {A B : D} (f : A ⟶ B) (S : Subobject A)
    (T : Subobject B) (h : S ≤ (Subobject.pullback f).obj T) :
    ∃ k : (S : D) ⟶ (T : D), k ≫ T.arrow = S.arrow ≫ f := by
  have hf := (Subobject.factors_pullback_obj_iff f T S.arrow).mp
    ((Subobject.le_iff_factors_arrow _ _).mp h)
  exact ⟨T.factorThru _ hf, T.factorThru_arrow _ hf⟩

private theorem preserves_pullback {D : Type u} [Category.{v} D] [Abelian D]
    {A B X Y : D} (a : A ⟶ B) (b : X ⟶ Y)
    (f : A ⟶ X) (g : B ⟶ Y) (w : f ≫ b = a ≫ g)
    (S : Subobject X) (T : Subobject Y) (h : S ≤ (Subobject.pullback b).obj T) :
    (Subobject.pullback f).obj S ≤
      (Subobject.pullback a).obj ((Subobject.pullback g).obj T) := by
  rw [← Subobject.pullback_comp, ← w, Subobject.pullback_comp]
  exact (Subobject.pullback f).monotone h

private theorem preserves_image {D : Type u} [Category.{v} D] [Abelian D]
    {A B X Y : D} (a : A ⟶ B) (b : X ⟶ Y)
    (f : A ⟶ X) (g : B ⟶ Y) (w : f ≫ b = a ≫ g)
    (S : Subobject A) (T : Subobject B) (h : S ≤ (Subobject.pullback a).obj T) :
    (Subobject.«exists» f).obj S ≤
      (Subobject.pullback b).obj ((Subobject.«exists» g).obj T) := by
  apply (Subobject.gc_exists_pullback f _ _).mpr
  rw [← Subobject.pullback_comp, w, Subobject.pullback_comp]
  exact h.trans ((Subobject.pullback a).monotone
    ((Subobject.gc_exists_pullback g).le_u_l T))

private theorem preserves_inf {D : Type u} [Category.{v} D] [Abelian D]
    {A B : D} (f : A ⟶ B)
    (S S' : Subobject A) (T T' : Subobject B)
    (h : S ≤ (Subobject.pullback f).obj T)
    (h' : S' ≤ (Subobject.pullback f).obj T') :
    S ⊓ S' ≤ (Subobject.pullback f).obj (T ⊓ T') := by
  rw [(Subobject.gc_exists_pullback f).u_inf]
  exact inf_le_inf h h'

private theorem preserves_sup {D : Type u} [Category.{v} D] [Abelian D]
    {A B : D} (f : A ⟶ B)
    (S S' : Subobject A) (T T' : Subobject B)
    (h : S ≤ (Subobject.pullback f).obj T)
    (h' : S' ≤ (Subobject.pullback f).obj T') :
    S ⊔ S' ≤ (Subobject.pullback f).obj (T ⊔ T') :=
  sup_le (h.trans ((Subobject.pullback f).monotone le_sup_left))
    (h'.trans ((Subobject.pullback f).monotone le_sup_right))

private theorem preserves_steps {D : Type u} [Category.{v} D] [Abelian D]
    (K L : CochainComplex D ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (t : K ⟶ L)
    (s : ∀ a : ℤ, (F.step a : CochainComplex D ℤ) ⟶
      (G.step a : CochainComplex D ℤ))
    (hs : ∀ a, s a ≫ (G.step a).arrow = (F.step a).arrow ≫ t) (a n : ℤ) :
    F.complexStep a n ≤ (Subobject.pullback (t.f n)).obj (G.complexStep a n) := by
  apply (Subobject.imageSubobject_le_iff _ _).mpr
  apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
  have w := congrArg (fun h ↦ h.f n) (hs a)
  change (s a).f n ≫ (G.step a).arrow.f n = (F.step a).arrow.f n ≫ t.f n at w
  rw [← w]
  exact imageSubobject_factors_comp_self _ _

set_option linter.unusedVariables false in
/-- A filtered map induces cycle and boundary quotient maps and a representative restriction.
Source: Stacks Project, Homology, Tag 012K, displayed cycle-boundary formulas and
Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-map-restrictions)

Proof: The chain-map equation sends representatives x in F^p with dx in F^(p+r)
to representatives of the target complex: s p preserves F^p and the restrictions
s (p+r) preserve the condition on dx. Apply the pullback universal property defining
the unquotiented representative subobjects to obtain ρ with its inclusion equation.
The graded projection square hg identifies the image of ρ with the image defining
complexCycles. Thus restriction of g to that image yields kz and its monic square.
For boundaries, the chain-map equation takes d(F^(p-r+1)) into d(F^(p-r+1));
preservation of F^p takes its intersection with that image into the corresponding
intersection, and preservation of F^(p+1) takes the added filtration step into its
target counterpart. The graded projection therefore sends complexBoundaries into
complexBoundaries. Restrict this map to the boundary subobjects and cancel their
monic inclusions to obtain the commuting boundary-to-cycle square. Apply cokernel
map to that square to obtain k with its projection equation. Repeat the cycle and
boundary constructions at r=1 with the same s and g to obtain kz₁ and k₁.
All arguments are pullback, image and cokernel universal properties in an abelian
category; zero steps, zero objects and r=1 obey the same construction. No comparison
isomorphisms or naturality equations for homology are part of this conclusion. -/
theorem filteredQuotient_map_restrictions
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r)
    (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex C ℤ))
    (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
    (hs : ∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom)
    (hg : U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega))
    :
    ∃ (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
            (V.obj.filtration.complexCycles p (p + q) r : C))
          (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
            cokernel (Subobject.ofLE _ _ (hBZ V p q r hr))),
          kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
            (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q) ∧
          cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
            kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr)) ∧
          (∃ (kz₁ : (U.obj.filtration.complexCycles p (p + q) 1 : C) ⟶
              (V.obj.filtration.complexCycles p (p + q) 1 : C))
            (k₁ : cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ⟶
              cokernel (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))),
            kz₁ ≫ (V.obj.filtration.complexCycles p (p + q) 1).arrow =
              (U.obj.filtration.complexCycles p (p + q) 1).arrow ≫ g.f (p + q) ∧
            cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫ k₁ =
              kz₁ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q 1 (by omega)))) ∧
          ∃ ρ : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
              (V.obj.filtration.complexCycleRepresentatives p (p + q) r : C),
            ρ ≫ (V.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (s p).f (p + q) := by
  have hstep := preserves_steps U.obj.obj V.obj.obj U.obj.filtration V.obj.filtration
    t.hom.hom s hs
  have hrep (a n j : ℤ) :
      U.obj.filtration.complexCycleRepresentatives a n j ≤
        (Subobject.pullback ((s a).f n)).obj
          (V.obj.filtration.complexCycleRepresentatives a n j) := by
    unfold DecreasingFiltration.complexCycleRepresentatives
    apply preserves_pullback _ _ _ _
      (congrArg (fun h ↦ h.f n) (hs a)).symm
    apply preserves_inf
    · exact hstep a n
    · exact preserves_pullback (t.hom.hom.f n) (t.hom.hom.f (n + 1))
        (U.obj.obj.d n (n + 1)) (V.obj.obj.d n (n + 1))
        (t.hom.hom.comm n (n + 1)).symm
        _ _ (hstep (a + j) (n + 1))
  have hcycle (j : ℤ) : U.obj.filtration.complexCycles p (p + q) j ≤
      (Subobject.pullback (g.f (p + q))).obj
        (V.obj.filtration.complexCycles p (p + q) j) := by
    unfold DecreasingFiltration.complexCycles
    apply preserves_image _ _ _ _ (congrArg (fun h ↦ h.f (p + q)) hg)
    apply preserves_pullback _ _ _ _
      (congrArg (fun h ↦ h.f (p + q)) (hs p)).symm
    apply preserves_sup
    · apply preserves_inf
      · exact hstep p (p + q)
      · exact preserves_pullback (t.hom.hom.f (p + q)) (t.hom.hom.f (p + q + 1))
          (U.obj.obj.d (p + q) (p + q + 1))
          (V.obj.obj.d (p + q) (p + q + 1)) (t.hom.hom.comm _ _).symm _ _
          (hstep (p + j) (p + q + 1))
    · exact hstep (p + 1) (p + q)
  have hboundary (j : ℤ) : U.obj.filtration.complexBoundaries p (p + q) j ≤
      (Subobject.pullback (g.f (p + q))).obj
        (V.obj.filtration.complexBoundaries p (p + q) j) := by
    unfold DecreasingFiltration.complexBoundaries
    apply preserves_image _ _ _ _ (congrArg (fun h ↦ h.f (p + q)) hg)
    apply preserves_pullback _ _ _ _
      (congrArg (fun h ↦ h.f (p + q)) (hs p)).symm
    apply preserves_sup
    · apply preserves_inf
      · exact hstep p (p + q)
      · exact preserves_image (t.hom.hom.f (p + q - 1)) (t.hom.hom.f (p + q))
          (U.obj.obj.d (p + q - 1) (p + q))
          (V.obj.obj.d (p + q - 1) (p + q)) (t.hom.hom.comm _ _).symm _ _
          (hstep (p - j + 1) (p + q - 1))
    · exact hstep (p + 1) (p + q)
  have hquot (j : ℤ) (hj : 1 ≤ j) :
      ∃ (kz : (U.obj.filtration.complexCycles p (p + q) j : C) ⟶
          (V.obj.filtration.complexCycles p (p + q) j : C))
        (k : cokernel (Subobject.ofLE _ _ (hBZ U p q j hj)) ⟶
          cokernel (Subobject.ofLE _ _ (hBZ V p q j hj))),
        kz ≫ (V.obj.filtration.complexCycles p (p + q) j).arrow =
          (U.obj.filtration.complexCycles p (p + q) j).arrow ≫ g.f (p + q) ∧
        cokernel.π (Subobject.ofLE _ _ (hBZ U p q j hj)) ≫ k =
          kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q j hj)) := by
    obtain ⟨kz, hz⟩ := restriction _ _ _ (hcycle j)
    obtain ⟨kb, hb⟩ := restriction _ _ _ (hboundary j)
    have w : Subobject.ofLE _ _ (hBZ U p q j hj) ≫ kz =
        kb ≫ Subobject.ofLE _ _ (hBZ V p q j hj) := by
      rw [← cancel_mono (V.obj.filtration.complexCycles p (p + q) j).arrow]
      rw [Category.assoc, hz, ← Category.assoc, Subobject.ofLE_arrow,
        Category.assoc, Subobject.ofLE_arrow, hb]
    refine ⟨kz, cokernel.map _ _ kb kz w, hz, ?_⟩
    exact cokernel.π_desc _ _ _
  obtain ⟨kz, k, hz, hk⟩ := hquot r (by exact hr)
  obtain ⟨kz₁, k₁, hz₁, hk₁⟩ := hquot 1 (by omega)
  exact ⟨kz, k, hz, hk, ⟨kz₁, k₁, hz₁, hk₁⟩, restriction _ _ _ (hrep p (p + q) r)⟩

end CategoryTheory
