/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Restrictions of filtered maps to cycles and boundary quotients

Source: Stacks Project, Homology, Tag 012K, Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-map-restrictions).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

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
                (s p).f (p + q) := by sorry

end CategoryTheory
