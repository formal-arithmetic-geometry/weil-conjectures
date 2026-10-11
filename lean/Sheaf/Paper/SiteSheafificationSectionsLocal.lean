module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u w

/-! # Local sections after sheafification
Source: literature/stacks-project/sites.tex, Sites, Theorem 00WB and Lemma 00WK
(blueprint: lem-weil-pbc-site-sheafification-sections-local)
-/

/-- Local representability, descent, and local equality for sheafification on a site.
Source: Sites, Theorem Tag 00WB and Lemma Tag 00WK
(blueprint: lem-weil-pbc-site-sheafification-sections-local).
First identify sheafification with the double plus construction using
lem-weil-pbc-sheafification-plus-theorem. Represent a section locally in the first
plus construction, then refine again to obtain actual presheaf sections. Equality
on overlaps in the first plus construction supplies further covering refinements
(00WK). Conversely, apply the unit to locally compatible representatives; separatedness
makes their images agree on the overlaps, and the sheaf equalizer condition glues
them uniquely (00WB(4)). Finally, lem-weil-pbc-sheafification-plus-separated gives
injectivity of the first plus into the double plus. Equal images of two original
sections therefore agree in the first plus, so the common-refinement relation gives
a covering on which they agree in the original presheaf (00WB(1)-(2)).
Overlap compatibility is tested on every cone over the two covering arrows.
This is equivalent to testing on their fibre product: pull a witnessing covering
back along the cone's comparison map; conversely take the fibre-product cone.
-/
theorem sheafification_sections_local
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasWeakSheafify J.toGrothendieck (Type w)]
    (F : Cᵒᵖ ⥤ Type w) :
    (∀ (U : C) (s : (sheafify J.toGrothendieck F).obj (op U)),
      ∃ (S : Presieve U) (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
        S ∈ J U ∧
        (∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
        (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
          (hf : S f) (hg : S g),
          ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
            ∃ (T : Presieve Z), T ∈ J Z ∧
              ∀ (Y : C) (h : Y ⟶ Z), T h →
                F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg))) ∧
    (∀ (U : C) (S : Presieve U) (_ : S ∈ J U)
      (x : ∀ (V : C) (f : V ⟶ U), S f → F.obj (op V)),
      (∀ (V W : C) (f : V ⟶ U) (g : W ⟶ U)
        (hf : S f) (hg : S g),
        ∀ (Z : C) (a : Z ⟶ V) (b : Z ⟶ W), a ≫ f = b ≫ g →
          ∃ (T : Presieve Z), T ∈ J Z ∧
            ∀ (Y : C) (h : Y ⟶ Z), T h →
              F.map (h ≫ a).op (x V f hf) = F.map (h ≫ b).op (x W g hg)) →
      ∃! s : (sheafify J.toGrothendieck F).obj (op U),
        ∀ (V : C) (f : V ⟶ U) (hf : S f),
          (sheafify J.toGrothendieck F).map f.op s =
            (toSheafify J.toGrothendieck F).app (op V) (x V f hf)) ∧
    (∀ (U : C) (p q : F.obj (op U)),
      (toSheafify J.toGrothendieck F).app (op U) p = (toSheafify J.toGrothendieck F).app (op U) q →
      ∃ (S : Presieve U), S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U) (_ : S f),
          F.map f.op p = F.map f.op q) := by
  sorry

end CategoryTheory
