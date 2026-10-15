/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.IndexedCoveringClass
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Canonical
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
import Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings

/-!
# A generating subcategory of sheaves presents the topos

Source: Stacks Project, Sites, Tag 03A1, and Sets, Tag 000X
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Epimorphic indexed families in a subcategory of sheaves, expressed by joint right
cancellation. This is precisely epimorphy of the map from the coproduct, by its universal
property, without choosing that coproduct or restricting its index size.
Source: Sites, Tag 03A1 (blueprint: lem-weil-pbc-sheaf-subcategory-comparison). -/
def sheafSubcategoryEpimorphicFamilies {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) :
    Set (Σ A : E, PreZeroHypercover.{max u v w} A) :=
  {p | ∀ (B : Sheaf J (Type u)) (f g : F.obj p.1 ⟶ B),
    (∀ i, F.map (p.2.f i) ≫ f = F.map (p.2.f i) ≫ g) → f = g}

/-- The restricted Yoneda presheaf functor, with restriction maps given by precomposition
and functoriality in the sheaf by postcomposition.
Source: Sites, Tag 03A1, Hom calculation in the proof of (5)
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison). -/
def sheafSubcategoryNerve {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) : Sheaf J (Type u) ⥤ Eᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft Eᵒᵖ (Sheaf J (Type u))ᵒᵖ (Type u)).obj F.op

/-- A full pullback-closed subcategory containing the sheafified representables presents
its ambient topos, with any prescribed small collection of epimorphic families retained.
Source: Sites, Tag 03A1 (1)-(5), and Sets, Tag 000X
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison).

Proof plan:
1. Sheafification adjunction and Yoneda identify maps from a sheafified representable
   to B with sections of B. Presheaf coproducts are sectionwise; sheafifying them gives
   sheaf coproducts. Local representation of sheafification sections and the epi/local
   surjectivity criterion identify joint epimorphy with the displayed local lifting sieve.
   This also applies to the empty family.
2. Isomorphisms, composites and pullbacks are epimorphic families, using successive
   local lifts and sectionwise fibre products. Fullness and the closure hypothesis
   realize the pullbacks in E.
3. Apply exists_small_coveringFamilies (000X), adjoining the prescribed families, the
   images of the original coverings, and all-sections covers by sheafified representables.
   Equal supports have the same matching families: the diagonal forces equal assignments
   to repeated arrows. Thus the resulting precoverage generates the required topology.
4. Matching maps into a sheaf descend along local lifts. Their values agree on fibre
   products and glue uniquely, independently of the lifts. This proves the nerve is a
   sheaf, and fullness identifies the nerve of F(A) with the representable at A.
5. Sheafified Yoneda is continuous: it takes coverings to epimorphic families and
   preserves existing covering pullbacks by left exactness of sheafification.
6. Local lifting of the unit section of a sheafified representable proves cocontinuity.
7. Local equality and local representation for sheafification prove local faithfulness
   and local fullness, respectively, without a subcanonicity assumption on C.
8. All-sections covers give cover density. Apply the special-cocontinuous comparison
   theorem. Its inverse image on representables is F, naturally in E.
9. The direct-image compatible families are exactly maps of sheaves, by the adjunction
   and Yoneda section bijections. This identifies the equivalence functor with the nerve,
   including both its restriction maps and its functoriality in the ambient sheaf. -/
theorem sheafSubcategory_comparison {C : Type u} [SmallCategory C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J.toGrothendieck (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (Cov₀ : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
    (hsmall : Small.{max u v w} Cov₀)
    (hsub : Cov₀ ⊆ sheafSubcategoryEpimorphicFamilies F) :
    (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
      (⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F ↔
        ∀ (U : C) (a : (F.obj A).obj.obj (op U)),
          Sieve.generate (fun (V : C) (f : V ⟶ U) ↦
            ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj (op V)),
              (F.map (R.f i)).hom.app (op V) b = (F.obj A).obj.map f.op a)
            ∈ J.toGrothendieck U)) ∧
    ∃ (Cov' : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
      (K : Precoverage E) (hK : K.toGrothendieck.Subcanonical)
      (e : Sheaf J.toGrothendieck (Type u) ≌ Sheaf K.toGrothendieck (Type u)),
      Small.{max u v w} Cov' ∧ Cov₀ ⊆ Cov' ∧
      Cov' ⊆ sheafSubcategoryEpimorphicFamilies F ∧
      PreZeroHypercover.IsCoveringClass Cov' ∧ K.IsSiteForCoverings ∧
      (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
        ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F →
          ∃ R' : PreZeroHypercover.{max u v w} A,
            ⟨A, R'⟩ ∈ Cov' ∧ R.presieve₀ = R'.presieve₀) ∧
      (∀ (A : E) (S : Presieve A),
        S ∈ K A ↔ ∃ R : PreZeroHypercover.{max u v w} A,
          ⟨A, R⟩ ∈ Cov' ∧ S = R.presieve₀) ∧
      Nonempty (e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅
        sheafSubcategoryNerve F) ∧
      Nonempty (F ⋙ e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅ yoneda) ∧
      Nonempty ((@GrothendieckTopology.yoneda E _ K.toGrothendieck hK) ⋙ e.inverse ≅ F) := by
  sorry

end CategoryTheory
