/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Equivalence
import Sheaf.Algebra.Homology.SubcategoryLeftResolution
import Sheaf.CategoryTheory.RightFractionDenseSubcategory

/-!
# Derived descent through a bounded above resolving class

Source: Stacks Project, `derived.tex`, Tag 0794, first paragraph of the proof,
with Tags 05T7, 05RT, 0GSL and Categories Tags 04VI, 04VJ, 04VK
(blueprint: lem-trf-resolving-class-derived-descent).

The auxiliary definitions spell out the subcategories and restricted arrow classes
in this statement. `homotopyProperty` is the inverse image of the existing bounded
above derived subcategory, so its objects are exactly the complexes with bounded
above cohomology. `toMinus` is the literal corestriction of `Qh`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w uA vA uB vB uC vC uR vR

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BoundedResolvingDescent

variable (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The cohomologically bounded above part of the homotopy category.
Source: Stacks Project, Tags 05T7 and 0794
(blueprint: lem-trf-resolving-class-derived-descent).
By `DerivedCategory.isLE_iff` and the homology comparison for `Qh`, membership
means that some integer `b` bounds the nonzero cohomology degrees above. -/
def homotopyProperty : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  DerivedCategory.TStructure.t.minus.inverseImage DerivedCategory.Qh

/-- The bounded above complexes with terms in the given class.
Source: Stacks Project, Tag 05T7, part (1), and Tag 0794
(blueprint: lem-trf-resolving-class-derived-descent). -/
def complexProperty (P : ObjectProperty A) : ObjectProperty (CochainComplex A ℤ) :=
  fun M ↦ (∃ b : ℤ, M.IsStrictlyLE b) ∧ ∀ j : ℤ, P (M.X j)

/-- The full resolving subcategory inside the cohomologically bounded above category.
Source: Stacks Project, Tag 0794, first paragraph of the proof
(blueprint: lem-trf-resolving-class-derived-descent). -/
def resolvingProperty (P : ObjectProperty A) :
    ObjectProperty (homotopyProperty A).FullSubcategory :=
  fun M ↦ complexProperty A P M.obj.as

/-- The inclusion of the resolving subcategory into the homotopy category.
Source: Stacks Project, Tag 0794, first paragraph of the proof
(blueprint: lem-trf-resolving-class-derived-descent). -/
def inclusion (P : ObjectProperty A) :
    (resolvingProperty A P).FullSubcategory ⥤ HomotopyCategory A (ComplexShape.up ℤ) :=
  (resolvingProperty A P).ι ⋙ (homotopyProperty A).ι

/-- Quasi-isomorphisms restricted to the cohomologically bounded above category.
Source: Stacks Project, Tags 05RT and 0794
(blueprint: lem-trf-resolving-class-derived-descent). -/
def quasiIsoC : MorphismProperty (homotopyProperty A).FullSubcategory :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage (homotopyProperty A).ι

/-- Quasi-isomorphisms restricted to the bounded above resolving category.
Source: Stacks Project, Tags 05RT and 0794
(blueprint: lem-trf-resolving-class-derived-descent). -/
def quasiIsoR (P : ObjectProperty A) :
    MorphismProperty (resolvingProperty A P).FullSubcategory :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage (inclusion A P)

/-- The localization `Qh` corestricted to the existing bounded above derived category.
Source: Stacks Project, Tag 0794, first paragraph of the proof
(blueprint: lem-trf-resolving-class-derived-descent). -/
def toMinus : (homotopyProperty A).FullSubcategory ⥤ DerivedCategory.Minus A :=
  DerivedCategory.TStructure.t.minus.lift
    ((homotopyProperty A).ι ⋙ DerivedCategory.Qh) (fun M ↦ M.property)

/-- Resolving-class localization, the same-bound resolution, and additive descent.
Source: Stacks Project, Tag 0794, first paragraph of the proof; Tags 05T7,
05RT, 0GSL and Categories Tags 04VI, 04VJ, 04VK
(blueprint: lem-trf-resolving-class-derived-descent).

Proof:
1. For cohomology zero above `b`, good truncation replaces `M` by a complex
   strictly zero above `b`. Its kernel inclusion is a quasi-isomorphism: below
   `b` and in degree `b` it induces the canonical cohomology isomorphisms, and
   above `b` both cohomology objects vanish (`def-weil-abstract-derived-category`).
2. Apply `lem-sfb-subcategory-left-resolution` to this truncation. Compose its
   quasi-isomorphism with the truncation inclusion. All terms lie in `P` and
   the strict upper bound remains `b`; thus every object of C receives a
   quasi-isomorphism from R.
3. Restrict the ambient right calculus of
   `lem-pc-quasi-isomorphisms-multiplicative-system` to C. Every auxiliary source
   in an Ore or cancellation problem is quasi-isomorphic to an object of C,
   so has bounded above cohomology and itself belongs to C.
4. The localization universal property gives J with its inclusion comparison.
   Represent an ambient derived arrow by a roof using
   `lem-pc-right-fraction-representation`. Its denominator makes the roof source
   cohomologically bounded above, so the roof lies in C and proves fullness.
5. For two such roofs with equal images, use
   `lem-pc-right-fraction-common-refinement`. The common denominator puts the
   refinement source in C, giving equality in its localization and faithfulness.
   Localization essential surjectivity transports these Hom bijections to all
   localized objects (`lem-trf-localization-essentially-surjective`).
6. The homology comparisons for Q and Qh identify the essential image of J
   with D minus. Conversely represent any object of D minus by a complex using
   localization essential surjectivity; its homology bound puts that complex in C.
   Corestriction is an equivalence by
   `lem-trf-fully-faithful-ess-surj-equivalence`.
7. Apply `lem-trf-right-fraction-dense-subcategory` to R inside C, using steps
   2 and 3. It gives the right calculus on R and the inclusion equivalence I.
   Composing I with the corestriction of J gives an equivalence T to D minus,
   with the natural comparison to Qh on R.
8. By `lem-trf-additive-homotopy-triangulated`, termwise F acts on homotopy
   classes. Its composite with Qh on R inverts quasi-isomorphisms by the stated
   preservation assumption. The localization universal property gives G on
   the localization of R and a natural isomorphism lambda to this composite.
9. Choose an inverse U to T, with nu : T followed by U isomorphic to the identity,
   and define Fhat as U followed by G. If kappa compares T on localized R with
   Qh, set beta_M = U(kappa_M inverse) followed by nu_M, and set
   rho_M = G(beta_M) followed by lambda_M. Naturality of kappa, nu and lambda
   gives Fhat(Qh(f)) followed by rho_N = rho_M followed by Qh(F(f)).
   This is exactly the naturality of the final natural isomorphism, for every
   homotopy class and hence every chain map; the canonical quotient/Qh
   comparisons identify it with the displayed chain-level normalization.
-/
theorem resolvingClassDerivedDescent
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderFiniteCoproducts]
    (hcover : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X), P Y ∧ Epi p)
    (LC : Type uC) [Category.{vC} LC]
    (qC : (homotopyProperty A).FullSubcategory ⥤ LC) [qC.IsLocalization (quasiIsoC A)]
    (LR : Type uR) [Category.{vR} LR]
    (qR : (resolvingProperty A P).FullSubcategory ⥤ LR)
    [qR.IsLocalization (quasiIsoR A P)] :
    (quasiIsoC A).HasRightCalculusOfFractions ∧
    (quasiIsoR A P).HasRightCalculusOfFractions ∧
    (∃ J : LC ⥤ DerivedCategory A, J.Full ∧ J.Faithful ∧
      Nonempty (qC ⋙ J ≅ (homotopyProperty A).ι ⋙ DerivedCategory.Qh) ∧
      J.essImage = DerivedCategory.TStructure.t.minus) ∧
    (∃ I : LR ⥤ LC, I.IsEquivalence ∧
      Nonempty (qR ⋙ I ≅ (resolvingProperty A P).ι ⋙ qC)) ∧
    (∀ (M : CochainComplex A ℤ) (b : ℤ),
      (∀ j : ℤ, b < j → IsZero (M.homology j)) →
      ∃ (V : CochainComplex A ℤ) (v : V ⟶ M), QuasiIso v ∧
        (∀ j : ℤ, P (V.X j)) ∧ (∀ j : ℤ, b < j → IsZero (V.X j))) ∧
    (∀ (F : A ⥤ B) [F.Additive],
      (∀ (M N : CochainComplex A ℤ) (f : M ⟶ N),
        complexProperty A P M → complexProperty A P N → QuasiIso f →
        QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) →
      ∃ Fhat : DerivedCategory.Minus A ⥤ DerivedCategory B,
        Nonempty ((resolvingProperty A P).ι ⋙ toMinus A ⋙ Fhat ≅
          inclusion A P ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh)) := by
  sorry

end CategoryTheory.BoundedResolvingDescent
