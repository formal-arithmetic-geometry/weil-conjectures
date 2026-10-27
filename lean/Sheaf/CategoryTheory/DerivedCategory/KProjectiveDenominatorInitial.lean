/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# K-projective identity denominators are initial

Source: Stacks Project, Derived Categories, Tags 05S8 and 05S9; Categories, Tag 05PU(2).
The unique-section argument is the agent-written expansion of the denominator computation
(blueprint: lem-trf-kprojective-denominator-initial).

## Main declarations

* `CochainComplex.identityQuasiIsoDenominator`: the actual identity denominator.
* `CochainComplex.quasiIsoDenominatorDiagram`: the domain diagram followed by a functor.
* `CochainComplex.IsKProjective.denominator_initial`: initiality, unique sections,
  localization and naturality, with the specified essential-constancy witnesses.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uH vH

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The identity denominator in the homotopy category; the horizontal morphism property is
`⊤`, so every commuting triangle is allowed. Source: Stacks Project, Tags 05S8, 05S9 and
05Q4 (blueprint: lem-trf-kprojective-denominator-initial). -/
def identityQuasiIsoDenominator {A : Type u} [Category.{v} A] [Abelian A]
    (P : CochainComplex A ℤ) :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) :=
  MorphismProperty.Over.mk ⊤ (𝟙 _)
    ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).id_mem _)

/-- The denominator diagram `s : Y ⟶ P ↦ F(Y)`, with every commuting triangle as an arrow.
Source: Stacks Project, Derived Categories, Tag 05S9(2)
(blueprint: lem-trf-kprojective-denominator-initial). -/
def quasiIsoDenominatorDiagram {A : Type u} [Category.{v} A] [Abelian A]
    (P : CochainComplex A ℤ) {H : Type uH} [Category.{vH} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⥤ H :=
  MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⋙
    Over.forget ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⋙ F

/-- For K-projective `P`, the identity denominator is initial, and any functor gives an
essentially constant denominator pro-diagram with value `F(P)`. For the initiality witness
`h`, the section `t_s` is `(h.to s).left`. The cone has these sections as its images,
identity leg and identity retraction at the identity denominator, and that same denominator
as the common earlier stage, with arrows `𝟙` and `h.to s`.

Source: Stacks Project, Derived Categories, Tags 05S8 and 05S9; Categories, Tag 05PU(2)
(blueprint: lem-trf-kprojective-denominator-initial).

Proof (the three steps of the node):
1. Localization inverts `s`. The Hom bijection with K-projective source `P`
   (`lem-coef-kprojective-derived-hom-bijection`, Mathlib `Qh_map_bijective`) lifts its
   inverse uniquely to `t_s`. Injectivity with target `P` gives `t_s ≫ s = 1`.
   Any other section localizes to the same inverse and hence equals `t_s` by injectivity
   with target `Y`. No K-projectivity of `Y` is required.
2. Sections are exactly the arrows from the identity denominator. This proves initiality.
   For a commuting triangle `u`, `t_s ≫ u` is a section of the next denominator and so
   equals its unique section. The section of the identity is the identity. The identity
   denominator supplies nonemptiness and common sources; its arrows equalize parallel
   arrows by uniqueness, proving cofilteredness.
3. Apply `F` to the sections. Their compatibility gives a cone and its identity-stage
   leg is the identity. In Tag 05PU(2), choose this stage, the identity retraction, and,
   for every denominator, the same common stage with arrows the identity and its section.
   Functoriality gives the required transition factorization and the retraction equation.
   These are exactly all clauses of `IsEssentiallyConstantProDiagram`. -/
theorem IsKProjective.denominator_initial
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    IsCofiltered ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) ∧
    ∃ h : IsInitial (identityQuasiIsoDenominator P),
      (∀ s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P),
        (h.to s).left ≫ s.hom = 𝟙 _ ∧
          ∀ t : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶ s.left,
            t ≫ s.hom = 𝟙 _ → t = (h.to s).left) ∧
      (∀ s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P),
        DerivedCategory.Qh.map (h.to s).left =
          (Localization.isoOfHom DerivedCategory.Qh
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) s.hom s.prop).inv) ∧
      (∀ (s s' : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) (a : s ⟶ s'),
        (h.to s).left ≫ a.left = (h.to s').left) ∧
      ∀ (H : Type uH) (_ : Category.{vH} H)
          (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H),
        IsEssentiallyConstantProDiagram (quasiIsoDenominatorDiagram P F)
          (F.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) ∧
        ∃ (c : (Functor.const ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))).obj
              (F.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) ⟶
                quasiIsoDenominatorDiagram P F)
            (r : F.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P) ⟶
              F.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)),
          (∀ s, c.app s = F.map (h.to s).left) ∧
          c.app (identityQuasiIsoDenominator P) = 𝟙 _ ∧
          r = 𝟙 _ ∧
          c.app (identityQuasiIsoDenominator P) ≫ r = 𝟙 _ ∧
          ∀ s, (quasiIsoDenominatorDiagram P F).map (h.to s) =
            (quasiIsoDenominatorDiagram P F).map (𝟙 (identityQuasiIsoDenominator P)) ≫
              r ≫ c.app s := by
  sorry

end CochainComplex
