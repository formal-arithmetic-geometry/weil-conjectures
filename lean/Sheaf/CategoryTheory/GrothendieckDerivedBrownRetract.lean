/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Retract

/-! # The localization step in Grothendieck Brown representability

Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`, before the final
Karoubianity argument.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- The localization construction makes a cohomological functor a natural retract
of a representable functor, before splitting any idempotent in the derived category.
Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`, first two paragraphs.
(blueprint: lem-grothendieck-derived-brown-retract)

Proof in words: choose the Gabriel-Popescu module presentation with exact left
adjoint L and fully faithful derived right adjoint RG; the counit L RG is invertible.
The functor H L is cohomological and takes coproducts to products. The free rank-one
module compactly generates the module derived category, so compactly generated
Brown representability gives a representing module complex E. Complete the unit
E -> RG(L(E)) to a distinguished triangle M -> E -> RG(L(E)) -> M[1]. Exactness
of L and the adjunction identities show L(M) is zero. Representability of H L
then gives Hom(M,E)=0. The exact contravariant Hom sequence yields a retraction
RG(L(E)) -> E of the unit. Evaluate this pair of split maps on RG(X). Use the
counit to identify H(L(RG(X))) with H(X), and full faithfulness to identify
Hom(RG(X),RG(L(E))) with Hom(X,L(E)). These identifications and the split maps
are natural in X and give the required retract with vertex L(E). Lift both sides
to the common value universe max(w,vH). Every sum in Brown's construction is
indexed in max(w,vA,vH), as required by the hypotheses. This step does not assert
that the retract is representable and does not split an idempotent. -/
theorem grothendieckDerived_brown_retract
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ E : DerivedCategory A,
      Nonempty (Retract (H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w})
        (uliftYoneda.{vH}.obj E)) := by sorry

end CategoryTheory
