/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Localization data preceding the Grothendieck Brown retract

Source: Stacks Project, Tag 0F5X, first paragraph.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Gabriel-Popescu localization followed by Brown representability on the module
category supplies a representation of the pullback of H.  Source: Stacks Project,
Tag 0F5X, `injectives-lemma-brown`, first paragraph, and Tag 0F5V.
(blueprint: lem-g2-grothendieck-derived-localization-brown-data)

Proof in words: choose a Gabriel-Popescu presentation by modules over the endomorphism
ring of a generator. Its exact localization induces L on derived categories, with
fully faithful derived right adjoint R and invertible counit. L is exact and preserves
coproducts, so H composed with L is cohomological and sends coproducts to products.
The free rank-one module is a compact generator of the module derived category.
Apply compact-generator Brown representability to obtain E and its natural Hom
bijections. Lift both sets to max(w,vH), obtaining the displayed isomorphism.
Use module complexes in the universe max(w,vH), so their Hom types and the
lifted H values share a universe. Lift the object universe, if necessary, to
max(uA,vA,max(w,vH)+1). The explicit larger coproduct hypothesis covers the
universe used in Brown's construction. No splitting of the unit
or retract in the target category is included in this assertion. -/
theorem grothendieckDerived_localization_brown_data
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
        (adj : L ⊣ R), IsIso adj.counit ∧
        ∃ E : B, Nonempty (uliftYoneda.{vH}.obj E ≅
          L.op ⋙ H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w}) := by sorry

end CategoryTheory
