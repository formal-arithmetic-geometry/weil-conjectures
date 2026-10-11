import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Coverage
/-! # The plus construction of a separated presheaf is a sheaf
Source: literature/stacks-project/sites.tex, Sites, Definition 00WA and
Theorem 00WB, part (2).
Blueprint: lem-weil-pbc-site-plus-of-separated-is-sheaf.
-/
open CategoryTheory
universe u1 v1
namespace CategoryTheory
/-- Source: Sites, Theorem 00WB, part (2) (blueprint: lem-weil-pbc-site-plus-of-separated-is-sheaf).
For a separated presheaf, the canonical map to its plus construction is
objectwise injective and the plus construction is a sheaf. The proof applies
`GrothendieckTopology.inj_of_sep` and `GrothendieckTopology.isSheaf_of_sep`
to the generated Grothendieck topology. -/
theorem sitePlus_of_separated_isSheaf {C : Type u1} [Category.{v1} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (F : Cᵒᵖ ⥤ Type (max u1 v1))
    (hsep : ∀ (X : C) (S : (Precoverage.toGrothendieck J).Cover X)
      (x y : F.obj (Opposite.op X)),
      (∀ I : S.Arrow, F.map I.f.op x = F.map I.f.op y) → x = y) :
    (∀ X : C, Function.Injective
      (((Precoverage.toGrothendieck J).toPlus F).app (Opposite.op X))) ∧
      Presheaf.IsSheaf (Precoverage.toGrothendieck J)
        ((Precoverage.toGrothendieck J).plusObj F) := by
  sorry
end CategoryTheory
