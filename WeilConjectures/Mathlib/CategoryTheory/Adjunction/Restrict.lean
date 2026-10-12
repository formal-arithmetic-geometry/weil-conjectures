/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Left adjoints commuting with fully faithful functors

Let `iC : C ⥤ C'` and `iD : D ⥤ D'` be fully faithful, and let `L' ⊣ R'` and `L ⊣ R` be
adjunctions `C' ⇄ D'` and `C ⇄ D` such that `iD ⋙ R' ≅ R ⋙ iC`. If `L'` maps the image of `iC`
into the essential image of `iD`, then `iC ⋙ L' ≅ L ⋙ iD`: lifting `iC ⋙ L'` along `iD` gives a
functor `C ⥤ D` which is left adjoint to `R` by `CategoryTheory.Adjunction.restrictFullyFaithful`,
hence isomorphic to `L`.

## Main definitions

- `CategoryTheory.Adjunction.compIsoOfForallMemEssImage`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {iC : C ⥤ C'} {iD : D ⥤ D'} (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (comm : iD ⋙ R' ≅ R ⋙ iC) (h : ∀ X, iD.essImage (L'.obj (iC.obj X)))

/-- **Left adjoints commute with fully faithful functors preserved by them.** If the right
adjoints commute with the fully faithful functors `iC`, `iD`, and the left adjoint `L'` maps the
image of `iC` into the essential image of `iD`, then the left adjoints commute with `iC`, `iD`:
`iC ⋙ L' ≅ L ⋙ iD`. -/
noncomputable def compIsoOfForallMemEssImage : iC ⋙ L' ≅ L ⋙ iD :=
  have := hiD.full
  have := hiD.faithful
  (Functor.essImage.liftFunctorCompIso (iC ⋙ L') iD h).symm ≪≫
    Functor.isoWhiskerRight
      ((adj'.restrictFullyFaithful hiC hiD
        (Functor.essImage.liftFunctorCompIso (iC ⋙ L') iD h).symm comm).leftAdjointUniq adj) iD

end CategoryTheory.Adjunction
