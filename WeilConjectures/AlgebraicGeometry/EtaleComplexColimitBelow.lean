/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
/-! # Lower bound of the pulled-back complex colimit

## References

* Stacks Project, Tags 015J and 0EZM
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent page and presentation families.
/-- A colimit of uniformly lower bounded inverse-image complexes has the same lower bound.
(Stacks, Tag 0EZM). -/
theorem etaleComplex_colimit_below
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (L : Cocone G) (hL : IsColimit L) :
    ∀ n : ℤ, n < a → IsZero (L.pt.X n)  := by
  intro n hn
  let ev := HomologicalComplex.eval
    (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ) n
  apply (isColimitOfPreserves ev hL).isZero_pt
  apply (G ⋙ ev).isZero
  intro i
  have hz := (upperStar AddCommGrpCat.{u + 1} (c.π.app i.unop)).map_isZero
    (hbelow i.unop n hn)
  exact hz.of_iso (HomologicalComplex.eval _ _ n |>.mapIso (eG i.unop))


end AlgebraicGeometry.Etale
