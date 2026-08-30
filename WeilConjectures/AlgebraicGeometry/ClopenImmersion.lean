/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Open immersions with clopen range

An open immersion `j : U ⟶ X` whose range is also closed presents `X` as the disjoint union
of the range of `j` and of the open complement of that range. This file introduces that
complement and records the two facts that make it a decomposition of `X`: the two ranges are
disjoint and they cover `X`.

The decomposition is what makes restriction along `j` and along the complement jointly
conservative on étale sheaves, hence what makes `j_!` agree with `j_*`; see
`WeilConjectures.SixFunctors.LowerShriek.Proper`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.complOpensRange`: the open complement of the range of a
  morphism with closed range.

## Main results

- `AlgebraicGeometry.Scheme.Hom.inter_range_ι_complOpensRange` and
  `AlgebraicGeometry.Scheme.Hom.union_range_ι_complOpensRange`: the range of `j` and the
  range of the inclusion of its complement are disjoint and cover `X`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsClosed (Set.range j.base))

/-- The open complement of the range of a morphism with closed range. -/
def complOpensRange : X.Opens := ⟨(Set.range j.base)ᶜ, hj.isOpen_compl⟩

@[simp]
lemma range_ι_complOpensRange :
    Set.range (complOpensRange j hj).ι.base = (Set.range j.base)ᶜ :=
  Scheme.Opens.range_ι (complOpensRange j hj)

/-- The range of `j` and the range of the inclusion of its complement are disjoint. -/
lemma inter_range_ι_complOpensRange :
    Set.range j.base ∩ Set.range (complOpensRange j hj).ι.base = ∅ := by
  simp [complOpensRange]

/-- The range of `j` and the range of the inclusion of its complement cover `X`. -/
lemma union_range_ι_complOpensRange :
    Set.range j.base ∪ Set.range (complOpensRange j hj).ι.base = Set.univ := by
  simp [complOpensRange]

end AlgebraicGeometry.Scheme.Hom
