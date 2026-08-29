/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The open complement of an open immersion with clopen range

If the range of an open immersion `j : U ⟶ X` is closed, its complement is an open of `X`.
Together with the range of `j` it is then a decomposition of `X` into two complementary
opens, which is what makes the restrictions along `j` and along the complement jointly
conservative on sheaves.

## Main results

- `AlgebraicGeometry.Scheme.Hom.complOpensRange`: the open complement of the range.
- `AlgebraicGeometry.Scheme.Hom.isCompl_complOpensRange`: the range of `j` and its complement
  are complementary opens of `X`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (j : U ⟶ X) (hj : IsClosed (Set.range j.base))

/-- The open complement of the range of a morphism with closed range. -/
def complOpensRange : X.Opens := ⟨(Set.range j.base)ᶜ, hj.isOpen_compl⟩

lemma range_ι_complOpensRange :
    Set.range (complOpensRange j hj).ι.base = (Set.range j.base)ᶜ :=
  Scheme.Opens.range_ι (complOpensRange j hj)

variable [IsOpenImmersion j]

lemma inf_complOpensRange : j.opensRange ⊓ complOpensRange j hj = ⊥ := by
  ext x
  simp [complOpensRange, Scheme.Hom.opensRange]

lemma sup_complOpensRange : j.opensRange ⊔ complOpensRange j hj = ⊤ := by
  ext x
  simp [complOpensRange, Scheme.Hom.opensRange]

lemma isCompl_complOpensRange : IsCompl j.opensRange (complOpensRange j hj) :=
  ⟨disjoint_iff.mpr (inf_complOpensRange j hj), codisjoint_iff.mpr (sup_complOpensRange j hj)⟩

end AlgebraicGeometry.Scheme.Hom
