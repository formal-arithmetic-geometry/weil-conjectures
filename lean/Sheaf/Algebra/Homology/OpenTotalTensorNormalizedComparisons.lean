module

public import Sheaf.Algebra.Homology.OpenTotalTensorCoefficientNormalization

/-! # Normalized open total tensor comparisons

Source: Stacks Project, Modules on Sites, Tag 0E8I, and Cohomology on Sites,
Tag 0GL1; agent coefficient refinement
(blueprint: lem-sf-open-total-normalized-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


attribute [local irreducible] SheafOfModules.monoidalCategory

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
namespace SheafOfModules.OpenTotalTensorCoefficient

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The three ordinary chain comparisons exist with their generator normalization.
Source: Stacks Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Tag 03EL, and Cohomology on Sites, Tag 0GL1. Agent cochain refinement.
(blueprint: lem-sf-open-total-normalized-comparisons).

Proof: totalize the normalized module projection comparison over every coefficient
ring. Extension preserves the coproduct indexed by p+q=n because it is a left
adjoint. Naturality in each differential gives the chain identity, with the same
sign (-1)^p. Totalize the coefficient-linear comparison from slice tensor generator
coherence degreewise to obtain linear. Restriction and scalar extension have the
same sectionwise balanced tensors, so their sheafifications give
restrictionCoefficient. The forward generator equations are the corresponding
module equations followed by coproduct insertions; inverse equations follow by
applying the inverse maps to the forward equations. This construction asserts no
interchange equation and constructs no coefficient transitions. -/
theorem normalizedComparisons_exists :
    ∃ e : Comparisons.{c, v, r} R V,
      GammaNormalization.{c, v, r} R V e ∧ LinearNormalization.{c, v, r} R V e ∧
      RestrictionNormalization.{c, v, r} R V e := by sorry

end SheafOfModules.OpenTotalTensorCoefficient
