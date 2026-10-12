/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Sheaf.Topology.AbelianOpenExtensionByZero
import Sheaf.Topology.ConstantSheafLocallyConstantComparison
import Sheaf.Topology.AbelianOpenExtensionByZeroStalks

/-! # Positive constant compact-open components

Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
(blueprint: lem-sc-constant-subsheaf-positive-presentation)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Refine a finite compact-open presentation into positive constant components.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
(blueprint: lem-sc-constant-subsheaf-positive-presentation)

Proof: Evaluate each original component on its canonical unit section. Compose its
image with isoC and view it as a locally constant integer function. Its fibres give a
finite clopen partition of the compact domain; each fibre is compact in X. Restrict
the section to every fibre. A section of K on V defines a map from the constant integer
sheaf on V by integer multiplication, and then a map from its extension by zero by
adjunction. Delete the zero fibres: their sections vanish since ι is monic. Replace
negative sections and their component maps by their negatives. Their images are the
positive absolute values. On each stalk the refined components generate exactly the
same subgroup as the original components: a point of an original domain is in exactly
one fibre, and the sign change preserves the generated subgroup. Outside the domains
the extension-by-zero stalks vanish. Thus the resulting coproduct map is stalkwise
surjective and therefore epi. Enumerate the finite family by Fin n. If all fibres are
zero, K has zero stalks and the empty coproduct map is epi. No intersection-compactness
hypothesis or attained-divisor assertion is used in this step. -/
theorem constantSubsheaf_positive_presentation
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g) :
    ∃ (n : ℕ) (A : Fin n → Opens X),
      (∀ i, IsCompact (A i : Set X)) ∧
      ∃ (c : Fin n → ℕ), (∀ i, 0 < c i) ∧
      ∃ (f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K),
        Epi (Sigma.desc f) ∧ ∀ i,
        (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ)) := by
  sorry

end TopCat.Sheaf
