/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.Sites.ZariskiTorsorRepresentativeExists

/-!
# Torsor classes as boundaries of the representative extension

## References

* Stacks Project, Cohomology of Sheaves, Lemma 02FQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

/-- Every Zariski torsor is represented by the fibre over one of an extension by the
constant integer sheaf, and that fibre has the connecting class of one. Conversely,
the fibre of every such extension is a torsor with this class.

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ. -/
theorem torsor_h1_boundary_representative (X : Scheme.{u})
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (T : G.Torsor) :
    (∃ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ι : G ⟶ E) (p : E ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
      (hzero : ι ≫ p = 0)
      (hS : (ShortComplex.mk ι p hzero).ShortExact),
      Nonempty (Torsor.Iso T
        (Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X))
          hS
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩))) ∧
      CategoryTheory.Sheaf.Torsor.classH1 G (IsTerminal.ofUnique (⊤ : Opens X)) ⟦T⟧ =
        H.δSections hS
          (IsTerminal.ofUnique (⊤ : Opens X))
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩)) ∧
      ∀ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ι : G ⟶ E) (p : E ⟶
          (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
        (hzero : ι ≫ p = 0)
        (hS : (ShortComplex.mk ι p hzero).ShortExact),
        CategoryTheory.Sheaf.Torsor.classH1 G (IsTerminal.ofUnique (⊤ : Opens X))
            ⟦Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS
              ((toSheafify (Opens.grothendieckTopology X)
                ((Functor.const (Opens X)ᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩)⟧ =
          H.δSections hS (IsTerminal.ofUnique (⊤ : Opens X))
            ((toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩) := by
  constructor
  · obtain ⟨E, ι, p, hzero, hS, hT⟩ := zariski_torsor_representative_exists X G T
    refine ⟨E, ι, p, hzero, hS, hT, ?_⟩
    rw [_root_.Quotient.sound hT]
    exact Torsor.classH1_lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS _
  · intro E ι p hzero hS
    exact Torsor.classH1_lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS _

end CategoryTheory.Sheaf
