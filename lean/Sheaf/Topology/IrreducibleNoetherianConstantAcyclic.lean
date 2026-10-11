import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Flasque
import Sheaf.Topology.IrreducibleConstantSections

open CategoryTheory TopologicalSpace Opposite

universe u w'

namespace TopCat

/-! # Constant sheaves are acyclic on irreducible Noetherian spaces
Source: literature/stacks-project/cohomology.tex, Lemma 02UW
(blueprint: lem-sc-irreducible-noetherian-constant-acyclic) -/

/-- The constant abelian sheaf on an irreducible Noetherian space has no higher cohomology.
Source: literature/stacks-project/cohomology.tex, Lemma 02UW
(blueprint: lem-sc-irreducible-noetherian-constant-acyclic)
Proof:
1. Every nonempty open is irreducible; `irreducible_constant_sections` identifies constant
   sections and restrictions, while the empty open has the zero group. Hence the sheaf is flasque.
2. Apply flasque acyclicity on the topological opens site.
-/
theorem irreducible_noetherian_constant_acyclic
    (X : TopCat.{u}) [IrreducibleSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (A : Type u) [AddCommGroup A] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H' ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)) q ⊤) := by
  sorry

end TopCat
