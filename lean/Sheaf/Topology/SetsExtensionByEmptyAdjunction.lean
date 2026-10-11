import Sheaf.Topology.SetsExtensionByEmpty
import Mathlib.Topology.Sheaves.Functors

/-!
# Extension by the empty set: adjunction and stalks

Source: `literature/stacks-project/sheaves.tex`, Lemmas 00A0 and 00A3
(blueprint: `lem-weil-pbc-sets-extension-by-empty-adjunction`).
-/

universe u

open CategoryTheory TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

noncomputable section

variable {X : TopCat.{u}} (U : Opens X)

/--
Source: Stacks Project, Lemma 00A3 (blueprint: lem-weil-pbc-sets-extension-by-empty-adjunction).
The proof composes the presheaf extension and restriction bijection with
sheafification, computes stalks from neighbourhood colimits, and applies the
stalk criterion for sheaf isomorphisms.
-/
theorem extensionByEmpty_adjunction_stalks
    (G : TopCat.Sheaf (Type u) ((toTopCat X).obj U)) :
    Nonempty
        (extensionByEmptyPresheaf U ⊣
          (Presheaf.pullback (Type u) (inclusion' U) ⋙
            presheafToSheaf (Opens.grothendieckTopology ((toTopCat X).obj U)) (Type u))) ∧
      Nonempty
        (extensionByEmpty U ⊣ Sheaf.pullback (Type u) (inclusion' U)) ∧
      (∀ (x : X), x ∉ U →
        IsEmpty (ToType (((extensionByEmpty U).obj G).presheaf.stalk x))) ∧
      (∀ (x : X) (hx : x ∈ U),
        Nonempty
          (G.presheaf.stalk ⟨x, hx⟩ ≃
            ToType (((extensionByEmpty U).obj G).presheaf.stalk x))) ∧
      Nonempty
        (G ≅ (Sheaf.pullback (Type u) (inclusion' U)).obj ((extensionByEmpty U).obj G)) := by
  sorry

end
end TopCat
