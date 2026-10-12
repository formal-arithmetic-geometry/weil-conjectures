module

public import Sheaf.AlgebraicGeometry.Coherent

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Local finite-free replacement for a cokernel relation map.
Source: Stacks Project, Modules, Lemma 01BY.
(blueprint: lem-weil-pbc-coherent-cokernel-relations-local)
Proof: around each point, lift the finitely many sections defining `g` through the cokernel
map, choose finitely many local generators for the image of `f`, and combine those lifts and
generators into `ψ`. The local lifting criterion and the snake lemma produce an epimorphism
from `kernel ψ` onto `kernel g`; shrinking around each point gives the stated map on `U`. -/
theorem coherent_cokernel_relations_local (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G)
    (hF : F.IsFiniteType) (hG : IsCoherent X G)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      (cokernel f).over U) :
    ∃ (m : ℕ)
      (ψ : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin m)) ⟶ G.over U),
      ∃ e : kernel ψ ⟶ kernel g, Epi e := by
  sorry

end AlgebraicGeometry.RingedSpace
