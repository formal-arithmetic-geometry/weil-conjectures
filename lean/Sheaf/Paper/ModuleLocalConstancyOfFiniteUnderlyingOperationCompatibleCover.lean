module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction

/-! The finite operation refinement needed for local constancy of module sheaves.
(blueprint: lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover)
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The module operations lift an underlying constant trivialization.

Source: Stacks Project, Tag 0DV5, proof of (2)--(3), using Tag 093S (1).  Starting
from a cover on which the underlying sheaf of sets is constant, refine it successively
for addition, zero, negation, and scalar multiplication (there are finitely many
scalars).  The resulting constant maps satisfy the module identities after evaluation
at a geometric point, and hence give a constant sheaf of modules on every member.
This is the operation-lifting subargument; the finite underlying-stalk hypothesis is
used only to obtain the cover supplied to this theorem.
(blueprint: lem-pod-module-local-constancy-of-finite-underlying-operation-compatible-cover) -/
theorem module_operationCompatibleCover
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hG : G = (sheafForget Y.smallEtaleTopology).obj F)
    (𝒰 : Cover.{u} etalePrecoverage Y)
    (h𝒰 : ∀ i : 𝒰.I₀,
      (G.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) :
    IsLocallyConstantSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
