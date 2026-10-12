module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-!
# Local sections of finite locally free quotients

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, Proof of (*), determinant paragraph: local splitting
(blueprint: lem-sc-local-section-quotient-finite-free)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A finite locally free quotient of a short exact sequence admits local sections.

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-sc-riemann-roch.md, Proof of (*), determinant paragraph: local splitting.
The proof fixes a point, trivializes the finite locally free quotient, lifts finitely many
basis sections locally using local surjectivity of an epimorphism of sheaves, intersects the
resulting finitely many neighbourhoods, and defines the section by the lifted basis. The
rank-zero case uses the zero section.
(blueprint: lem-sc-local-section-quotient-finite-free)
-/
theorem exists_local_section_of_shortExact_finiteLocallyFree
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {d : ℕ} (hE₃ : S.X₃.IsFiniteLocallyFreeOfRank d) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj S.X₃ ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₂,
        (Scheme.Modules.restrictFunctor U.ι).map S.g ≫ s = 𝟙 _ := by
  sorry

end AlgebraicGeometry
