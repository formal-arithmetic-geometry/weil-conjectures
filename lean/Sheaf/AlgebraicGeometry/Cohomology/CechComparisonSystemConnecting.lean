module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Any normalized Čech comparison system satisfies its stored connecting law.
Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-cech-comparison-system-existence-connecting)
Proof: The connecting identity is one of the fields of `CechComparisonSystem`;
project that field for the supplied system. -/
theorem cechComparisonSystem_comparison_connecting
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : CechComparisonSystem U hcover)
    (q : ℕ) (T : ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) :
    TopCat.Sheaf.cechδ U hT hg q ≫ (c.comparison (q + 1)).app T.X₁ =
      (c.comparison q).app T.X₃ ≫ Sheaf.functorHδ hT q := by
  exact c.connecting T hT hg q
end AlgebraicGeometry.Scheme.Modules
