-- Measures checking the declared type with a typed diagnostic placeholder.
module

public import WeilConjectures.DeligneLaumon.AffineLine.RealPushforward

set_option maxHeartbeats 200000
@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

example {ι : PadicAlgCl l →+* ℂ} {K : WeilSheaf k₀ l X}
    (hK : K.IsReal ι) (hvan : ∀ ν : ℕ, ν ≠ 1 → IsZero ((higherLowerShriek k₀ l f ν).obj K)) :
    ((higherLowerShriek k₀ l f 1).obj K).IsReal ι := by
  sorry

end AlgebraicGeometry.WeilSheaf
