module
public import WeilConjectures.NumberTheory.Padics.ULiftAdicComplete
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
variable (p : ℕ) [Fact p.Prime]
#synth IsDomain (ULift.{3} ℤ_[p])
example : IsDiscreteValuationRing (ULift.{3} ℤ_[p]) := inferInstance
