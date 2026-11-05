module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

set_option pp.universes true
#check @IsoAlgebra.derivedForgetCommIso
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
#check (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
example : True := by
  have := IsoAlgebra.derivedForgetCommIso.{u+2, u+1, u+2, u+1} (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g _))
  trivial
end AlgebraicGeometry.ProEtaleWeilSheaf
