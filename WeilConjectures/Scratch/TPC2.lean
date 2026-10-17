module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ConstructibleReduction

universe u
open CategoryTheory
variable {A : Type (u + 1)} [CommRing A] (T : AlgebraicGeometry.Scheme.{u})
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
set_option pp.explicit true in
#synth Linear A (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
set_option pp.explicit true in
#synth Linear A (Sheaf J (ModuleCat.{u + 1} A))
set_option pp.explicit true in
#synth Linear A (DerivedCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
set_option pp.explicit true in
#synth Linear A (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
