module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.Obj

universe u
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (X : Scheme.{u})
abbrev MX := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
#synth (Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)).ReflectsIsomorphisms
#synth (Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)).Additive
#synth HasFiniteBiproducts (MX Λ X)
#synth Preadditive (MX Λ X)
end AlgebraicGeometry.ProEtale.CondensedRing
