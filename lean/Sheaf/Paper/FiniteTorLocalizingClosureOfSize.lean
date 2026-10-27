module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-! # Finite-Tor constructible hulls with an explicit coproduct universe

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
fixed indexing universe
(blueprint: def-sfb-finite-tor-localizing-closure-of-size).

The existing generic `localizingClosureOfSize` supplies the intersection. This interface
specializes it to the recorded finite constant-model generators, retaining the original
`localizingClosureProEtale` and admissible coefficient interfaces by public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The ordinary finite-Tor constructible localizing hull, with coproducts indexed in `w`.
This is the same intersection as `localizingClosureProEtale`, with its indexing universe
made explicit; neither the generators nor the ambient derived category change.
Source: blueprint main-20261015, sk-def-localizing-closure, fixed smallness convention
(blueprint: def-sfb-finite-tor-localizing-closure-of-size). -/
def finiteTorLocalizingClosureOfSize
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  CategoryTheory.localizingClosureOfSize.{w}
    (constantModelBoundedConstructible Λ X ⊓ fun K ↦
      DerivedCategory.finiteTorAmplitude _ K)

end AlgebraicGeometry.ProEtale
