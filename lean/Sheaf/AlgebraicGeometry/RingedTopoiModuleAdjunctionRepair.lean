module
public import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf

/-!
# General ringed-topos module adjunction interface

Source: Stacks, Modules on Sites, Tag 03D3 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction).
This declaration repairs the old completed-pullback interface by exposing the arbitrary
ring-object module adjunction used by the supported reconstruction statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The arbitrary-ring module inverse/direct-image adjunction.
Source: Stacks, Tag 03D3 (blueprint: lem-weil-pbc-ringed-topoi-module-adjunction). -/
noncomputable abbrev ringedTopoiModuleAdjunction {T X : Scheme.{u}}
    (f : T ⟶ X) (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  ringSheafAdjunction f B

end AlgebraicGeometry.ProEtale
