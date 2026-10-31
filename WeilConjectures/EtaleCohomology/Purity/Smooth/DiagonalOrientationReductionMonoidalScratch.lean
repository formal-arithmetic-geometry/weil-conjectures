module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalSheaf

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry.Etale
variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {U X : Scheme.{u}}
  (e : U ⟶ X)
set_option pp.explicit true in
#synth (Sheaf.extendScalars X.smallEtaleTopology ρ ⋙ (e)^*[ModuleCat.{u + 1} Λ']).LaxMonoidal
set_option pp.explicit true in
#synth ((e)^*[ModuleCat.{u + 1} Λ']).LaxMonoidal
set_option pp.explicit true in
#synth ((e)^*[ModuleCat.{u + 1} Λ']).Monoidal
end AlgebraicGeometry.Etale
