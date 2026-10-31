module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.EtaleCohomology.TateTwist.ReductionTateTwistOne
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

#synth (derivedExtendScalars hρ ha X).CommShift ℤ
#synth (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).CommShift ℤ
#synth (derivedExtendScalarsAdjunction hρ ha X).CommShift ℤ
end AlgebraicGeometry.Etale
