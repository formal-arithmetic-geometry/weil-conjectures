/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.Paper.CompletedOrdinaryComparisons

/-! # Identity normalization before deriving open exchange

Source: Stacks Project, etale-cohomology.tex, lemma-shriek-base-change,
and sites-modules.tex, lemma-localize-morphism-ringed-sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Identity on the ordinary module pullback, with the section-normalized adjunction.
Source: Stacks 03D8 and 03DI
(blueprint: lem-cbc-underived-open-exchange-identity). -/
def cbcModulePullId {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) : completedModulePullback (𝟙 T) d ≅ 𝟭 _ :=
  eqToIso (cbcDatumModulePull_eq d (𝟙 T)) ≪≫
    (proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)

/-- The underived inverse open exchange respects the normalized module identity.
Source: Stacks, etale-cohomology.tex, lemma-shriek-base-change, and
sites-modules.tex, lemma-localize-morphism-ringed-sites; identity specialization
(blueprint: lem-cbc-underived-open-exchange-identity).
Proof: identify the completed scalar maps with the datum maps by their finite
projections. Their normalized pullback adjunctions agree: on the model site both
units send a section x to 1 tensor x, and tensor generators and sheafification
force equality of the Hom equivalences. On a pro-etale object V of U, the right
exchange restricts along the canonical map V times_U U to V times_T T. Compose
with the two direct-image identity comparisons, which restrict along the inverse
pullback identities. The composites agree because both underlying scheme maps
have first projection the identity and second projection the structure map.
Functoriality of restriction proves the right-adjoint square on every section,
including over an empty open. Transpose through the two composite adjunctions.
The triangle identities cancel their units and counits and give the displayed
left-adjoint square. The isomorphism on each identity pullback is precisely
cbcModulePullId, since it is obtained from the same section-normalized direct
image by leftAdjointIdIso. This proof uses neither completeness nor a bound. -/
theorem cbcUnderivedInverseExchange_identity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T))
    (M : pbcModules U (pbcAdicCompletion U d)) :
    (cbcUnderivedInverseExchange d sq).app M ≫
        (cbcModulePullId d T).hom.app ((cbcOpenShriek d j inferInstance).obj M) =
      (cbcOpenShriek d j inferInstance).map ((cbcModulePullId d U).hom.app M) := by sorry

end AlgebraicGeometry.Scheme
