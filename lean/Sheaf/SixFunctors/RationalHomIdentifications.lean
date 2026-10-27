/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.SixFunctors.RationalOperationsData

/-! # The full rational Hom adjunction and its scalar evaluation square

Source: lem-coef-rational-operations, steps 2--9, 12 and 20
(blueprint: lem-sf-rational-hom-identifications).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The full rational tensor-Hom adjunction, with its normalized integral evaluation,
identifies Verdier duality with Hom into the dualizing object and respects finite scalars.
Source: lem-coef-rational-operations, DAG proof steps 2--9, 12 and 20
(blueprint: lem-sf-rational-hom-identifications).

Proof: for complete constructible inputs P,K, compute the completed tensor using their
flat-term K-flat representatives and the normalized finite reduction tower. The residue-Tor
bounds and finite tensor theorem give a common constructible interval; normalized effectivity
makes its limit complete. The quotient maps define the canonical completion unit, with zero
shifted mapping-fiber coordinate. Its reductions are invertible. The cone has invertible
uniformizer, so has no maps, in any shift, into finite reductions. Applying Hom into the
complete target's Roos triangle gives the same vanishing for that target; the completion
triangle then gives the Hom bijection induced by the completion unit. Ordinary ringed-site
currying on K-flat and K-injective representatives combines with this bijection. Integral Hom
closure restricts it to the full constructible categories. Tensor the linear Hom bijection
with the fraction field: objects are unchanged, and pure tensors determine the rational
maps. Its counit is precisely ordinary evaluation preceded by the inverse completion map.
Specializing the second argument to omega, compare with A and B using their object,
pure-map and evaluation-integral equations; transposition gives the stated natural duality
identifications and evaluation equations. Finally finite-free scalar extension commutes
with the strict tensor tower, completion unit and ordinary currying. On local tensors its
Hom comparison sends h tensor s and k tensor t to h(k) tensor st. Hence the two completed
evaluations agree. Localizing this equation proves HomScalarCompatibility. These
constructions apply independently to A and B, including identity and ramified extensions. -/
theorem rationalHom_identifications
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (A : RationalVerdier.Datum D l hl X E wE)
    (B : RationalVerdier.Datum D l hl X L wL) :
    ∃ (hE : HomIdentification l E X D hl wE A)
      (hL : HomIdentification l L X D hl wL B),
      HomScalarCompatibility l E X D hl L ι wE wL A B hE hL := by sorry

end WeilConjectures.RationalOperations
