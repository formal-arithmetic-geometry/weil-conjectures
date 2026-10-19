/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions

/-! # Normalized ring-sheaf diagram for embedded integral coefficients

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2;
Stacks Tags 099I and 099L.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
namespace AlgebraicGeometry.ProEtale

/-- The embedded scalar and first reduction maps form the canonical constant/limit
coefficient diagram after the section-action and small-site identifications. All three
squares are part of the assertion; arbitrary unrelated coefficient isomorphisms do not
suffice. There is no module-category, derived-category or completeness assertion here.

Source: blueprint main-20261015, sk-lem-integral-models, proof step 2;
Stacks Tags 099I and 099L.
(blueprint: lem-sfb-embedded-integral-coefficient-ring-diagram).

Proof: constant sheafification and the inverse image from the pro-etale point identify
the pulled-back discrete ring with the constant ring on the equivalent small site.
The identity scalar sections specify this identification. Identify each positive finite
residue ring with its continuous-function ring: on a profinite test object the fibres
of a continuous function form a finite clopen covering, so the constant-function map
is locally surjective and injective. Sheafification therefore makes that specified map
an isomorphism. Its normalization keeps each scalar unchanged. The integral limit
comparison identifies the continuous integer coefficient ring with the limit of these
constant positive quotients. Transport the quotients along ULift.ringEquiv; it maps the
uniformizer ideal to I and intertwines the quotient homomorphisms. These finite-level
identifications commute with the transitions because they keep the same residue scalar.
Apply the limit universal property to obtain the completed ring isomorphism. Its first
projection is the specified first reduction, giving the second square. Test the first
square on the constant-sheaf unit, where both maps send each scalar to its compatible
residue classes; the limit projections jointly distinguish sections. The third square
follows by the same unit calculation for the constant quotient map. Reconstructing
section rings and precomposing with AsSmall.down preserve these actual maps. Empty
schemes are covered by the same universal properties. -/
theorem embeddedIntegral_coefficient_ring_diagram
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
    let I : Ideal A := Ideal.map ULift.ringEquiv.symm.toRingHom (Ideal.span {π})
    let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
    ∃ (eB : IntegralModelsStacks.smallRing X (integralCoefficientObject X ℓ E) ≅
        ConstantCompletion.completed J A I)
      (eR : IntegralModelsStacks.smallRing X
        (condensedRingObj (IntegralModelsEmbedded.discreteObj
          (PadicAlgCl.integers ℓ E.1)) X) ≅ ConstantCompletion.constant J A)
      (eSB : IntegralModelsStacks.smallRing X
        (completedCoefficient X
          (Profinite.continuousMapRingSheaf (completedResidue ℓ E π 0))).X ≅
            ConstantCompletion.finite J A I 0)
      (eSR : IntegralModelsStacks.smallRing X
        (condensedRingObj (IntegralModelsEmbedded.discreteObj
          (completedResidue ℓ E π 0)) X) ≅ ConstantCompletion.finite J A I 0),
      (IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X) ≫ eB.hom =
        eR.hom ≫ ConstantCompletion.coefficientMap J A I) ∧
      (IntegralModelsStacks.smallMap X
        (completedCoefficientMap X (completedReduction ℓ E π 0)).hom ≫ eSB.hom =
          eB.hom ≫ ConstantCompletion.projection J A I 0) ∧
      (IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X) ≫
        eSR.hom = eR.hom ≫ ConstantCompletion.quotient J A I 0) := by sorry

end AlgebraicGeometry.ProEtale
