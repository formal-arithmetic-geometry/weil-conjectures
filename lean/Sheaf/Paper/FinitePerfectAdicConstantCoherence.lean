/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantCohomology

/-! # Restriction coherence of the constant finite perfect transition

Source: Stacks Project, Tags 06YY, 09BV and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The explicit constant transition satisfies etale restriction coherence.

Source: Stacks Project, Tags 06YY, 09BV and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-normalization-coherence).

Proof: expand the two displayed arrows as the inverse-image coefficient mates of
the same normalized constant arrow. Naturality of the pullback mate, followed by
the composition law for etale inverse images, identifies both composites on each
etale source. The identity is checked before localization and therefore descends
to the derived categories. No universality or stalk argument is used here.
-/
theorem finitePerfectAdicEtaleConstant_coherence (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    ∀ {U V : Y.Etale} (f : U ⟶ V),
      (localIsomorphismRestrictionComp Y
          (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))) f).inv.app
          (finitePerfectAdicEtaleConstant Y T (n + 1)) ≫
        etaleIsomorphismNormalizationArrow Y
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (finitePerfectAdicEtaleConstantTransition Y T n) U =
      (Etale.upperStar (ModuleCat.{t + 1}
          (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) f.left).mapDerivedCategory.map
          (etaleIsomorphismNormalizationArrow Y
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
            (finitePerfectAdicEtaleConstantTransition Y T n) V) ≫
        (etaleNormalizationCoefficients f.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
          ((localIsomorphismRestriction Y
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) V).obj
            (finitePerfectAdicEtaleConstant Y T n)) ≫
        (normalizationRestrict U.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).map
          ((localIsomorphismRestrictionComp Y
            (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) f).inv.app
            (finitePerfectAdicEtaleConstant Y T n)) := by
  sorry

end AlgebraicGeometry.Scheme
