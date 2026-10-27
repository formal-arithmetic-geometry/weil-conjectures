/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.SfDerivedDirectImage

/-! # Quotient compatibility of the projection-adjoint comparisons

Source: Stacks Project, Tags 03EK, 06YY and 08TC; Step 5 of
lem-sf-tensor-exchange-ctf-domains.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- Taking scalar-extension adjuncts of the prescribed Roos projections respects
successive quotient transitions. This concerns the actual maps, independently of
constructibility, dimension bounds, or invertibility of these comparisons.

Source: Stacks Project, Tags 03EK, 06YY and 08TC; Step 5 of
lem-sf-tensor-exchange-ctf-domains
(blueprint: lem-sf-direct-image-reduction-transitions).

Proof: the first two maps of a distinguished Roos triangle compose to zero.
Postcompose with the n-th product projection and expand the endomorphism 1-s.
This gives p_(n+1) followed by t_n equal to p_n. Resolve the original complex
by K-flat complexes and compute the scalar-extension adjunctions by the published
representative comparisons. Consecutive reduction is associated ordinary tensor;
the transition sends s tensor x to rho(s) tensor x, and both units send x to
1 tensor x. Restriction of scalars commutes with direct image by the prescribed
section-normalized square, so its derived comparison on K-injective targets
retains this quotient map. The two restricted adjuncts are therefore maps of
the same quotient module, and the n+1 coefficient adjunction identifies both
with the displayed projection relation. Injectivity of this adjunction proves
the square on representatives. Independence of resolutions and localization
prove it in the unbounded derived category. In particular, no faithfulness of
derived restriction and no epimorphism property of a derived unit are used.
The argument also applies to zero towers and empty schemes. -/
theorem sfDirectImageReductionComparison_transition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K)
    (n : ℕ) :
    (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
          (sfDirectImageReductionComparison l E f L (n + 1)) ≫
        sfDirectImageTransition l E f K n =
      (sfDerivedReductionTransition l E Y n).app L.obj ≫
        (scalarReductionDerivedRestriction.{u, u} l E Y n).map
          (sfDirectImageReductionComparison l E f L n) := by
  sorry

end WeilConjectures
