/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData

/-! # Open extension and the invertible normalized tensor transpose

Source: Zheng Construction 4.1; Stacks 03DI, 0E8I and 0GL1;
the system case of openTensorNormalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact open extension in already fixed geometric coordinates has invertible
tensor-adjunction transpose. The forward tensor isomorphism is not chosen here:
it is recovered by inverting this specified arrow.
Source: blueprint operations proof (2), open tensor step; Stacks 03DI, 0E8I
and 0GL1; openTensorNormalization on the ringed sequence site.
(blueprint: lem-sp-strict-open-tensor-coordinates).

Proof: form extension by zero on the vertical sequence site, using direct sums
over the open factorizations and sheafification. The coefficient action and
the adjacent transitions come from the actual quotient maps. The ordinary
summand Hom correspondence gives the adjunction to the supplied g.pull;
its identity-on-open-sections normalization agrees with the constant-section
level adjunction. This gives both ordinary evaluation equations and their
unit and counit formulas. Exactness permits termwise localization of the
extension, unit and counit, giving Open with its two termwise equations.
Apply the open tensor support argument on this same ringed sequence site.
On the open, the adjunction unit is invertible and the inverse tensor
pullback comparison identifies the displayed transpose with the identity.
On the complementary closed part both sides are zero. The open/closed
restriction functors jointly detect isomorphisms, so this actual system
arrow is invertible. The signed representative normalization of g's tensor
comparison identifies it with precisely the displayed transpose, rather
than an independently chosen isomorphism. These statements include the
empty open, the identity open and zero complexes; they require no flatness
of any quotient transition and do not infer equality of derived arrows
from their evaluations. -/
theorem strictOpenTensorCoordinates (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j) :
    ∃ o : Open l E b j g, ∀ (K : D l E U) (L : D l E T),
      IsIso ((o.derivedAdjunction.homEquiv _ _).symm
        ((tensor l E b U).map (Prod.mkHom (o.derivedAdjunction.unit.app K) (𝟙 _)) ≫
          g.tensorPullback.inv.app ((openD l E b o).obj K, L))) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
