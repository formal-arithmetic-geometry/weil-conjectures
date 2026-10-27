/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.FinitePullbackStrictTowerData

/-! # Quotient comparison and its ordinary finite evaluations

Source: Stacks Project, Tags 03EK, 03EL and 07A4.
(blueprint: lem-a1-balanced-finite-tower-quotient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData

namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The pulled tensor-reduction tower has the quotient-unit-normalized comparison.
Its degreewise maps are the unique normalized ordinary finite comparisons,
including the literal published comparison after additive universe transport.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL; steps 1, 2, 4, 5
and the ordinary-comparison part of step 8 of
lem-a1-balanced-finite-tower-generator-comparison.
(blueprint: lem-a1-balanced-finite-tower-quotient-comparison).

Proof: the completed uniformizer has the compatible constant residues. The
constant inverse-image isomorphisms preserve them, so the coefficient map sends
the pulled uniformizer to the target uniformizer, by equality of limit
projections. The specified two-term coefficient resolution identifies S_n with
the cokernel of the (n+1)st uniformizer power, through its actual projection.
Exact module inverse image preserves this cokernel. Thus the coefficient square
is the square of actual principal sheaf quotients. Apply the ideal-quotient
scalar associator to this square and compose with the inverse-image tensor
identification and the balanced coefficient-square comparison. Its formula on
b times the pulled quotient-unit tensor is b times the finite generator.
The associator's transition equations, and the projection identities, assemble
these maps into the natural isomorphism c of the actual strict towers.

For each n the same module-level construction gives the ordinary comparison e.
Local tensor generation makes it the unique map with OrdinaryNormalization:
quotient residues lift locally, and the pullback adjunction units generate
locally after restriction. Sheaf separation then gives equality of maps and
hence of natural isomorphisms. Tensor with the degree-zero quotient has its
canonical natural isomorphism r to ordinary reduction; in each homogeneous
summand it sends x tensor z to the recorded tensor section z tensor x.
Its inverse inserts the degree-zero summand. The single-complex unitor and
the direct-sum universal property prove invertibility and chain naturality;
the quotient maps prove tower naturality. This is ReductionNormalization.
The formulas for c, r and e agree on the same locally generating pure tensors,
so c in each degree is pull(r) followed by e. This holds for all P, in
particular for good P.

For PublishedCompatibility, transport both module-level tensor constructions
sectionwise using the supplied additive module equivalences and coefficient
ring equivalences. The source and target transports are obtained from the
sheafified tensor universal properties, on generators by source_unit and
target_tensor of PublishedOrdinaryTransport. Their inverses use the inverse
section equivalences. Restriction and scalar compatibility make these actual
section transports. The prescribed unit and tensor equations determine both
transports uniquely, again by local tensor generation and sheaf separation.
The published completedReductionOrdinaryComparison has the same quotient-unit
formula by its normalization theorem. The coefficient projection and structural
compatibilities in PublishedCoefficients therefore make its conjugate equal to
e on each local generator, and hence on every section. This proves the stated
unique existence of the transport and the literal conjugation equation. -/
theorem quotient_comparison_with_ordinary_evaluations :
    ∃ c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g,
      QuotientUnitNormalization l E g c ∧
      (∀ n : ℕ, ∃! e : ordinaryReduction l E Y n ⋙ pull l E g ≅ ordinaryFinite l E g n,
        OrdinaryNormalization l E g n e ∧ PublishedCompatibility l E g n e ∧
        ∀ (P : CochainComplex (Modules l E Y) ℤ),
        integralOperationsGoodComplex l E Y P →
          ∃ r : tensorReduction l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor,
            ReductionNormalization l E Y P r ∧ ∀ i : ℤ,
              (((c.hom.app P).app (op n)).f i) =
                (pull l E g).map (((r.hom.app (op n)).f i)) ≫
                  (e.hom.app (P.X i))) := by sorry

end WeilConjectures.BalancedFiniteTower
