/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerNormalizedTheta
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerAugmentationSquare

/-! # Koszul generator comparison and augmentation compatibility

Source: Stacks Project, Tags 03EK, 03EL and 07A4.
(blueprint: lem-a1-balanced-finite-tower-koszul-augmentation).
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

/-- The natural Koszul comparison respects both basis vectors and intertwines
any balanced and quotient-unit-normalized finite comparisons with augmentation.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 and sites-modules.tex,
Tag 03EK; steps 1 (uniformizer preservation), 6 and 7 of
lem-a1-balanced-finite-tower-generator-comparison.
(blueprint: lem-a1-balanced-finite-tower-koszul-augmentation).

Proof: the coefficient map preserves the uniformizer because it preserves all
its constant residues. Apply ordinary cochain tensor pullback coherence and
the action unitor on the two terms of the principal Koszul complex. They send
(x tensor e_j) tensor b to (x tensor b) tensor e'_j, for j = -1 and 0.
The differential is multiplication by the (n+1)st uniformizer power and the
transition has components (uniformizer, 1). Uniformizer preservation therefore
makes these maps commute with the differentials and transitions. Cochain
pullback coherence handles the full direct-sum totalization: neither homogeneous
factor moves, so d_P tensor 1 and (-1)^degree times 1 tensor d_Q have exactly
the original signs. Naturality in P gives the natural isomorphism theta.

For the square, evaluate on b times a pulled homogeneous tensor x tensor e_0.
The theta, augmentation, lambda route gives the finite generator multiplied by
pi_n(b), using BalancedNormalization. The pulled augmentation, c route has
the same value by QuotientUnitNormalization and linearity. On e_-1 both
augmentations vanish. The two basis vectors generate the two Koszul terms;
the tensor direct-sum inclusions and local pulled pure tensors jointly
determine each map. Equality on these sections, extended by sheafification
and sheaf separation, proves the equality of chain maps at every n. Functor
extensionality proves the equality of strict tower maps for every P.
This argument applies to every supplied pair of normalized comparisons,
without choosing their isomorphisms or assuming exactness of ordinary G. -/
theorem koszul_augmentation_compatibility
    (lambda : G l E g ⋙ reductions l E X ≅ finite l E g)
    (c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g)
    (hlambda : ∀ P : CochainComplex (Modules l E Y) ℤ,
      BalancedNormalization l E g P (lambda.app P))
    (hc : QuotientUnitNormalization l E g c) :
    ∃ theta : koszuls l E Y ⋙ diagramPull l E g ≅ G l E g ⋙ koszuls l E X,
      (∀ P : CochainComplex (Modules l E Y) ℤ,
        KoszulNormalization l E g P (theta.app P)) ∧
      (∀ P : CochainComplex (Modules l E Y) ℤ,
        (theta.hom.app P) ≫ augmentation l E X ((G l E g).obj P) ≫ lambda.hom.app P =
          (diagramPull l E g).map (augmentation l E Y P) ≫ c.hom.app P) := by
  obtain ⟨e, hlevel, hnorm, hnatural⟩ := normalized_theta_exists l E g
  let component (P : CochainComplex (Modules l E Y) ℤ) :
      (koszuls l E Y ⋙ diagramPull l E g).obj P ≅
        (G l E g ⋙ koszuls l E X).obj P :=
    NatIso.ofComponents (e P) (hlevel P)
  let theta : koszuls l E Y ⋙ diagramPull l E g ≅ G l E g ⋙ koszuls l E X :=
    NatIso.ofComponents component (by
      intro P P' f
      apply NatTrans.ext
      funext n
      exact hnatural f n)
  have htheta (P : CochainComplex (Modules l E Y) ℤ) :
      KoszulNormalization l E g P (theta.app P) := by
    exact hnorm P
  refine ⟨theta, htheta, ?_⟩
  intro P
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  exact normalized_theta_augmentation_square l E g lambda c hlambda hc theta P (htheta P) n k

end WeilConjectures.BalancedFiniteTower
