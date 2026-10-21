/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity
import Sheaf.AlgebraicGeometry.AffineSupportVanishing
import Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Support bounds for affine higher direct images

Source: Stacks Project, Etale Cohomology, Tag 0F0X, lemma-interlude-I
(blueprint: lem-kun-affine-direct-image-support-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Affine higher direct images lower the transcendence-degree support bound by their degree.
The target stratum is empty when `a - q < 0`, as expressed by the first conjunct.
Source: Stacks Project, Etale Cohomology, Tag 0F0X, lemma-interlude-I
(blueprint: lem-kun-affine-direct-image-support-bound).

Proof:
1. At a geometric point y with b = trdeg_K kappa(y) > a - q, use affine permanence
   (lem-weil-pbc-affine-morphism-permanence) and the strict-henselization stalk formula
   (prop-weil-pbc-strict-henselization-stalk-formula) to compute the stalk as H^q(T,F_T),
   where T is the pullback of X to the strict local scheme at y.
2. Use lem-kun-strict-local-algebraic-residue-models to express T as a cofiltered limit
   of affine finite-type schemes T_i over a separably closed field L of trdeg_K L = b.
   Their transition maps are affine. Tensor products commute with the ring colimit by
   their universal property, giving the required limit over X.
3. Residue extensions from points of T_i to their images in X are algebraic: they come
   from prime quotients of a tensor product with an algebraic field extension, which
   is integral over the other field. Pullback stalks (lemma-openclosed-stalk-upperstar)
   imply support pulls back into support of F; torsion pulls back too, using
   lem-weil-pbc-torsion-sheaf-characterizations.
4. The transcendence-degree tower formula (lem-kun-transcendence-degree-tower) gives
   b + trdeg_L kappa(z) <= a on this support. If b > a the sheaves F_i vanish by
   lemma-weil-pbc-geometric-stalk-conservative. Otherwise apply
   lem-kun-affine-support-vanishing with bound a - b; q > a - b gives H^q(T_i,F_i) = 0.
5. The canonical pullback transition isomorphisms identify the limit sheaf with F_T.
   Apply lem-weil-pbc-cofiltered-etale-cohomology-continuity to get H^q(T,F_T) = 0.
   By def-kun-support, vanishing of these stalks is exactly the asserted containment.
   This includes degree zero, q > a, and empty schemes. -/
theorem affine_direct_image_support_bound
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] [IsAffineHom f]
    (a : ℤ) (ha : 0 ≤ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf F)
    (hsupport : etaleSheafSupport F ⊆ (X ↘ Spec (.of K)).pointsOfTrdegLE a.toNat)
    (q : ℕ) :
    etaleSheafSupport
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⊆
      {y | 0 ≤ a - (q : ℤ) ∧
        y ∈ (Y ↘ Spec (.of K)).pointsOfTrdegLE (a - (q : ℤ)).toNat} := by
  sorry

end AlgebraicGeometry.Scheme
