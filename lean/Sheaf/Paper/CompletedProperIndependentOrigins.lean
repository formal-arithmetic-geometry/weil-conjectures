/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.StrictTowerExchangeMateNormalization

/-! # Completed proper exchange with independent finite origins

Source: Stacks Project, proetale.tex, Tags 09C9 and 099N; sites-cohomology.tex,
Tag 07A7. The strict normalization and ambient naturality refine the construction
omitted in the proof of Tag 09C9.
(blueprint: lem-cbc-completed-proper-independent-origins).

The map is the existing `AdicCoefficientDatum.completedExchange`, whose definition
is Rlim of strict projection, Rlim of strict exchange, and the inverse canonical
direct-image/Rlim comparison, in that order. Its source uses `completedPull` on
all ambient objects. The isomorphism clause retains one independent bounded-below
etale-origin pair for every positive quotient, with no common bound.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The specified three-factor completed proper exchange is natural on the whole
ambient derived category. On intrinsically complete objects with independent finite
origins it is invertible and is the specified completed base-change map.

`PbcIsIntrinsicallyComplete` is the published existential Koszul-unit predicate,
transported to the same completed coefficient ring. Its canonical implication
`pbcIntrinsicComplete_towerComplete` supplies exactly the completion hypothesis of
`completedBaseChangeMap`. The witnesses retain a separate object of D+ and its
comparison isomorphism at each n; n denotes the positive exponent n+1.

Source: Stacks Tags 09C9 (theorem-proper-base-change), 099N
(lemma-pushforward-Noetherian-case), and 07A7 (remark-base-change).
(blueprint: lem-cbc-completed-proper-independent-origins).

Proof:
1. On the small ringed diagram sites, profinite coefficient inverse image is an
isomorphism. Tensor/pullback comparison gives the strict reduction comparison.
Normalized evaluation identifies the projection adjunct with the finite projection
map. Perfectness of every quotient and the perfect projection formula make each
such map invertible for every ambient object. Levelwise kernels, cokernels and
cohomology, followed by derived isomorphism detection, make the strict projection
invertible without completeness or origins.
2. Write the strict exchange as V R(e) U inverse, with U and V the specified
projection/tensor comparisons and e the ambient ringed mate. Projection naturality
in both variables and tensor-comparison naturality give natural U and V. Ambient
mate naturality then gives naturality of this conjugate as a strict tower morphism,
before evaluation; no lift is selected from a family of evaluated arrows.
3. The canonical direct-image/Rlim comparison is natural, computed by the identity
of underived direct-image/limit composites on K-injective strict towers. Rlim is a
functor. Multiply naturality for projection, strict exchange and this inverse
comparison to obtain the displayed equality for arbitrary H, H' and a.
4. For an intrinsically complete H, Koszul reconstruction makes its quotient unit
invertible. Normalized pullback and direct-image evaluations and the ring-sheaf
change adjunction identify U, V and R(e) with the specified four finite arrows.
The intrinsic finite exchange rectangle identifies the evaluated conjugate with
the actual finite ambient mate, retaining coefficient restrictions.
5. At each n separately, finite-level proetale proper base change applies to the
specified bounded-below etale origin. Thus every evaluation of strict exchange is
invertible. Levelwise cohomology and derived isomorphism detection make the strict
exchange invertible. Rlim preserves its inverse; the other two factors are already
invertible. No transition between origins or common lower bound enters this step.
6. Direct image preserves completeness. Strict-tower exchange mate normalization
identifies the actual strict lift with the same conjugate, using the independent
witnesses. The first and last factors of completedBaseChangeMap are the same strict
projection and inverse direct-image/Rlim comparison. The ordered composites agree.
Steps 2 and 3 preceded all completeness and origin restrictions. -/
theorem completedProperIndependentOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f] :
    (∀ (H H' : d.derived X) (a : H ⟶ H'),
      d.completedExchange sq H ≫ (d.push f').map ((d.completedPull g').map a) =
        (d.completedPull g).map ((d.push f).map a) ≫ d.completedExchange sq H') ∧
    (∀ (H : d.derived X) (hH : PbcIsIntrinsicallyComplete X d H)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj H)),
      IsIso (d.completedExchange sq H) ∧
        d.completedExchange sq H = d.completedBaseChangeMap sq H
          (pbcIntrinsicComplete_towerComplete d X H hH) W) := by
  constructor
  · intro H H' a
    let pi : d.push f ⋙ completedReductionTower Y d ≅
        completedReductionTower X d ⋙ d.towerPush f :=
      NatIso.ofComponents (fun K ↦ asIso (d.towerProjection f K))
        (fun {K L} b ↦ (d.towerProjection_properties f K).2.1 L b)
    let P := Functor.isoWhiskerRight pi (d.towerPull g)
    let R := completedRlim Y' (d.completedRing Y')
    let E := Functor.whiskerRight P.hom R ≫
      Functor.whiskerRight (exchangeStrictNatTrans d sq) R ≫
        Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
          (d.directImageRlimIso f').inv
    exact (E.naturality a).symm
  · intro H hH W
    have hTower := pbcIntrinsicComplete_towerComplete d X H hH
    have he (n : ℕ) : IsIso
        ((reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map (d.towerV' sq H)) := by
      obtain ⟨α, _, _, _, hv⟩ :=
        (strictTowerExchangeMateNormalization d sq H hTower W).2.1 n
      have : IsIso
          ((reductionTowerDerivedEvaluation Y'
            (reductionModuleRing Y' (d.completedRing Y')) n).map (d.towerV' sq H) ≫
              (α 3).hom) := by
        rw [hv]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (α 3).hom
    have : IsIso (d.towerV' sq H) := by
      rw [DerivedCategory.isIso_iff]
      intro i
      have (n : ℕᵒᵖ) : IsIso
          (((DerivedCategory.homologyFunctor (d.towers Y') i).map
            (d.towerV' sq H)).app n) := by
        let E := reductionTowerEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n.unop
        have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor _ i).map
            (d.towerV' sq H)) := by
          change IsIso ((DerivedCategory.homologyFunctor _ i).map
            ((reductionTowerDerivedEvaluation Y'
              (reductionModuleRing Y' (d.completedRing Y')) n.unop).map (d.towerV' sq H)))
          have := he n.unop
          infer_instance
        exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i)
          (d.towerV' sq H)).2 inferInstance
      exact NatIso.isIso_of_isIso_app _
    refine ⟨?_, rfl⟩
    unfold AdicCoefficientDatum.completedExchange
    infer_instance

end AlgebraicGeometry.Scheme
