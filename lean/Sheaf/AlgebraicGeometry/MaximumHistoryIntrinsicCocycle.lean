module

public import Sheaf.AlgebraicGeometry.FiniteMaximumLabeledHistory
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal

/-!
# Intrinsic comparison and cocycle for finite maximum histories

Source: ILO, Expose VIII, 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94;
Stacks Project, Tags 02OS, 0806 and 080E
(blueprint: lem-trf-maximum-history-intrinsic-cocycle).

The comparison is on strict transforms. All earlier centers remain recorded, including
centers whose intrinsic blowup is an identity. Every equation is on actual scheme maps.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The next comparison is precisely the map of intrinsic ordinary blowups induced by
its preceding component: identify both strict transforms with those blowups over their
sources, then characterize the induced map by its equation over the preceding component.
This characterization includes uniqueness, rather than choosing an arbitrary lift.
Source: ILO VIII 2.3.11--2.3.13; Stacks Tags 080E and 0806
(blueprint: lem-trf-maximum-history-intrinsic-cocycle). -/
def IsIntrinsicBlowupHistoryComparison {L : Type w} [LinearOrder L]
    {A B : EmbeddedResolutionPair.{u}} {e : A.X ≅ B.X}
    {T : LabeledEmbeddedResolutionTower L A} {U : LabeledEmbeddedResolutionTower L B}
    (c : LabeledEmbeddedResolutionIntrinsicComparison e T U) (l : L) : Prop :=
  ∃ (s : T.intrinsic.obj (op (LowerSet.Iic l)) ≅ (T.centerToIntrinsic l).ker.blowup)
    (t : U.intrinsic.obj (op (LowerSet.Iic l)) ≅ (U.centerToIntrinsic l).ker.blowup),
    s.hom ≫ (T.centerToIntrinsic l).ker.blowupMap =
      T.intrinsic.map (homOfLE (Set.Iio_subset_Iic_self)).op ∧
    t.hom ≫ (U.centerToIntrinsic l).ker.blowupMap =
      U.intrinsic.map (homOfLE (Set.Iio_subset_Iic_self)).op ∧
    ∀ f : (T.centerToIntrinsic l).ker.blowup ⟶ (U.centerToIntrinsic l).ker.blowup,
      f ≫ (U.centerToIntrinsic l).ker.blowupMap =
        (T.centerToIntrinsic l).ker.blowupMap ≫ (c.iso.app (op (LowerSet.Iio l))).hom ↔
      s.hom ≫ f = (c.iso.app (op (LowerSet.Iic l))).hom ≫ t.hom

/-- Finite maximum histories have canonical intrinsic comparisons with invariant, ideal,
ordinary-blowup, identity, cocycle and cartesian smooth-pullback compatibility, on every cut.

Source: ILO VIII 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp. 91--94; conditional
history argument extracted from the ambient-comparison proof; Stacks Tags 02OS, 0806, 080E
(blueprint: lem-trf-maximum-history-intrinsic-cocycle).

Proof:
1. Induct over the given finite maximum extensions. The empty-prefix comparison is the
   given initial isomorphism. Keep every previously recorded ideal in its original order.
2. The intrinsic-values clause of the calculus identifies invariant functions on compared
   admissible prefixes. Their ranges, positive maxima and regularity agree. First-regular
   stopping forces both histories to stop at the same index, including empty schemes.
3. At a nonterminal prefix the centers are reduced full maximum-stratum ideals. The
   intrinsic-ideals clause identifies them by actual ideal extension. Maximum geometry
   supplies coherent ideals. This uses the already compared prefixes, not the next stages.
4. Tag 080E identifies each ambient strict transform with the ordinary blowup of its
   intrinsic center ideal, over its preceding strict transform.
5. Tag 02OS makes the extended center invertible. Tag 0806 lifts the preceding isomorphism
   through the two intrinsic blowups. Lifting its inverse and using uniqueness gives the
   inverse comparison and its transition square. Identity blowups keep their ideals.
6. The finite induction gives equal lengths and labels. Strict progress makes labels
   strictly increase in the reverse positive-value order; no well-foundedness is required.
7. For identities, uniqueness of the lift gives identity components. For composites, both
   the composite lift and the direct lift induce the same canonical quotient of the same
   extended ideal. Uniqueness gives the cocycle, inductively at every stage.
8. Under the identified smooth pullbacks, ideal extension commutes with the cartesian
   initial square. Both next comparisons lift the same map into the same blowup, so Tag
   0806 identifies them. Empty inverse-image centers agree and are deleted on both sides.
   Restriction is the open-immersion case. No relative-dimension restriction is used.
9. At a lower cut take the component after its active labels. Naturality follows by
   composing stage squares; absent labels insert identities. The identity, cocycle and
   pullback equations therefore hold on all cuts, including zero-length histories.
-/
theorem exists_maximum_history_intrinsic_cocycle
    {V : Type w} [LinearOrder V] [OrderBot V] (ν : ResolutionInvariantCalculus.{u} V) :
    ∃ c : ∀ {A B : EmbeddedResolutionPair.{u}}
      (H : FiniteMaximumLabeledHistory ν A) (K : FiniteMaximumLabeledHistory ν B)
      (e : A.X ≅ B.X), LabeledEmbeddedResolutionIntrinsicComparison e H.tower K.tower,
      (∀ {A B : EmbeddedResolutionPair.{u}}
        (H : FiniteMaximumLabeledHistory ν A) (K : FiniteMaximumLabeledHistory ν B)
        (e : A.X ≅ B.X),
        H.length = K.length ∧
        (∀ (D : LowerSet (OrderDual {v : V // v ≠ ⊥}))
          (x : H.tower.intrinsic.obj (op D)),
          H.valueAtCut D x = K.valueAtCut D (((c H K e).iso.app (op D)).hom x)) ∧
        ∀ l ∈ H.tower.labels, IsIntrinsicBlowupHistoryComparison (c H K e) l) ∧
      (∀ {A : EmbeddedResolutionPair.{u}} (H : FiniteMaximumLabeledHistory ν A),
        (c H H (Iso.refl A.X)).iso = Iso.refl H.tower.intrinsic) ∧
      (∀ {A B C : EmbeddedResolutionPair.{u}}
        (H : FiniteMaximumLabeledHistory ν A) (K : FiniteMaximumLabeledHistory ν B)
        (M : FiniteMaximumLabeledHistory ν C) (e : A.X ≅ B.X) (f : B.X ≅ C.X),
        (c H M (e ≪≫ f)).iso = (c H K e).iso ≪≫ (c K M f).iso) ∧
      (∀ {A B A' B' : EmbeddedResolutionPair.{u}}
        (H : FiniteMaximumLabeledHistory ν A) (K : FiniteMaximumLabeledHistory ν B)
        (H' : FiniteMaximumLabeledHistory ν A') (K' : FiniteMaximumLabeledHistory ν B')
        (f : EmbeddedResolutionSmoothMap A' A) (g : EmbeddedResolutionSmoothMap B' B)
        (e : A.X ≅ B.X) (e' : A'.X ≅ B'.X)
        (p : LabeledEmbeddedResolutionPullback f H'.tower H.tower)
        (q : LabeledEmbeddedResolutionPullback g K'.tower K.tower),
        IsPullback e'.hom f.intrinsic g.intrinsic e.hom →
          (c H' K' e').iso.hom ≫ q.intrinsic = p.intrinsic ≫ (c H K e).iso.hom) := by
  sorry

end AlgebraicGeometry
