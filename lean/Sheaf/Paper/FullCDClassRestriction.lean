/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.EssentialImage
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Restriction of the étale-origin coefficient class

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin`,
node `lem-sf-fullcd-class-restriction`; Stacks Project, Tags 094U and 09A5
(blueprint: lem-sf-fullcd-class-restriction).

The witness isomorphism below composes actual canonical inverse-image maps. Membership
itself remains the existential predicate `Functor.essImage`; it carries no chosen witness.
The coefficient field is placed in the larger coefficient universe, independently of the
scheme site's object and morphism universes. There is no finite-type assumption on the
base-changed scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Given any witness `α : ν_X^* G ≅ F`, the restriction isomorphism is
`Q.mapIso α.symm ≪≫ c.symm.app G`, where `Q` is the scheme pro-étale inverse image and
`c` is the canonical comparison of inverse images. This is the node's displayed
isomorphism; no existence choice supplies any of its data.
Source: blueprint `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin`,
node `lem-sf-fullcd-class-restriction`, proof steps 2 and 3; Stacks, Tag 09A5
(blueprint: lem-sf-fullcd-class-restriction). -/
noncomputable def etaleOriginRestrictionWitnessIso
    {Λ : Type (u + 1)} [CommRing Λ] {W X : Scheme.{u}} (q : W ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (α : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G ≅ F) :
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) q).obj F ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} Λ) q).mapIso α.symm ≪≫
    ((comparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) q).app G).symm

/-- The fibre-product projection is weakly étale; inverse image preserves the
étale-origin class. Every witnessing pair gives the displayed isomorphism through
`etaleOriginRestrictionWitnessIso`. For `F = ν_X^* G` and `α = Iso.refl _`, these
particular isomorphisms are natural in every morphism `a : G ⟶ G'`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin`,
node `lem-sf-fullcd-class-restriction`; Stacks, Tags 094U and 09A5
(blueprint: lem-sf-fullcd-class-restriction).

Proof: (1) `def-pc-fibre-product` supplies the scheme `pullback f V.hom`, its two
projections and cartesian universal property. Apply the base-change clause of
`lem-weil-pbc-weakly-etale-composition-base-change` to `V.hom` and `f`. Its projection
is `pullback.fst f V.hom`, which is weakly étale and therefore defines a pro-étale
site object. No finiteness of the pullback scheme is used.
(2) For any étale witness `G`, apply `lem-weil-pbc-comparison-pullback` to that
projection. Its component `c` identifies `ν_W^* (q_et^-1 G)` with `Q (ν_X^* G)`.
(3) The class predicate `def-sf-fullcd-used-class` is exactly existence of `G` and
`α : ν_X^* G ≅ F`. Compose `Q.mapIso α.symm` with `c.symm` as in the definition above.
The inverse is `c ≪≫ Q.mapIso α`. Both inverse identities follow from functoriality
and the inverse identities for `α` and `c`. The inverse of this constructed
isomorphism is the étale-origin witness on `W`, proving the essential-image clause.
For `α = Iso.refl _`, functoriality reduces the construction to `c.symm`; naturality
of that inverse natural isomorphism gives the final equation for every `G`, `G'`,
and `a`. This is exactly the node's three proof steps. -/
lemma etaleOrigin_restriction_to_proetale_base_change
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (Xbar : Scheme.{u})
    [Xbar.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Xbar ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Xbar ↘ Spec (CommRingCat.of D.k))]
    (Y : Scheme.{u}) (f : Xbar ⟶ Y) (V : Y.ProEt)
    (F : Sheaf (Scheme.ProEt.topology Xbar)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))
    (_hF : (comparisonUpperStar
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Xbar).essImage F) :
    IsPullback (pullback.fst f V.hom) (pullback.snd f V.hom) f V.hom ∧
      WeaklyEtale (pullback.fst f V.hom) ∧
      (comparisonUpperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (pullback f V.hom)).essImage
        ((ProEtale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
          (pullback.fst f V.hom)).obj F) ∧
      (∀ (G : Sheaf Xbar.smallEtaleTopology
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))
          (_α : (comparisonUpperStar
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Xbar).obj G ≅ F),
        Nonempty ((ProEtale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
          (pullback.fst f V.hom)).obj F ≅
          (comparisonUpperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
            (pullback f V.hom)).obj
            ((Etale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
              (pullback.fst f V.hom)).obj G))) ∧
      (∀ (G G' : Sheaf Xbar.smallEtaleTopology
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (a : G ⟶ G'),
        (ProEtale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
          (pullback.fst f V.hom)).map
          ((comparisonUpperStar
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Xbar).map a) ≫
          (etaleOriginRestrictionWitnessIso (pullback.fst f V.hom) G' (Iso.refl _)).hom =
        (etaleOriginRestrictionWitnessIso (pullback.fst f V.hom) G (Iso.refl _)).hom ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
            (pullback f V.hom)).map
            ((Etale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
              (pullback.fst f V.hom)).map a)) := by
  refine ⟨IsPullback.of_hasPullback f V.hom, inferInstance, ?_, ?_, ?_⟩
  · obtain ⟨G, ⟨α⟩⟩ := _hF
    exact ⟨(Etale.upperStar _ (pullback.fst f V.hom)).obj G,
      ⟨(etaleOriginRestrictionWitnessIso (pullback.fst f V.hom) G α).symm⟩⟩
  · intro G α
    exact ⟨etaleOriginRestrictionWitnessIso (pullback.fst f V.hom) G α⟩
  · intro G G' a
    simpa [etaleOriginRestrictionWitnessIso, Functor.comp_map,
      etaleComparisonPullback, comparisonCoefficientPullback, proEtaleComparisonPullback,
      Etale.upperStar, ProEtale.upperStar, comparisonUpperStar, Scheme.smallEtaleTopology] using
      (comparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (pullback.fst f V.hom)).inv.naturality a

end AlgebraicGeometry.ProEtale
