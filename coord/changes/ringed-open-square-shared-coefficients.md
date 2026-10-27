# Actual-ring open-square construction

## Reason

The unit-normalization lemma and its consumer must use the same `actualSquare`
constant. Converting a separately expanded coefficient record caused repeated
Lean kernel deterministic timeouts. Move the existing public declarations below
verbatim to `Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization`, with the
private helpers needed by the coherence proof. The item publicly imports it.
The item's identity-coherence proof retains its existing private identity helpers.

## Old

In `Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`:

```lean
/-- The canonical chosen fibre-product square. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def cartesian {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T) :
    ChosenCartesianSquare (pullback.fst p h) (pullback.snd p h) p h where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The specified actual inverse-image ring comparisons are coherent. Source: Stacks 03CB.
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: conjugate the projection-preserving fibre-product comparison under the ring-sheaf
adjunctions. The definition of coefficientIso is exactly this conjugate. The two
composite units consequently agree, so the composite coefficient isomorphisms agree.
This is step 1 of the node's proof and uses site-morphism-composition. -/
theorem actualCoefficients_coherent {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HEq
      (proEtaleRingCompositeCoefficients (pullback.fst p h) p R
        (ProEtaleOpenRestriction.RX p R) (ProEtaleOpenRestriction.RXW p h R)
        (Iso.refl _) (Iso.refl _))
      (proEtaleRingCompositeCoefficients (pullback.snd p h) h R
        (ProEtaleOpenRestriction.RW h R) (ProEtaleOpenRestriction.RXW p h R)
        (Iso.refl _) (ProEtaleOpenRestriction.coefficientIso p h R)) := by
  have hl := ringComposite_heq (pullback.fst p h) p (pullback.fst p h ≫ p) rfl R
    (ProEtaleOpenRestriction.RX p R) (ProEtaleOpenRestriction.RXW p h R)
    (Iso.refl _) (Iso.refl _)
  have hr := ringComposite_heq (pullback.snd p h) h (pullback.fst p h ≫ p)
    (pullback.condition (f := p) (g := h)) R
    (ProEtaleOpenRestriction.RW h R) (ProEtaleOpenRestriction.RXW p h R)
    (Iso.refl _) (ProEtaleOpenRestriction.coefficientIso p h R)
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  apply Iso.ext
  simp [ProEtaleOpenRestriction.coefficientIso, ringSquare_eq]

/-- The square over R with precisely p⁻¹R, h⁻¹R and h'⁻¹p⁻¹R as coefficients.
Source: Stacks 09A5 and 03CB
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def actualSquare {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    StrictTowerRingedSquare (cartesian p h) where
  RY := R
  RX := ProEtaleOpenRestriction.RX p R
  RY' := ProEtaleOpenRestriction.RW h R
  RX' := ProEtaleOpenRestriction.RXW p h R
  cf := Iso.refl _
  cg := Iso.refl _
  cg' := Iso.refl _
  cf' := ProEtaleOpenRestriction.coefficientIso p h R
  coherent := actualCoefficients_coherent p h R
```

## New

The exact same public declarations, signatures, docstrings, definitions and proofs
are in `Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization`, under the same
namespace and universe. The item re-exports them through a public import.
There is no change to the coefficient rings, comparisons, coherence proposition,
chosen Cartesian square or downstream meaning of any definition.
The new module also states the smaller unit-normalization theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent | G3 | Re-exports the unchanged declarations; its new proof uses the normalization theorem. |
| Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization | new in G3 | Holds the unchanged construction and the new normalization statement. |

A direct-import scan of the shared `lean/` tree found no importers of the item.
No other existing module is edited. Existing target statements and the meanings
of their definitions are unchanged.

## Status

landed 20261027T034649-L-3672011 2026-10-27 (merge of deliver/G3/Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent)
