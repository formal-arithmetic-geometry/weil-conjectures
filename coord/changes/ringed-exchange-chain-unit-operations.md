# Ringed restriction exchange shared operations

## Reason

Move the existing nine declarations below into `Sheaf.AlgebraicGeometry.RingedExchangeChainUnit`
verbatim, retaining their namespace, signatures, docstrings, bodies and visibility. The original
module publicly imports the lower module. This gives the split cochain-unit statement access to
the same declaration names as its consumer and prevents the Lean kernel from repeatedly
converting expanded ringed module operations. The comparison attempt completed elaboration but
hit a kernel deterministic timeout; using identical names removes that conversion.

## Old

In `Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`:

```lean
/-- The source vertical inverse image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev verticalPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f r.RY r.RX r.cf

/-- The source vertical direct image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev verticalPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f r.RY r.RX r.cf

/-- The base inverse image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev basePull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g r.RY r.RY' r.cg

/-- The inverse image on the upper side of the square. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev upperPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback g' r.RX r.RX' r.cg'

/-- The target vertical inverse image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev targetPull (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModulePullback f' r.RY' r.RX' r.cf'

/-- The target vertical direct image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev targetPush (r : StrictTowerRingedSquare sq) :=
  proEtaleRingModuleDirectImage f' r.RY' r.RX' r.cf'

/-- The ordinary counit mate, prior to deriving. Source: Stacks 09T5 and 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def ordinary (r : StrictTowerRingedSquare sq) :
    verticalPush r ⋙ basePull r ⟶ upperPull r ⋙ targetPush r :=
  (mateEquiv (proEtaleRingModuleAdjunction f r.RY r.RX r.cf)
    (proEtaleRingModuleAdjunction f' r.RY' r.RX' r.cf')
    (TwoSquare.mk _ _ _ _ r.exchangeModuleSquare.hom)).natTrans

/-- The derived counit mate for the ordinary-derived adjunctions. Source: Stacks 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev exchange (r : StrictTowerRingedSquare sq) :
    (verticalPush r).rightDerivedFunctor ⋙ (basePull r).mapDerivedCategory ⟶
      (upperPull r).mapDerivedCategory ⋙ (targetPush r).rightDerivedFunctor :=
  proEtaleAmbientRingedExchange sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

/-- The comparison Q(FK) → RF(QK) for any additive direct image.
Source: Stacks 070K (blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def chainComparison [Abelian.HasKInjectiveResolutions C] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app K)
```

## New

The exact declarations above, with the same section universe binders, are in
`Sheaf.AlgebraicGeometry.RingedExchangeChainUnit`. The original module adds
`public import Sheaf.AlgebraicGeometry.RingedExchangeChainUnit` and removes those local
copies. There is no mathematical or definitional change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent | G8 | Receives the identical declarations through the public import; new proofs use the split theorem. |
| Sheaf.AlgebraicGeometry.RingedExchangeChainUnit | new in G8 | Defines the shared operations and states their cochain-unit normalization. |

The downstream script reports zero downstream modules of the item. Its name-based scan finds
only the item as a consumer of `chainComparison`. No consumer signature needs adaptation.
The moved definitions retain exactly the same meanings in the targets.

## Status

landed 20261025T162514-L-465568 2026-10-25 (merge of deliver/G8/Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent)
