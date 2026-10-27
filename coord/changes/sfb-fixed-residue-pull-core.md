# AlgebraicGeometry.Scheme.sfbFixedResiduePull

## Reason

The fixed residue pullback data is moved into a small core module so the two
strictly smaller comparison obligations can import it without an import cycle.
The original public name remains available as an abbreviation in the item module.

## Old

def sfbFixedResiduePull {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k)

## New

abbrev sfbFixedResiduePull {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k) :=
  SfbResidueComparisonCore.sfbFixedResiduePull i k

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicImmersionCompletedTransport | F8 | The existing import continues to use the unchanged public abbreviation. |
| Sheaf.Paper.AdicImmersionResidueComparison | X9 | The theorem target uses the abbreviation and the core implementation. |

## Status

landed 20261026T071516-L-3943000 2026-10-26 (merge of deliver/X9/Sheaf.Paper.AdicImmersionResidueComparison)
