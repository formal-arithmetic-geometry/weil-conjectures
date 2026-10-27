# WeilConjectures.sfCompletedCompositionTransport

## Reason

The component theorem needs local proper/open comparisons on finite-type schemes
whose structure maps are not assumed separated. The existing
PurCompactSupport.refinementProperOpen_existsUnique has separated structure-map
binders. The abstract strict-tower calculus and compactification coherence do not
identify the actual completed maps appearing in the component predicate.

Add three strictly lower obligations and assemble the original component statement
from them. The new transport definition is an explicit composite with every factor
supplied as an argument. It chooses no witness and contains no proof hole.

## Old

The four declarations below did not exist. The statement and definition exported by
Sheaf.Paper.FieldShriekCompositionIntegralComponent are preserved verbatim.

## New

- WeilConjectures.sfQcqsCompletedRefinement_exists, in
  Sheaf.Paper.QcqsCompletedRefinement: existence of an adjunction-normalized comparison
  for one proper refinement and one integral constructible input.
- WeilConjectures.sfCompletedCompositionOnTower_isIso, in
  Sheaf.Paper.CompletedCompositionTowerIsIso: open-unit and Lambda invertibility and
  invertibility of the prescribed completed map on one compatible tower.
- WeilConjectures.sfCompletedCompositionTransport, in
  Sheaf.Paper.CompletedCompositionTowerIndependence: the explicit completed arrow
  (image cg).map rho_f.inv followed by rho_g.inv, the tower map, and rho_fg.hom.
- WeilConjectures.sfCompletedCompositionTransport_independent, in the same module:
  equality of two such constructed arrows, conditional on the local data and the
  three normalized refinement equations on each tower.

The exact signatures are in the new Lean modules and their matching DAG records.
Each new theorem has its whole proof postponed with a named, sourced DAG obligation;
the transport definition has its complete implementation. No existing signature,
instance, attribute, definition body or public import changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldShriekCompositionIntegralComponent | S5 | Uses all four new declarations through private proof imports; complete assembly proof. |

There are no adaptations of other existing modules. Consumers of the component
retain its exact previous signature and normalization predicate.

## Status

landed 20261027T180808-L-3902903 2026-10-27 (merge of deliver/S5/Sheaf.Paper.FieldShriekCompositionIntegralComponent)
