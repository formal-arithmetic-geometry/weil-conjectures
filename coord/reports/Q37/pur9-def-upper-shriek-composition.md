# Stage-1 report: pur9-def-upper-shriek-composition

## Files written

- `dag/nodes/sec-smooth-purity/pur9-def-upper-shriek-composition.json`: item, split; no new nodes and therefore no Mathlib leaves.
- `citations.json`: empty because this is a definition with no proof steps.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, blueprint tag, and upper-shriek composition terminology; no sorry-free project declaration states this definition.

## WANTED

None.

## What was checked

The imported item and its source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/pur9-def-upper-shriek-composition.md` were read together with the `sk-prop-sp-composition` unit and the current chapter. The source is a definition, so there are no proof steps to split. The stale references `pur9-input-ambient-composition`, `pur9-def-standing-choices`, and `pur9-def-shriek-notation` do not occur as nodes in the current DAG or as definitions in either blueprint snapshot. I replaced them by existing statements that supply the same interfaces: `thm-sf-comp-composition` gives the natural compact-support map `alpha_{g,f}`; `def-pur-conventions` fixes the field, coefficient, schemes and standing adjunction; `def-weil-pbc-composite-adjunction` gives the composite adjunction and its counit; `def-compact-support-direct-image-detailed` and `pur713-def-upper-shriek` define the two functor families; and `def-weil-pbc-proetale-site` defines the displayed derived categories. The defining mate and the counit-normalized composite are unchanged in content.

I checked each dependency statement directly. The compact-support theorem has exactly the morphism `alpha_{g,f}: Rg_! Rf_! -> R(gf)_!`; the composite-adjunction definition states the Hom-bijection and counit formula; the compact-support and exceptional-inverse-image definitions provide the functors with the finite coefficient ring; and the conventions node supplies the finite-field and coefficient hypotheses and the standing counit. Identity maps, `L=0`, `n=1`, and `f` or `g` an identity are well-typed edge cases. The resulting statement is self-contained at the level required for this definition and has no proof dependencies or cycles. The Mathlib searches run during the audit returned only generic adjunction/pushforward declarations, so no Mathlib leaf is claimed.

## Review by Q37

I reread the item, its blueprint source, the unit record, and every cited statement. The item is a pure definition: it introduces the mate (c_{g,f,L}) from the specified composite (Rg_!Rf_!R(gf)^!L\to L), and its source does not assert a theorem or require proof steps. The current DAG has no nodes for the three old pur9 aliases, so I verified that the replacements are semantically exact rather than inventing nodes. In particular, `thm-sf-comp-composition` supplies the same `alpha_{g,f}` direction and domain, while `def-weil-pbc-composite-adjunction` supplies the right adjoint (Rf^!Rg^!) and the composite counit. The two functor definitions and the pro-etale-site definition cover all remaining notation. I checked finite coefficient (A=\\mathcal O_E/\\varpi_E^n), separated finite-type (k)-morphisms, and the category of (L) against those statements. No non-elementary proof fact is used, so `citations.json` is correctly empty; no new node, duplicate, or Mathlib leaf is needed.

Nothing remains unfinished in the stage-1 split.
