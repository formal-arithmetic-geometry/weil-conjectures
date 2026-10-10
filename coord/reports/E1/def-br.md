# Worker report: def-br

## Files written

- `dag/nodes/sec-curve-estimates/def-br.json`: split the definition and named its existing etale-descent input.
- `dag/units/sk-def-br.json`: recorded `def-br` as the realization of the unit's definition sentence; this unit has no proof steps.
- `coord/reports/E1/def-br.md`: this report. No new nodes were created.

## Attachments

- `AlgebraicGeometry.Scheme.CohomologicalBrauerGroup` belongs to `def-br` (`WeilConjectures/AlgebraicGeometry/Sites/Gm.lean:139-147`), **has sorry transitively** according to the node's slopmaster2 audit. Its own abbreviation has no sorry, but its sheaf input depends on `AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf` (`Gm.lean:87-93`), which is open in that audit. This is an exact statement match, not a closed attachment.
- The open structure-presheaf theorem is the instance `\mathcal F=\mathcal O_X` of the existing general node `lem-sc-etale-qcoherent-descent`. It is a specialization, not an exact declaration attachment to that general node. I cited that node rather than creating a duplicate special-case node.

## Wanted sources

None.

## Findings and changes

The master blueprint's `def-br.md` (order 890) and `sk-def-br/_section.md` say exactly that `\operatorname{Br}(C)=H^2(C_{\mathrm{\acute et}},\mathbb G_m)` for its curves. The Lean abbreviation defines `Sheaf.H X.gmSheaf 2` for any scheme `X`, so it specializes to every curve, including empty and disconnected curves; its broader domain does not alter the claimed definition. I retained the curve, units-sheaf, and small-etale-site dependencies and added `lem-sc-etale-qcoherent-descent` to expose the input that the structure presheaf is a sheaf. For `\mathcal F=\mathcal O_X`, the existing node states that `U\mapsto\Gamma(U,u^*\mathcal O_X)=\Gamma(U,\mathcal O_U)` is a sheaf. The Lean source also uses that the units functor preserves the sheaf condition; `def-sc-gm-torsor` already names `\mathbb G_m` as that sheaf.

The existing `lean_audit.slopmaster2` is `rests_on_sorry`; it must not be reclassified as closed from the one-line body alone. No statement or blueprint error was found. A search of the whole blueprint with `tools/blueprint_refs.py search 'Brauer group'` and `search 'H^2(C'` found no duplicate definition.

## Unfinished work

The transitive sorry behind the attached Lean abbreviation remains for the maintainer to verify against its sorry map; the DAG's descent node is still unsplit.

## Review by E1

I read the sk-def-br unit's definition sentence and the def-br node: both define Br(C) as degree-two cohomology of G_m on the small etale site for C as in def-sc-curves. This agrees with the Lean `CohomologicalBrauerGroup` abbreviation in Gm.lean:139-147, which specializes from schemes to these curves. The node's citations to def-sc-curves, def-sc-gm-torsor and def-weil-pbc-etale-site introduce precisely the curve, units sheaf and site occurring in the formula. The added lem-sc-etale-qcoherent-descent states the sheaf property of U |-> Gamma(U,u*F); at F=O_X it gives the structure-presheaf input at Gm.lean:87-94. The source's units construction then gives G_m. I checked the empty and disconnected curve cases: the cohomology expression remains defined, and no connectedness is silently assumed.

There is no proof split or new node to test under B1-B9, C or D; the only item change is an existing statement dependency, and the unit realization names this exact item. The Lean abbreviation's body has no sorry, but its structure-presheaf input is open in the committed audit, so B10 does not permit closure. The worker made no mathematical change to the definition and I found no A-E defect to send back.
