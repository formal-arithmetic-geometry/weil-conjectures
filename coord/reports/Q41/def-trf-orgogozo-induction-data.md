# Stage-1 worker report: def-trf-orgogozo-induction-data

## Files written

- `dag/nodes/sec-trace-formula/def-trf-orgogozo-induction-data.json`: existing definition, marked `split`; no new nodes.
- `citations.json`: empty, because a definition has no proof steps.

## Attachments

No sorry-free project declaration states this item exactly. The source searches found no declaration for the Orgogozo induction-data definition.

## WANTED

WANTED: local archival copy of `literature/orgogozo-modifications-cycles-proches.pdf`, §§1, 3.1, 3.3 (author PDF URL is retained in the node); the imported node's source identifies the universal truncated comparison and the modification/alteration terminology there.

## What was checked

The item is a definition rather than a proposition. Its statement introduces the finite commutative coefficient ring, the morphism and bounded derived object, then defines the universally quantified truncated comparison property (P_r(f,K)), modification, alteration, semistable tower datum, almost plurinodal datum, and excellence. The statement dependencies are exactly the existing nodes for oriented nearby cycles, proper morphisms, excellence, flat morphisms, finite integral morphisms, closed immersions, and smooth morphisms. I searched the DAG and blueprint for duplicate definitions and found no node stating this combined construction; the existing dependency nodes provide the notions used by the definition, so adding clause nodes would only restate parts of the item.

I read the imported node, its source metadata, the nearest blueprint ancestor `lem-trf-local-term-locality`, and each of the seven dependency statements. In particular, `def-trf-oriented-nearby-cycles` supplies the ordinary comparison and vanishing-topos language; `def-weil-proper-morphism`, `def-weil-flat-morphism`, `def-weil-finite-integral-morphism`, `def-weil-closed-immersion`, and `def-sbc-smooth-morphisms` supply the named morphism notions; and `def-exc-excellent-ring` supplies excellence. No proof step is required for a definition, so `proof` and `proof_deps` remain empty and `citations.json` is empty. I checked edge cases in the definitions (identity modification/tower, empty or zero coefficient ring, and arbitrary preliminary base changes) and found no statement change needed. The existing Mathlib searches for this item were read; their hits concern generic scheme properties and do not state this nearby-cycle/alteration definition.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to record.

## Review by Q41

I independently reread the full item statement and all seven statement dependencies named in `stmt_deps`. Each dependency says the exact interface used: oriented nearby cycles supplies the comparison map, proper morphism supplies “proper,” excellence supplies excellent coordinate rings, flat morphism supplies proper flat tower factors, finite integral morphism supplies “finite over its base,” closed immersion supplies the selected closed subschemes, and smooth morphism supplies smooth complements. The remaining words in the item are introduced as definition data (finite ring, derived category object, cone and cohomology, dense opens, surjectivity, irreducible components, geometric fibres, ordinary double points, completed local rings, finite disjoint unions, and nowhere-dense images), so no hidden theorem or uncited proof step is present. I checked that (P_r) quantifies over both (T\to S) and (T'\to T), that the modification requires density of the inverse image of the isomorphism open, and that the semistable datum permits the identity tower. I also searched the whole DAG and blueprint for duplicate Orgogozo/induction-data definitions and searched the source checkout for an exact declaration; none exists. The item remains unchanged except for the stage-1 `split_report` and `status: split` fields.
