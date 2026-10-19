## Files written

- `dag/nodes/sec-trace-formula/def-trf-coherent-topos.json`: completed the one-level split of the definition by marking it `split`; the four existing statement dependencies already supply all notions in the statement. No new nodes or Mathlib leaves.
- `citations.json`: empty list, because a definition has no proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the exact blueprint tag, the declaration names, and the coherent-topos terminology. No sorry-free project declaration states this full definition. The occurrences of “coherent” in the source concern coherent isomorphisms or quasi-coherent modules and are not this item.

## WANTED:

- A local archival copy of Orgogozo, *Modifications et cycles proches sur une base générale*, §8.1, printed pp. 17–18, for the finiteness terminology used by this definition. I read the author’s PDF online at the URL in the node; it is not present in `literature/`.

## What was wrong and what changed

The imported node was unsplit and carried inherited metadata from an unrelated constructibility-descent dispatch: its `created.item` and `unit` identify `lem-trf-psi-constructibility-descent`/`sk-i-curve-zero`, while this item is the coherent-topos definition. I preserved those maintainer-owned fields and recorded the mismatch for maintenance; the statement and dependency list are mathematically appropriate for the item. I added only the stage-1 `split_report` and set `status` to `split`. No statement, hypothesis, clause, dependency, or source citation was changed. The current blueprint search finds no separate blueprint node stating this definition, so no child node was created.

## Not duplicates

No new node was created. The existing nodes `def-weil-pbc-topos`, `def-weil-pbc-sites-and-cohomology`, and `def-trf-geometric-morphism` provide the underlying site/topos, sheaf, size, and geometric-morphism notions; each is a prerequisite used in the item’s statement, not a duplicate of the coherent-object/coherent-topos definition.

## Review by Q46

I read the item, `sec-trace-formula`, and the assigned unit `sk-i-curve-zero`, then opened all four statement dependencies in full. `def-weil-pbc-topos` supplies a category of sheaves of sets on a small site in the chosen universe; `def-weil-pbc-sites-and-cohomology` supplies the site and sheaf language; `def-weil-size-convention` supplies the containing universes and small-skeleton convention; and `def-trf-geometric-morphism` supplies an adjunction with finite-limit-preserving inverse image. These statements say exactly what the item takes from them. Since the item is a definition, there are no proof steps, `proof_deps`, or citation quotations.

I compared the coherent terminology with Orgogozo §8.1 (PDF pp. 17–18). The source describes coherent schemes, constructs the defining site of triples, states that the resulting topos is coherent, and identifies coherent objects with quasi-compact and quasi-separated objects; the item records the standard object-level definitions, the finite-limit generating-subcategory condition for a coherent topos, and the coherent/conservative conditions on a geometric morphism. The universe and sheaf-category clauses agree with the existing topos and size definitions. I tested edge cases at the definitional level: the terminal object is included among finite-limit generators, an empty indexing family cannot be an epimorphic coproduct unless the target is initial, and conservativity is exactly reflection of isomorphisms by the inverse-image functor.

For Mathlib, I reused and read the existing recorded searches (grep, Loogle, LeanFinder, and LeanSearch). The grep hits in `CategoryTheory/Sites/Coherent/SequentialLimit.lean` and `Equivalence.lean` concern the coherent topology on a preregular category, not coherent objects or coherent geometric morphisms. Loogle and LeanSearch returned quasicoherent-module APIs, and LeanFinder returned coherent-topology/condensed APIs; none states this definition. Thus `mathlib_match` remains null. The required sandbox `check_dag` preflight passed with no finding.
