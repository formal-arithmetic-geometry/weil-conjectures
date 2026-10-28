## What changed

Added the proof-only module `Sheaf.Paper.EtaleLocalIsoCoverFromProEtaleSection` with a named
local-cover substep, and imported it privately from the item. The item theorem is now proved by
applying the local-cover substep and lifting the given separably closed geometric point through
its étale cover with `Scheme.Cover.exists_comp_eq_of_isSepClosed`.

## Proved and sorry left

The item theorem `AlgebraicGeometry.Scheme.exists_etale_local_representative_of_proetale_local_iso_sections`
is proved. One strictly simpler theorem remains split off:
`AlgebraicGeometry.Scheme.exists_etale_iso_cover_of_proetale_local_iso_section`, in node
`new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover`.

## No longer needed

The item no longer imports `Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom` or
`Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison` directly; those proof-only imports are
owned by the split local-cover module. The direct proof route uses that new node and the existing
source-library declaration `Scheme.Cover.exists_comp_eq_of_isSepClosed`.

## Where the brief, the DAG or earlier work was wrong

The original node omitted the local-cover theorem needed to formalize the sheafification and
common-refinement argument. That argument is now recorded as a separate, strictly simpler node.

## New nodes

`new-lem-weil-pbc-lisse-finite-level-etale-local-representative-cover`: a pro-étale local Isom
section is represented by actual derived isomorphisms on an étale cover. Source: Stacks
proetale.tex, Tags 09BV and 00WJ. Searches found only generic sheafification and point-fibre
APIs, so the local-cover statement is split off for parallel proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleLocalIsoCoverFromProEtaleSection": "aa3ac6274820d9e14de73a2acd587ae01ba4ede3", "Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative": "309cce6272b57890ca17d05761d17e36b6e35760"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms": {"hash": "f8674c4dc52da453ee46e36207bde58015c17f03", "status": "OK"}}, "seconds": 11, "time": "2026-10-28T11:01:40+0800", "transitive": 0, "version": 1}
```

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
