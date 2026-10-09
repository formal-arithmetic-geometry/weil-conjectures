# def-weil-pbc-generating-sections

## Worker report

- Files written: `dag/nodes/sec-proper-base-change/def-weil-pbc-generating-sections.json` (definition, split; no exact Mathlib match). No new nodes or unit records were needed.
- Attachments: none. The node's `lean_audit` records no Lean declaration on either source branch.
- WANTED: none. The definition cites Stacks Project Modules, Tag 01AM, and Sheaves, Tag 007U.
- The imported definition needed an explicit finite free-sheaf map and its local surjectivity condition. The statement now includes both, and uses only `def-pc-scheme` as a statement dependency. The recorded LeanSearch, Loogle and Mathlib source searches find `SheafOfModules.GeneratingSections` as a near match, but no declaration states this local-surjectivity formulation directly.
- Unfinished work: none for this one-level stage-1 split. The equivalence between the categorical epimorphism formulation and local surjectivity belongs to later formalization.

## Review by C

I checked the definition against the cited Stacks descriptions: the displayed map is induced by the finite family of global sections, and surjectivity of a sheaf map has the stated local lifting meaning. The statement does not assert that sections over every open are generated without passing to a cover. Its one statement dependency is the scheme notion; a definition requires no proof steps. The item is not the unit's key node, so `realized` is unchanged.

I reviewed all three recorded Mathlib search kinds and the candidate's description. `SheafOfModules.GeneratingSections` uses an epimorphism in the category of sheaves of modules; identifying that with the stated local condition requires a separate result, so retaining this node as `split` with `mathlib_match: null` follows the stage-1 convention. I corrected no additional node content and rejected no part of the worker's split.
