# Worker report: def-sfb-derived-extend-subfield

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-derived-extend-subfield.json`: the imported definition, marked split; no new nodes and no Mathlib leaves.
- `citations.json`: `[]`, because the definition has no proof steps.
- `report.md`: this report.

## Attachments

No attachment. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `derivedExtendScalarsSubfield`, the blueprint tag, and the coefficient/derived-extension terminology; no sorry-free project declaration states this item. The upstream master declaration was read only as reference and is not treated as a finished proof.

## WANTED:

None.

## What was wrong or corrected

The imported node was a definition with the correct two statement dependencies and no proof to split. Its `blueprint.same_as` was `null`; whole-blueprint search found no alternate node stating the same definition, so I changed it to `[]`, as required for a completed split. I set `status` to `split` and kept the statement and dependency lists unchanged. No source error or statement dispute was found. No new node was introduced: creating a node for the specialization would merely restate the item or one of its dependencies (delivery-errors D1/D2).

## What I could not finish

Nothing remains for this stage-1 split. Lean source writing and compilation were forbidden by the run instructions, so none was attempted.

## Review by Q70

I read `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-subfield.md` and the surrounding two-colimit section. The source defines, for a prime `ell`, scheme `X`, and finite extensions `E ≤ F`, exactly the functor `F_X ⊗ᴸ_{E_X} - = L(Ext_{E_X → F_X})` from `D(Mod_{E_X})` to `D(Mod_{F_X})`. I opened `sk-def-sfb-derived-extension-of-scalars`: its statement defines `S ⊗ᴸ_R - = L(Ext_phi)` between the corresponding module-object derived categories. I also opened `def-sfb-subfield-coefficient-map`: it supplies the coefficient morphism `E_X → F_X`. Therefore the item is a direct specialization of those statements, with every notion in the item covered by its two `stmt_deps`; there are no proof steps and hence no node citations or quotation entries.

I checked the source checkout for the exact blueprint tag and declaration name and found no declaration, including the upstream-master reference declaration. I searched the whole DAG and blueprint for the displayed notation and `derivedExtendScalarsSubfield`; the only occurrence is this item and downstream uses, so `same_as` is empty. I ran and read LeanFinder, LeanSearch, Loogle (two phrasings), and Mathlib grep (two directories and two regex phrasings). LeanSearch found only the general underived `ModuleCat.extendScalars`; no Mathlib declaration states this sheaf-level derived functor. These searches are recorded in the node and in `searches.jsonl`.

For the definition-specific checks, I verified that `E_X` and `F_X` are the pulled-back coefficient ring objects supplied by the coefficient-map dependency, and that the source's `D(Mod_{E_X})`/`D(Mod_{F_X})` categories match the derived-extension dependency's source and target. I checked the boundary cases conceptually: when `E = F`, the coefficient map is the identity and the construction is the identity-derived extension; for any scheme `X`, the formula remains well typed; no constructibility or boundedness hypothesis is silently added. Because there are no proof steps, `citations.json` is correctly empty and C1/C4 proof-citation checks are vacuous. No SGA source, Lean edit, compiler, Lake build, or live-project write was made.

## Not duplicates

No new nodes were created, so no duplicate pairs arise. The existing `def-sfb-derived-extend-to-qlbar` is the analogous extension to `Q̄_ell`, but has a different coefficient target and is not the same statement; it remains a dependency-free neighboring definition.

## Second reading by Q70

- Item statement: checked against `def-sfb-derived-extend-subfield.md` (blueprint order 1758), clause by clause; verdict: exact specialization for a prime `ell`, scheme `X`, and finite extensions `E ≤ F`, with the displayed functor and source/target derived categories.
- Statement dependency `sk-def-sfb-derived-extension-of-scalars`: opened its statement in `dag/nodes/sec-proetale-coefficients`; verdict: it supplies precisely the general `L(Ext_phi)` construction and its domain/codomain used by the item.
- Statement dependency `def-sfb-subfield-coefficient-map`: opened its statement in `dag/nodes/sec-proetale-coefficients`; verdict: it supplies precisely the coefficient morphism `E_X → F_X` used for the specialization.
- Proof steps: there are none for this definition; `citations.json` is therefore correctly empty and no uncited proof fact is present.
- New nodes: none; no B1–B7 review or duplicate removal is applicable, and no Mathlib leaf is claimed.
- Edge cases: `E = F` gives the identity coefficient map and identity derived extension; the construction remains typed for the empty scheme and for arbitrary schemes, and no extra constructibility, boundedness, or characteristic hypothesis is introduced.
- Blueprint audit: whole-blueprint search found no alternate node stating this definition, so `blueprint.same_as = []`; the split report identifies the exact definition sentence realized.
- Changes made in this second reading: appended this audit only; no mathematical or node-field correction was needed.
