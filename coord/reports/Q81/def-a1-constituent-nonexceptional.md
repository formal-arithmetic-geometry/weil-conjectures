# Stage-1 worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/def-a1-constituent-nonexceptional.json`: item, split as a definition; its statement follows the current main-20261015 blueprint update and retains `def-wf-fundamental-representation` and `def-fd-artin-schreier-sheaf` as statement dependencies.
- `citations.json`: empty, because a definition has no proof steps.
- `report.md`: this report. No Lean, compiler, Lake, live-project, or launcher file was written.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, blueprint tag, `IsNonexceptional`, `HasLinearArtinSchreierConstituent`, and nonexceptional terminology. The source declaration `AlgebraicGeometry.WeilSheaf.IsNonexceptional` is at `WeilConjectures/DeligneLaumon/AffineLine/MiddleExtension.lean:68`; its body is a one-line predicate over `HasLinearArtinSchreierConstituent`, but the audit is `rests_on_sorry` through `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` (lines 405–415 of `SixFunctors/ProEtale/Adic/LowerStar.lean`). It therefore is not an attachable finished declaration. The source declaration also does not itself state the imported constituent/Jordan–Hölder wording as a sorry-free completed notion.

## Literature wanted

WANTED: none. The definition is supplied by the current blueprint and the source module; no proof document is needed for a definition.

## Corrections and limitations

The imported node's old statement required `\\mathcal M` to be nonzero and irreducible. The current blueprint snapshot `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-middle/def-a1-constituent-nonexceptional.md` explicitly changes this to a lisse Weil sheaf with no irreducibility hypothesis, while retaining the geometric constituent and all-`a\\in k` exclusion clauses. I applied that stated blueprint update and recorded it in the split. This is a source/blueprint update, not a weakening introduced to obtain a proof. The current source definition likewise quantifies over arbitrary `WeilSheaf` `F`, confirming that the irreducibility hypothesis does not belong in this definition.

I found no duplicate DAG node for this definition: the whole-DAG search by the id, `constituent`, `nonexceptional`, and `HasLinearArtinSchreierConstituent` found only this imported item and the separate comparison/concentration lemmas. The whole-blueprint search with `python3 tools/blueprint_refs.py search 'constituent'` found this definition and downstream results, but no alternate definition to cite. The existing statement dependencies are exactly the two notions used in the statement; no new node restates a clause of the item.

No new node was created, so there are no Mathlib leaf decisions or new Mathlib-search records. The item's own Lean audit is not `none`, so the item-level Mathlib search requirement for a none-audit item does not apply. The unrelated open theorem in the audit is not used by this definition and is not added as a fake statement dependency.

## Review by Q81

I read the current item node, `dag/chapters/sec-deligne-laumon-a1.json`, and `dag/units/sk-p-dl-a1-middle.json`. The unit describes the nonexceptional definition as the first input to the middle-extension proposition; this item is not the unit key node, so no unit `realized` fields are changed. I read both the old source node and its `blueprint_update`, then read the current blueprint definition file. The resulting statement introduces `j`, `U_0`, `A_0`, the base-changed open `U`, the geometric generic representation and its stalk `V`, defines constituents as Jordan–Hölder constituents, and excludes exactly the restrictions `\\mathcal L_{\\psi(ax)}|_U` for every `a\\in k`, including the trivial `a=0` case. It has the two existing statement dependencies that supply the representation and Artin–Schreier sheaf notions.

Because this is a definition, there are no proof steps, no non-elementary citations, and therefore no citation quotes; `citations.json` is correctly `[]`. I checked the two cited node statements directly: `def-wf-fundamental-representation` defines the geometric representation on the stalk of a lisse Weil sheaf after base change, and `def-fd-artin-schreier-sheaf` defines the Artin–Schreier sheaf and the notation `\\mathcal L_{\\psi(ax)}`. Neither cited node is being used to supply a theorem about nonexceptionality. The old irreducibility and nonzero assumptions were removed only because the current blueprint update removes them; no other hypothesis or exclusion clause was changed.

I inspected the source declaration and the audit's open list. The declaration has no local `sorry`, but its audit is `rests_on_sorry` via the unrelated finite lower-star theorem; hence I did not attach it. The source's current predicate is defined for any `WeilSheaf`, which is consistent with the updated statement. Small edge cases are covered by the definition: a zero sheaf has no constituents and therefore satisfies the universal exclusion vacuously; `a=0` is explicitly included and denotes the trivial rank-one sheaf; and a lisse sheaf with several Jordan–Hölder factors is tested constituent by constituent. No proof step hides a lemma, no new node duplicates an existing one, and no cycle is introduced.

The item is marked `split`, with `blueprint.same_as=[]` and a `split_report` identifying the current definition paragraph. No source error remains for this definition after applying the documented blueprint update.
