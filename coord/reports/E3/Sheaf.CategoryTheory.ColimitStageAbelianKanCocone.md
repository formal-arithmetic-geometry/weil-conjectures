## What changed

Filled the repository's `CategoryTheory.colimit_stage_abelian_kan_cocone` hole with the generator/subgroup and eventual-relation proof, retaining its exact signature. Added only proof imports and private proved helpers.

Removed the duplicate private `lift_stage_arrow` proof from
`Sheaf.CategoryTheory.ColimitStageAbelianKanCocone` and imported
`Sheaf.CategoryTheory.ColimitStageKanCocone` with `import all`. The existing
`CategoryTheory.lift_stage_arrow` declaration is now used by the abelian proof;
all other helpers and the target theorem are unchanged.

## Proved and sorry left

Closed one repository hole: `CategoryTheory.colimit_stage_abelian_kan_cocone`. Added zero holes, split off zero statements, and left zero holes in the delivered module. The axiom check of the theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

`CategoryTheory.colimit_stage_abelian_kan_cocone` remains fully proved, with no
`sorry` declarations added or left. The existing arrow-lifting theorem and
`CategoryTheory.raw_abelian_section_kan_unit_relations` are used as dependencies.

## No longer needed

The duplicate local `lift_stage_arrow` helper and its proof are no longer needed.
No other planned proof dependency or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the statement of the existing
`CategoryTheory.lift_stage_arrow` theorem from
`Sheaf.CategoryTheory.ColimitStageKanCocone`. The repair reuses that declaration
instead. The theorem is private in its source module, so `import all` is required
to make the existing declaration available to this proof; the import direction is
acyclic and the module compiles.

## Second reading by E3

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are unchanged; the delivery only fills the target proof and adds private proof helpers. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked the target with `#print axioms`. It compiles without errors or warnings, has no `sorry`, forbidden declarations, or hollow definitions, and uses only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the private helper route against the existing `ColimitStageKanCocone` declaration and searched the local library for duplicates. The duplicate local `lift_stage_arrow` was removed; the proof reuses the existing theorem through proof-only `import all`. No new public statement or split-off hole was introduced. Verdict: pass.
4. Reviewed the proof from the target downward. The subgroup argument supplies generator surjectivity, the existing abelian unit-relation theorem supplies filtered equality, and evaluation plus forgetting reflects the colimit. The import list is retained where used; no further pruning was found. Verdict: pass.
5. Compared the node proof, dependencies, and unit route with the Lean proof. The node records the existing stage Kan lifting and abelian relation dependencies, and the unit route remains intact. Verdict: pass.

Changed during second reading: no Lean declarations or DAG statements; verified and retained the prior repair removing the duplicate `lift_stage_arrow` helper and using the existing proof-only import. Added this review record only.
