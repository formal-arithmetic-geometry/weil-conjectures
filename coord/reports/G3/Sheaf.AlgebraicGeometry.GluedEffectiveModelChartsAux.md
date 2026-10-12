## What changed

Repaired the saved attempt. `GluedEffectiveModelChartsAux.lean` now constructs the global
map by Mathlib's `Scheme.Cover.glueMorphisms` and proves every chart equation using
`Scheme.Cover.ι_glueMorphisms`. Its existing theorem signature and visibility are unchanged.
Added a proof-only import of `Mathlib.AlgebraicGeometry.Gluing` and the new
`Sheaf.AlgebraicGeometry.GluedModelStructure` module. Updated the item's DAG proof to match.

The new `exists_glued_model_structure` theorem supplies descended charts and agreement of
the local maps on overlaps. It has no global map witness. This isolates the geometric part
of Stacks Tag 0AP4; the final global-map construction and verification are implemented here.
No definition or existing statement changes, and no forced adaptations.

## Proved and sorry left

Closed the original hole in `CategoryTheory.Over.DescentDatum.exists_glued_model_data`
(node `lem-pd-glued-effective-model-charts-aux`). No sorry remains in the item module.
Added one hole in `CategoryTheory.Over.DescentDatum.exists_glued_model_structure`
(node `lem-pd-glued-model-compatible-charts`), in `GluedModelStructure.lean`.
This is a decomposition: one original hole closed, one lower hole added, net zero holes.
It does not establish an axiom-free geometric gluing theorem yet. The new theorem's
source and complete proof in words are in its docstring and node.

Both delivered modules compile through lcompile.py. The empty-index case makes V empty
and is handled by the empty gluing; one chart needs no nontrivial transitions. Agreement
on overlaps includes all pairs, so duplicate opens and non-affine intersections cause no
missing assumption. The global map is constructed from a compatible family by a genuine
Mathlib gluing operation; no arbitrary witness is placed into any definition.

## No longer needed

No original import is removed, and no existing module is certified pruned from the target
closure. The original DAG proof dependency `lem-pd-glued-effective-model-charts` is removed
from this auxiliary node's proof: that parent invokes this auxiliary theorem, so using it
here would be circular. It remains needed upstream and is not globally pruned.

Discarded the unpublished saved `GluedModelCompatibility.lean` and its node
`new-glued-model-compatibility`, and replaced the saved `new-glued-model-structure` node.
Neither of those two saved intermediate statements is used. The revised structure module
and Mathlib gluing import are both needed by the implemented proof.

## Where the brief, the DAG or earlier work was wrong

The saved `glued_model_compatibility` statement was false: its q_0 was arbitrary and no
hypothesis related it to the local maps. For p the identity and a single full chart, an
unrelated endomorphism q_0 already violates the claimed equation. Its hstruct did not even
mention q_0. The saved node proofs also depended on the item they were meant to prove,
creating dependency cycles, and the saved docstrings lacked complete proofs in words.
The saved report's second-reading section was written prematurely; it has been removed.

The initial dry run reached preflight and rejected missing LeanSearch records in the saved
nodes, rather than the prior worker's reported "nothing is proved" failure. The current
LeanSearch service returns Internal Server Error; searches are recorded as unavailable,
not as a mathematical no-match. LeanFinder, Loogle, and Mathlib source searches ran.

The new node uses `lem-weil-pbc-open-subscheme-fpqc-descent` as a generic descent-of-opens
tool, and `lem-galois-fpqc-morphisms-descend` as a generic full-faithfulness tool for
singleton fpqc covers, together with the existing scheme/morphism gluing Mathlib leaves.
The maintainer should record these generic tool uses if required. The transport-form
`lem-pd-morphisms-descend` was inspected but requires `QuasiCompact p`, which is stronger
than the singleton-precoverage hypothesis here; the canonical-pullback form has exactly
the needed coverage hypothesis. No quasi-compactness assumption is added.
The unit's realized statement and steps are untouched (its recorded realization lists
are empty). No proof-dependency import of the parent is introduced.

## Second reading by G3

1. Compared the delivered auxiliary module with the repository version. The existing
   theorem signature and visibility are byte-for-byte unchanged; only proof and imports
   differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The auxiliary proof is
   accepted, and the only remaining `sorry` is the explicitly split-off structure
   theorem. No definitions contain `sorry`, and no forbidden declarations were added.
   Verdict: pass.
3. Checked the split-off statement and its node against the source construction. It is
   a strictly lower statement (charts and overlap agreement, without the global map),
   has a complete proof description, and introduces no extra hypotheses. Verdict: pass.
4. Checked the proof route and imports. The parent auxiliary node is not used
   circularly; Mathlib's `glueMorphisms` supplies the global map, while the structure
   theorem supplies only the descended charts. The unit realization and route are
   unchanged. Verdict: pass.
5. Checked the DAG proof and dependency records against the Lean proof and the
   recorded searches. The auxiliary node now depends on the structure node and the
   Mathlib gluing result; the structure node records its four genuine dependencies.
   Verdict: pass.

Changed after this reading: added this review record only; no Lean declarations or
statements were altered.

## New nodes

`lem-pd-glued-model-compatible-charts`, in
`dag/nodes/sec-picard-framework/lem-pd-glued-model-compatible-charts.json`, states the
existence of descended open charts with agreement on overlaps, before constructing the
global map. It follows the descended-overlap part of Stacks Tag 0AP4. Its four proof steps
use descent of opens, full faithfulness, scheme gluing, and the transition gluing relation.
The node has no dependency back to the auxiliary theorem or its parent. There are no
change records because no landed interface changes.
