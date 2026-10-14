## What changed

Empty Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker, leaving a module
with no declarations or imports, the same result as the withdrawal in step 8b.
This repairs the supplied compatibility stub rather than restoring the retired
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker declaration.
The full cokernel calculation stays in local hc of
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion. Its sole caller,
Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion, is adapted in this delivery:
replace the private Coker import with PicardDecomposition and TypeTags.Hom,
and inline the cokernel calculation. The surviving theorem's signature,
visibility, public imports and docstring are unchanged.

The cokernel node continues to map to the surviving parent theorem's second
conjunct; the parent node records its inlined proof and avoids a self-dependency.
No target statement or definition changes. Change record:
coord/changes/pic_proper_ntorsion_coker.md.

## Proved and sorry left

Zero holes closed, zero holes added, zero split off. This is a duplicate
withdrawal and forced importer repair, not net proof progress. The previously
proved AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker is retired; its
complete argument survives inside AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion.
The delivered parent contains no sorry. Dependency holes are unchanged.

## No longer needed

The standalone AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker and
Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker module. Remove the parent's
private import of that module. Its former private imports PicardDecomposition,
PicProperNTorsionDiv and Mathlib.Algebra.Group.TypeTags.Hom are still needed by
the inlined parent proof and are imported there explicitly. The withdrawn
module's six public imports are unnecessary because it has no remaining
importers; the parent already has the same six public imports.
No mathematical dependency or unit step is pruned. The cokernel DAG node stays
mapped to the parent's cokernel conjunct, with decomposition and divisibility
as its proof dependencies.

## Where the brief, the DAG or earlier work was wrong

Earlier repairs restored the retired duplicate and reversed its node mapping.
This delivery preserves retirement and includes the sole caller's adaptation.
The return calls the item its own importer, but a complete source search finds
PicProperNTorsion as the sole importing/calling module.

The aggregate BatchProbe error names SchemeTensorShiftBinaryLocalizationSquare
and DerivedTensorPreservesQCoh. This is an environment declaration clash in
that aggregate probe, not evidence that either Picard module fails alone.
The delivery tool checks both the adapted parent and its axiom/sorry probe;
the maintainer must verify the global aggregate environment independently.
No unrelated tensor module is changed and no worker global build is run.

The earlier report's tool blocker is obsolete: deliver3.py now recognizes
this group's dedicated repair handoff. A fresh dry run of the supplied
compatibility form passed. This session tried the brief's deleted.txt withdrawal format. Compilation
passed, but preflight rejected the tool-generated empty module's 120-character
comment. To achieve the same retirement without editing tools, this delivery
supplies the empty module explicitly with a short comment and no imports.
The adapted parent compiles in 2.4 seconds. The final dry run checks the whole
set and the forced-adaptation counterfactual. The final dry run printed OK,
except for the second reading reserved for the independent reader. The parent
axiom/sorry probe ran without reported forbidden axioms. For the empty component,
the tool's appended probe cannot elaborate its run_cmd without Lean.Elab.Command;
there are no declarations in that module to inspect, and deliver3.py accepts
this with a note. No unnecessary import is added just to support that probe.
The maintainer's aggregate probe remains a global verification task.

## Forced adaptations

Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion (unclaimed in the supplied
snapshot) is the sole caller. Its original compiles against the baseline,
but against the retired interface it fails at its hc call with:
Unknown constant AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker.
The adaptation replaces that call with the full typed cokernel calculation;
PicardDecomposition and TypeTags.Hom replace the Coker proof import because
the calculation uses their APIs. Its signature, visibility, public imports,
existing docstring, ht and hd lines and final conjunction stay unchanged.
The delivery tool checks the original against both environments and compiles
the adapted parent. No other module requires adaptation.

## Second reading by N3

1. **Statements and accidental changes.** Compared both delivered Lean modules and both DAG nodes with the repository. The parent theorem's signature and docstring are byte-for-byte unchanged; the standalone module is intentionally retired, and the node changes only update its mapping and proof metadata.

2. **Proof and trust basis.** Compiled the parent and retired module with `lcompile.py --all`; also compiled an axiom probe. The parent proof has no local `sorry`; its remaining `sorryAx` dependencies are the previously open torsion and divisibility declarations. No forbidden commands or hollow definitions occur. The empty module now has the required public section marker.

3. **Split statements and search.** No statements were split off and no new declarations were added. The cokernel statement is the parent theorem's existing second conjunct, so no duplicate theorem remains. The node's existing Mathlib and library search record was checked; the proof uses the existing decomposition, divisibility theorem, and Mathlib quotient first-isomorphism APIs.

4. **Shortest route and pruning.** The full cokernel calculation is retained inline in the parent, avoiding the retired duplicate. The parent imports `PicardDecomposition`, `PicProperNTorsionDiv`, and `TypeTags.Hom` because the calculation uses them; the retired module has no imports. The unit's route and all three realized components remain in use.

5. **DAG agreement.** The parent node's proof and `proof_deps` name torsion, divisibility, and Picard decomposition, matching the Lean proof. The cokernel node maps to the parent declaration's cokernel conjunct and records the retained local calculation. No target statement or definition changed.

**Changed:** verified and retained the supplied parent adaptation, ensured the withdrawn module is a valid empty module with `@[expose] public section`, and added this second-reading record. No holes were closed or added; no modules beyond the duplicate were pruned.
