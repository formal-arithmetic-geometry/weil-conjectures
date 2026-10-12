## What changed

The existing declaration `AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech`
keeps its signature byte for byte. Its proof now handles degree zero by continuous restriction
of the étale sheaf to opens, Mathlib's `rightDerivedZeroIsoSelf`, and the proved categorical
Čech degree-zero comparison. Positive degrees use the first worker's successor obligation,
moved to its own new module `Sheaf.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluationSucc`.

Added `Sheaf.Topology.OpenCechZerothHomology`, proving
`TopCat.Sheaf.nonempty_openCech_zerothHomology` directly by sheaf gluing, for coefficients one
universe above the space. Its augmentation and the pulled-back sheaf are real constructions;
no object is chosen from an unproved existence theorem. All added proof imports are private.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech` by a genuine degree split.
The degree-zero branch is now proved, without affine acyclicity, using the independently proved
`TopCat.Sheaf.nonempty_openCech_zerothHomology` (node `lem-sc-open-cech-zeroth-homology`).

Added exactly one remaining named hole:
`AlgebraicGeometry.Scheme.nonempty_rightDerived_etale_affineOpenCech_succ`, in
`Sheaf.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluationSucc`, node
`lem-sc-etale-affine-open-cech-derived-evaluation-succ`.
It has a complete spectral-sequence proof in its docstring. There is no other delivered sorry.

This is a reduction, not a complete proof of the original comparison: one old hole closed,
one positive-degree hole added, hence zero net holes closed in the delivered modules.
The original comparison still uses `sorryAx` through the successor obligation. The new
zeroth-homology theorem uses only `propext`, `Classical.choice`, and `Quot.sound`, verified by
`#print axioms`. The targets' import-closure ledger, not this local count, determines progress.

## No longer needed

Removed the direct proof imports
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` and
`Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation` from the item's module.
The corresponding old proof dependencies `lem-sc-cech-spectral` and
`new-sheaf-cohomology-derived-evaluation` are no longer direct dependencies of the item's
proof. Both remain dependencies and private imports of the successor obligation, so neither
node nor module is globally pruned. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The first worker's report was stale: the file also contained an unreported degree-zero sorry,
without a node or docstring. The successor node had no searches and its `lean.statement` was
an ellipsis. Its statement depended on the original theorem rather than the underlying
notions, which would create a dependency cycle after recording the case reduction. The
original node also failed to record its degree-zero branch.

The second reader closed degree zero instead of preserving that undocumented hole, supplied
complete successor metadata and verified search records, and made the DAG follow both actual
branches. The upstream `cechCohomologyZeroIso` concerns its explicit Čech complex with the
space and coefficient universes tied; it does not directly prove this categorical-complex
statement with larger coefficients. The new proof uses the existing, proved categorical
coface formula and Mathlib's existing unique-gluing lemmas.

## New nodes

`lem-sc-etale-affine-open-cech-derived-evaluation-succ` records only the positive-degree
spectral-sequence obligation, retaining the original geometric and acyclicity hypotheses.
Its module, verbatim Lean signature, full proof, underlying statement dependencies, source,
searches, provenance, and chapter/unit are recorded. It does not assert degree zero.

`lem-sc-open-cech-zeroth-homology` records the proved general open-cover gluing comparison,
with no separatedness, affineness, finite-cover, or acyclicity hypotheses. Its source is
Stacks Tag 03AN, as used by Tag 03AZ. Both new statements are in their own modules.
No existing statement or definition changed; no change record is required.

## Second reading by N1

1. Compared the item module with the repository using `diff` and independently compared the
   original declaration's signature byte for byte: identical. Existing visibility and
   definitions are unchanged. New declarations are confined to the two new modules. PASS.
2. Compiled all three modules with `lcompile.py --all`, with no errors or warnings. There is
   exactly one named theorem sorry, listed above, no sorry in data, and no forbidden axiom,
   unsafe, opaque, extern, or implemented_by escape. Scratch `#print axioms` checks show only
   the three allowed axioms for the new gluing proof, and those plus `sorryAx` for the original
   theorem, as expected from its positive-degree dependency. PASS as a reduction.
3. Read both new statements against their source arguments. The successor theorem is the
   strictly positive-degree part; the missing zero edge is actually proved, so this is not
   the entire original statement under another name. The gluing theorem follows from unique
   gluing and the absence of incoming boundaries. Checked empty covers/empty spaces, the
   zero sheaf, singleton covers, and nonempty finite intersections (including empty
   intersections of disjoint affine opens). No additional hypotheses enter the original
   statement. Searches used different queries through LeanFinder, Loogle and grep; LeanSearch
   was attempted and unavailable, with that failure recorded. Inspected the upstream
   explicit-complex comparison and used its proved coface formula, rather than duplicating
   a usable same-statement theorem. PASS.
4. The proof uses the shortest degree-zero route: left-exact evaluation plus ordinary
   sheaf gluing. The spectral-sequence route is retained for positive degrees. Imports are
   limited to signature/instance requirements and the proofs used or retained as obligations;
   new proof imports are private. Every old direct proof dependency removed from the item is
   accounted for under No longer needed. `dag/units/sk-prop-cd.json` has empty realized lists,
   and its Step 5 Artin–Schreier/étale descent route is unchanged. PASS.
5. The original node now records precisely the zero and successor branches. The successor
   node retains the spectral and derived-evaluation plan; the gluing node records augmentation,
   compatibility, unique gluing, and cycles-to-homology. Checked proof_deps against step uses,
   verbatim Lean records, source, search, provenance and chapter/unit fields. PASS.

Second-reading changes: proved the undocumented zero edge; moved the positive-degree hole
into its own module; supplied a proved categorical gluing helper; repaired both new nodes and
the original proof route; replaced the stale report and removed a long-line warning. The
successor spectral-sequence obligation remains open and is not reported as proved.

Validation: the required deliver3.py dry run passed (CODEX review class).
