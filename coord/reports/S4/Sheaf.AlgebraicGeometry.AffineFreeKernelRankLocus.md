## What changed

Proved `AlgebraicGeometry.Scheme.exists_affineFreeKernelRankLocus` in
`Sheaf.AlgebraicGeometry.AffineFreeKernelRankLocus`, preserving its signature and public
imports. Added two proof-only imports for new, fully proved intermediate theorems:
`Sheaf.AlgebraicGeometry.AffineFreeMapZeroLocus` and
`Sheaf.AlgebraicGeometry.FreeKernelMaximalRankCriterion`. The proof also imports the existing
scheme-module free-frame and empty-scheme API and the scheme initial-object API.

The zero-locus theorem constructs the quotient spectrum of the finitely generated matrix-entry
ideal and proves its universal property for arbitrary source schemes through the
Spec/global-sections adjunction. The kernel criterion trivializes the kernel on open charts,
uses injectivity of the transpose of a square matrix for equal ranks, and the injective
free-module rank inequality for strictly unequal ranks. The original theorem combines these
results: equal ranks use the zero locus; strictly larger requested rank uses the empty scheme.
Private section/matrix helpers in the new modules are fully proved. Updated the original node's
proof, proof dependencies and proof origin to match this route. No existing statement,
definition, visibility or unit realization changed; no forced adaptations or change records.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_affineFreeKernelRankLocus`
(node `lem-sc-affine-free-kernel-rank-locus`). Added zero holes and split off zero unproved
statements. No `sorry` remains in any delivered module.

The two added public theorems are also fully proved:
`AlgebraicGeometry.Scheme.exists_affineFreeMapZeroLocus` and
`AlgebraicGeometry.Scheme.finiteLocallyFree_kernel_maximalRank_iff`.
This delivery is a proof, not a decomposition into unproved dependencies.

All three modules compile together without warnings using `lcompile.py --all`.
The direct `#print axioms` checks of all three public theorems report only
`propext`, `Classical.choice`, and `Quot.sound`. The longest individual compilation was
approximately 31 seconds. The delivery dry run additionally probes all declarations.

## No longer needed

No original imports were removed: its public imports support the unchanged statement.
The planned dependency `lem-weil-pbc-quasi-coherent-ideal-closed-subscheme` is no longer needed
by this argument. The explicit affine quotient replaces the general ideal-sheaf construction;
that dependency is removed from the original node's proof dependencies. This is pruning from
this route, not a claim that other targets no longer use the general ideal-sheaf API.
The planned square-injection lemma is still needed through the new kernel criterion and is
implemented using its recorded Mathlib match. The strict-rank padding argument is unnecessary:
the existing injective free-module rank inequality proves that case directly.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The DAG described the correct matrix
argument but did not supply its sheaf-to-matrix glue as a declaration. The two new proved
results make that glue reusable. Mathlib searches found useful matrix and ideal/scheme
building blocks, but no exact sheaf-level theorem; the LeanSearch service returned an internal
server error, recorded in the new nodes' search histories. The theorem-of-cube unit's route
and its lowest-cohomology matrix-locus step are preserved; this is a refinement below that unit.

## New nodes

`lem-sc-affine-free-map-zero-locus`, in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-free-map-zero-locus.json`, records the fully proved
zero-pullback locus theorem in `Sheaf.AlgebraicGeometry.AffineFreeMapZeroLocus`. This is strictly
a geometric part of the original argument and makes no assertion about kernel rank. Its
construction is an explicit ideal quotient, with no data selected from an unproved existence
statement. Empty matrices, zero rings and arbitrary nonaffine source schemes are included.

`lem-sc-free-kernel-maximal-rank-criterion`, in
`dag/nodes/sec-abelian-varieties/lem-sc-free-kernel-maximal-rank-criterion.json`, records the
fully proved rank criterion in `Sheaf.AlgebraicGeometry.FreeKernelMaximalRankCriterion`.
It holds on any scheme and makes no representability or finite-presentation assertion.
The empty-scheme disjunct is essential when s<r. Rank-zero domains, rank-zero codomains,
empty schemes and nontrivial rings on charts containing a point were checked explicitly in
the proof. Both nodes have the original node's chapter and unit, source citations,
three kinds of recorded Mathlib search and complete Lean signature records.

## Second reading by S4

1. Compared the original module with the repository using `diff -u`: its sole existing
   declaration's signature is byte-for-byte unchanged, as are its docstring, visibility and
   public imports. Only proof imports and the proof body changed. The other two delivered
   modules are new; no existing definition or target statement changes.
2. Read all three modules, including every private helper. The only choices are supplied
   free-frame witnesses, and all private definitions have explicit constructions. No `sorry`,
   axiom, unsafe declaration, opaque declaration, external implementation or kernel-check
   bypass occurs. All three files compile cleanly with `lcompile.py --all`; the scratch
   axiom check of the three public results uses only `propext`, `Classical.choice`, and
   `Quot.sound`. The delivery additionally probes every declaration.
3. There are zero split-off unproved statements. Both new proved theorems are strictly
   intermediate parts of the argument, not restatements. Checked rank-zero domains and
   codomains, empty matrices, zero rings, empty schemes, strict rank inequality and arbitrary
   nonaffine source schemes. In particular the empty-scheme alternative in the kernel
   criterion is necessary. Independent leanfinder and grep searches with different wording,
   and repository/upstream `rg` searches, found no existing replacement for these sheaf-level
   results. The square-matrix argument uses the existing node's recorded Mathlib match.
4. The top-level proof uses the zero-locus universal property and the kernel criterion
   directly. The explicit quotient avoids the old general quasi-coherent ideal-sheaf
   construction. The square-injection dependency remains through the criterion; finite
   presentation remains used. Thus `No longer needed` accounts for all old proof dependencies.
   Public imports support the signatures; proof-only imports are plain imports. The
   QuasicoherentKernel import supplies preservation of limits under restriction, not an
   unproved quasi-coherence assumption. Read `sk-prop-av-cube.json`: its `realized` field
   remains unchanged, and the refinement stays below its lowest-cohomology matrix-locus route.
5. Checked each new node's statement, verbatim Lean signature, source, chapter/unit,
   creation record, search records and proof steps against the code. Each `proof_deps` is
   the union of the steps' `uses`. The original node retains its statement and Lean signature;
   its new proof and dependencies describe the actual equal-rank/empty-scheme case split.
   Read Stacks Tags 0BDL and 0EWY to check the cited local matrix argument.

Changed only the zero-locus node's copied `proof_origin.place` and `proof_origin.note`:
removed the irrelevant strict-rank/0EWY description and recorded its explicit quotient and
Spec/global-sections argument. Added this second-reading section. No Lean repair was needed.
