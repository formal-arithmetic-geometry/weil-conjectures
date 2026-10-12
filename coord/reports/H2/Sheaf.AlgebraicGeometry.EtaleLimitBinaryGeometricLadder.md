## What changed

Completed `AlgebraicGeometry.Etale.etale_limit_binary_geometric_ladder` from the native
zero restriction row and successor cocone segment. Its existing signature and docstring
are unchanged. Five private categorical/group helpers construct zero-term exactness and
transport stage-leg squares to colimit squares. The zero case uses a genuinely constructed
constant PUnit group diagram and connectedness of the directed index.

Added `EtaleLimitBinaryZeroRestrictionRow` and `EtaleLimitBinarySuccessorCoconeSegment`
and their nodes. Their public imports support their statements; plain imports retain the
geometric proof dependencies needed to complete the two remaining holes. Removed the unused
Exact import from the zero row. No definition or existing public statement changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etale_limit_binary_geometric_ladder`
(node `lem-weil-pbc-etale-limit-binary-geometric-ladder`).

Added two holes, each exactly the whole proof of a public named theorem with a source,
complete construction proof in its docstring, and its node:

- `AlgebraicGeometry.Etale.etale_limit_binary_zero_restriction_row`
  (`lem-weil-pbc-etale-limit-binary-zero-restriction-row`);
- `AlgebraicGeometry.Etale.etale_limit_binary_successor_cocone_segment`
  (`lem-weil-pbc-etale-limit-binary-successor-cocone-segment`).

The item has no direct sorry left. This is a decomposition: one original hole closed,
two added, net -1 among these declarations, with no claim of net progress or of an
axiom-free completed geometric theorem. The five private helpers have no holes. No data
is placed in a definition or chosen from an unproved mere existence theorem: row witnesses
are eliminated only within this propositional theorem proof.

## No longer needed

The main module no longer directly imports:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`;
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`;
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`;
- `Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`;
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

All twelve old proof dependencies leave the main node's immediate proof_deps:
`def-weil-pbc-scheme-conventions`, `def-weil-pbc-stage-cohomology-comparison`,
`lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-colimit-initial-full-subcategory`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lem-weil-pbc-etale-limit-canonical-cohomology-diagram`,
`lem-weil-pbc-etale-mayer-vietoris`, `lem-weil-pbc-etale-mayer-vietoris-pullback`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`,
`lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-left-adjoint-preserves-colimits`,
`lem-weil-pbc-limit-cone-affine-projections-opens`.
They remain in the two lower nodes' proof plans. Their declaration modules remain imported
there, directly or through public statement imports. Thus no geometric node or module is
claimed as globally pruned. The main categorical descent uses Mathlib
`Functor.Final.colimitIso` directly. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly described the old geometric dependencies as unnecessary:
they moved to the lower open statements. The second reader restored their proof imports,
so the import closure retains unfinished dependencies and cannot claim artificial pruning.

An earlier dry run had reported an ImportError for refuse_missing. The current dry run
passes that point; its first failure was only the missing second-reading report section.
All three delivered modules compile locally without a dependency rebuild or tool edit.

## New nodes

`lem-weil-pbc-etale-limit-binary-zero-restriction-row` constructs only the degree-zero
restriction transformation, its pointwise injectivity and its certified product comparison.
The main proof supplies the zero terms, their colimits, exactness and descended square.

`lem-weil-pbc-etale-limit-binary-successor-cocone-segment` constructs the positive-degree
native Mayer--Vietoris segment and equations on stage legs. The main proof supplies the
cofinal colimit identification and proves all three whole-colimit squares by hom_ext.
Neither statement simply renames the full item: the degree split and categorical descent
are explicit Lean proofs. No change record is required because existing signatures,
definitions and public imports remain unchanged.

## Second reading by H2

1. Compared the delivered main module with the repository using diff and checked the entire
   existing theorem signature byte for byte: identical. Only imports, new private helpers
   and its proof changed. The two row modules and their nodes are new. No target, existing
   definition, existing docstring or public import was changed.
2. Compiled all three modules through lcompile.py. Exactly two direct sorries occur, in the
   named row theorems listed above. No axiom, unsafe, opaque, implemented_by, extern,
   skipKernelTC or holed definition occurs. A scratch copy prints axioms for the public
   declarations and all five private helpers. The five helpers use only propext,
   Classical.choice and Quot.sound (some use fewer); the two row theorems additionally
   use sorryAx. The delivery tool also probes every declaration.
3. Checked both row statements against the source construction at Stacks Tags 09YQ and
   0A50 and against the imported canonical-diagram and Mayer--Vietoris APIs. The directed
   tail has i0 as its first stage; restrictions of U and V cover every stage and the limit.
   Compactness and quasi-separatedness are supplied on that stage, including their
   intersection. Empty opens give zero factors; coincident opens give diagonal/difference
   maps; degree q=0 is the ordinary first boundary segment. These do not require negative
   degree, ambient quasi-separatedness, or continuity. Coefficient and pullback naturality
   provide simultaneous boundary maps. Independent leanfinder, loogle, msearch grep and
   rg searches found generic sheaf gluing, Mayer--Vietoris, linear-map exactness and colimit
   descent tools, but no duplicate of either geometric row. The docstrings specify the
   full remaining construction. Closing these geometric rows requires that construction,
   rather than a few-minute application of an existing result.
4. Read top down: the zero branch constructs real zero diagrams and iso certificates;
   the successor branch transports three stage-leg equations using hom_ext and finality.
   The short direct group helpers avoid unnecessary linear-map transport. All old immediate
   proof dependencies are listed above and retained below the open rows. Read
   dag/units/sk-thm-p1.json: none of the removed immediate dependencies realizes a unit step;
   the unit's realized record and its higher route are unchanged. No globally pruned module
   is claimed. Restored proof-only imports in both row modules; removed the zero row's unused
   public Exact import.
5. Compared the main node with the repository: only proof, proof_deps and proof_origin differ.
   Its two dependencies match the two theorem applications, and the remaining categorical
   steps are elementary and actually proved. Checked new node fields, sources, complete
   statements, matching Lean records, chapter/unit, split status, blueprint provenance and
   searches. Each proof_deps list is exactly the union of its proof steps' uses.

Second-reading repairs: retained the lower geometric dependency imports, removed the unused
zero-row Exact import, recorded independent searches, and corrected the pruning and hole
accounting in this report. The theorem proof needed no repair.

Validation note: restoring the geometric proof imports compiled both lower rows, but
repeated full-main compiles exceeded lcompile.py's fixed 60-second limit on this highly
loaded shared machine. A signature/helper-only diagnostic compiled and printed the
helper and lower-row axioms. Transparency and a shorter zero-functor construction were
tested only in scratch copies and were not retained. No compiler limit or tool was changed.

Final validation: deliver3.py --no-push printed OK at dry-run commit ceb70322e4.
All delivered modules compiled and every declaration passed the delivery axiom probe.
The earlier timeouts cleared without a change to the original proof or compiler limits.
Explicit #print axioms of the compiled main theorem and both row theorems reports
exactly propext, Classical.choice, Quot.sound and sorryAx, with sorryAx inherited
from the two open rows in the main theorem. The scratch copy was removed.
