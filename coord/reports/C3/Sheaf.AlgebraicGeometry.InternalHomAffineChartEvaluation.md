## What changed

Proved AlgebraicGeometry.internalHom_evaluation_chart_compare in
lean/Sheaf/AlgebraicGeometry/InternalHomAffineChartEvaluation.lean.
The proof unfolds the constructed equivalences, identifies the overFunctorEquiv
components with identity functions, applies naturality along the map from the
resulting over object to Over.mk (identity U), and cancels the section transports
by functoriality in the thin category of opens. Definitions, signatures, visibility,
and imports are unchanged. This follows the existing node's component-comparison
plan and works uniformly for empty opens and arbitrary module sheaves.

## Proved and sorry left

Closed: AlgebraicGeometry.internalHom_evaluation_chart_compare
(node lem-sc-internal-hom-affine-chart-evaluation), the module's only sorry.
Added: none. Remaining in the delivered module: none.
This is a direct proof, with no decomposition or new holed dependency.

## No longer needed

None. Both existing public imports are needed by the definitions and statement;
there are no proof-dependency imports or DAG dependencies to prune.
No new module or node is needed.

## Where the brief, the DAG or earlier work was wrong

None. The existing node accurately describes the component computation.

## Second reading by C3

1. Interface: PASS. Read the complete repository and sandbox modules and their
   unified diff. The only difference replaces the body of
   AlgebraicGeometry.internalHom_evaluation_chart_compare. All three definitions,
   the theorem signature, docstrings, visibility and imports are byte-for-byte
   unchanged. No interface change or change record is needed.
2. Proof: PASS. Independently compiled the module with lcompile.py, without errors
   or warnings. Compiled a scratch copy with #print axioms for chartSectionsEquiv,
   isoRestrictEquiv, chartHomEquiv and internalHom_evaluation_chart_compare: each
   uses exactly propext, Classical.choice and Quot.sound, with no sorryAx. Scanned
   the delivered source: no sorry, axiom, unsafe, opaque, implemented_by or extern.
   The equivalences construct their data from existing categorical equivalences;
   no arbitrary witness from an unproved existence theorem is introduced.
3. Split statements: PASS, vacuous. There are no new declarations, new nodes or
   split-off holes. The original theorem remains uniform in X, M, F and the affine
   open U; the argument uses no quasi-coherence, finite-presentation or nonempty
   hypothesis, so empty opens and zero module sheaves are not excluded.
4. Route and pruning: PASS. Read Mathlib's restrictFunctorComp component lemmas
   and overFunctorEquiv construction. The proof unfolds precisely these
   constructions, checks the hom and inv additive components by rfl, then applies
   PresheafOfModules.naturality_apply to Over.homMk W.hom and cancels the remaining
   transports using functoriality. A fresh Loogle query for naturality_apply and
   searches for chart/evaluation comparisons in lean/ and upstream found no
   replacement for the constructed comparison. Both public imports supply types
   and definitions in the existing interface (internal Hom and moduleSpecΓFunctor),
   rather than only proof lemmas. The old proof_deps is empty, so the pruning list
   is complete. Read dag/units/sk-thm-picard-duality.json: this below-unit chart
   computation changes none of its realized fields or its residue/duality route.
5. DAG: PASS. Read lem-sc-internal-hom-affine-chart-evaluation.json in full. Its
   statement matches the unchanged Lean theorem, including arbitrary module
   sheaves. Its elementary component-comparison step describes the actual proof:
   forgetful preimage, over-site evaluation, identity comparison components,
   composite-image transports, naturality at the terminal over object, and linear
   map extensionality. Its empty proof_deps and existing proof_origin remain
   accurate. No node update is necessary.

Second reading changed only this report: no Lean or DAG repairs were needed.
Closed holes: AlgebraicGeometry.internalHom_evaluation_chart_compare (1 of 1).
Added holes: none. This is a proof, not a decomposition.
