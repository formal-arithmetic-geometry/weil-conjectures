## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_degree_zero`
with its original signature unchanged. The proof constructs the canonical Mathlib
`rightDerivedZeroIsoSelf` comparisons, applies the existing proved
`ModuleCohomologyFMapData.map_zero_augmentation`, and cancels the two comparison
isomorphisms. Added plain proof-only imports of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation` and
`Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`. The transparency option is
scoped to this theorem, and the existing public import is retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_degree_zero`
(node `lem-weil-pbc-module-cohomology-fmap-basic-degree-zero`).
No holes added; no sorry remains in the delivered module. This is a proof, not a
decomposition. Removed the first worker's proposed holed theorem
`moduleCohomologyFMapData_basic_degree_zero` and its unlanded node
`lem-weil-pbc-module-cohomology-fmap-basic-degree-zero-data`.
The scratch-copy `#print axioms` returned exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`.

## No longer needed

No existing import was removed and no whole module is claimed to become unreachable.
The new proof no longer directly uses these old proof dependencies (their statement
references remain unchanged):
- `def-pc-module-pullback`
- `def-sp-left-exact-additive`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-derived-functor-map-via-lift`
- `lem-weil-pbc-lift-along-injective-quasi-iso`

The Mathlib left-exact degree-zero node is retained: `rightDerivedZeroIsoSelf`
uses exactly the left-exact resolution comparison it records. The proposed
fixed-datum split-off node is removed entirely from this delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's fixed-datum lemma repeated the substantive conclusion of the
item and left that calculation unresolved, with only a short docstring. Its
one-line application was not an adequate reduction. An existing upstream proof
in `FormalFunctionsDegreeZeroSystemIso.degreeZero_naturality` revealed the shorter
route through the proved augmentation square. That private declaration is used as
a reference for the argument, not imported; its heavy formal-fibre module would
be unnecessary. LeanFinder independently found Mathlib's
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`; Loogle with an unqualified name
returned no hit, and source searches verified the precise declaration and the
existing project augmentation theorem.

## Second reading by D4

1. Compared the sandbox module with the repository using diff. PASS: the sole
   existing declaration's signature is byte for byte unchanged; there is no
   definition or visibility change and no change record is necessary.
2. Compiled the repaired file locally with lcompile.py: no error or warning.
   PASS: no sorry, axiom, unsafe, opaque, implemented_by or extern. Scratch-copy
   #print axioms reports only the three permitted axioms. No definition is added.
3. FAIL in the first delivery, repaired: removed the holed fixed-datum restatement
   and its node. No new statement is left to review. Searched using sections,
   augmentation and zeroth right-derived comparisons rather than only the item's
   name, including LeanFinder, Loogle and rg. The existing augmentation theorem
   has the needed equation exactly. Evaluation at the whole space and the
   canonical comparison apply also to the empty scheme and zero module sheaf;
   the argument adds no nonemptiness or nonzero hypothesis.
4. PASS after repair: the proof is the canonical degree-zero comparison followed
   by the already proved augmentation square and isomorphism cancellation.
   Both new imports are proof-only and used. All five removed old direct proof
   dependencies are listed above. Checked dag/units/sk-thm-p1.json: this auxiliary
   node is not a realized unit step, and no chapter/unit route or realized field
   changes.
5. PASS after repair: updated the existing node's proof, proof_deps and
   proof_origin to the actual argument, retaining its statement and lean record.
   The union of step uses is exactly proof_deps. No new node remains.

Changes made by this second reading: replaced the unresolved fixed-datum reduction
by the full proof, removed its proposed theorem and node, added two plain proof
imports, and corrected the DAG and report. One of one original holes closed;
zero split off.
