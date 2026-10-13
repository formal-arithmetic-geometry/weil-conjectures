## What changed

Proved `AlgebraicGeometry.Scheme.geometricPointMorphism_category_equivalence` with its
existing signature and public imports unchanged. Added two proof-only imports:
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts` and
`WeilConjectures.Mathlib.CategoryTheory.Elements`. Precomposition is bijective on
pointed lifts by the existing proved field-precomposition injectivity and etale
lift-descent lemmas. The resulting natural isomorphism induces the required
category equivalence. Updated the existing node's proof, proof_deps and proof_origin.

Removed the first worker's redundant component module and its new node, neither of
which belongs to the repository. No new statements, definitions, or change records.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.geometricPointMorphism_category_equivalence`
(node `new-geometric-point-morphism-category-equivalence`), one of one original holes.
Holes added: none. Sorries left in the delivered module: none. Split off: none.
The abandoned `geometricPointMorphism_category_equivalence_components` was removed.
This is a proof, not a decomposition. The final axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the proposed proof-only import
`Sheaf.AlgebraicGeometry.GeometricPointMorphismCategoryEquivalenceComponents` and
its unlanded module and node. No repository module import was removed, so no existing
module is claimed pruned from the target closure.

Every old proof_deps entry was replaced by the two proved upstream tool nodes. The
following nodes are no longer directly used by this proof (definitions still needed
by the unchanged signature remain in stmt_deps; tools can use these transitively):

- `lem-weil-pbc-morphism-from-spec-field`
- `lem-weil-pbc-residue-field-point-naturality`
- `def-weil-affine-spectrum`
- `def-weil-residue-field`
- `def-weil-geometric-point`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-pointed-etale-neighbourhoods`
- `lem-weil-pbc-etale-residue-field-extension-separable`
- `def-weil-pbc-separable-algebraic-extension`
- `def-weil-algebraic-closure`
- `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`

The new proof_deps are `lem-exc-field-point-precomposition-injective` and
`lem-exc-etale-lift-separably-closed-factorization`. Both are recorded closed tools.

## Where the brief, the DAG or earlier work was wrong

The first worker's conjunction of Faithful, Full and EssSurj was equivalent to the
entire target, not strictly simpler. Its proof_deps also cited the target while the
target proof cited it, producing a circular dependency. Its docstring omitted the
required complete proof. Removed that attempted split rather than count it as progress.
The original DAG's field argument is already implemented by proved upstream lemmas;
no new decomposition is needed.

## Second reading by G2

1. Compared the delivered module with the repository using diff and a byte-for-byte
   assertion on the existing theorem signature. Verdict: unchanged hypotheses,
   conclusion, universes, visibility, definitions, and public imports; only its proof
   and two plain imports changed. No change record is required.
2. Compiled the final module with lcompile.py, with no errors or warnings. Read the
   proof and the upstream tools. A scratch copy with #print axioms reports exactly
   propext, Classical.choice and Quot.sound. No sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition is present. Verdict: fully proved.
3. Rejected and deleted the single split-off conjunction and node as a restatement.
   Searched with Loogle for CategoryOfElements.map, LeanFinder for etale lift descent,
   and rg for field-precomposition injectivity and separably closed factorization.
   Read the existing recorded source lemmas SpecMap_comp_injective and
   exists_SpecMap_comp_eq_of_isSepClosed and reused them. Verdict: no new statement
   remains to review. Empty etale neighbourhoods have no pointed lifts, so their
   bijectivity is vacuous; identity maps, nonalgebraic extensions and arbitrary
   characteristic are covered without additional hypotheses.
4. Reduced the target directly to those proved tools and the generic NatIso.mapElements
   construction. Both added imports are needed; original public imports support the
   unchanged signature. Listed every old proof_deps entry above. Read
   dag/units/sk-thm-p1.json and its realized statement and steps: this tool node is not
   one of the realized unit steps, and none of those steps or units is bypassed or
   changed. Verdict: shorter route below the unit level, with no module pruning claim.
5. Replaced the existing node's proof by the actual injectivity, surjectivity and
   natural-isomorphism assembly steps; proof_deps is their union, and proof_origin
   names the proved source tools. All other node fields remain the repository's.
   Verdict: the node agrees with the delivered Lean and has no cycle introduced here.

Second reading changed the entire attempted restatement reduction into a closed
proof using existing tools, removed its component module/node, and corrected the DAG
and report. The existing theorem docstring and signature were preserved.
