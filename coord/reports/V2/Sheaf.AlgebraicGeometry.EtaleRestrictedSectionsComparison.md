## What changed

`Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparison` now proves
`AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_isIso` by the degreewise
isomorphism criterion `HomologicalComplex.Hom.isIso_of_components`.
The new module `Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso`
contains the remaining degreewise finite-diagonal comparison. It states the
factorization directly, so it imports Factors and creates no import cycle.
The original module imports this helper with plain `import`: it is proof-only.
All existing declaration signatures, definition bodies and public imports are unchanged.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_isIso`, node
`lem-weil-pbc-etale-restricted-sections-lift-isIso`.
Added one named hole in the new module:
`AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_component_isIso`, node
`lem-weil-pbc-etale-restricted-sections-lift-component-isIso`.
This is a decomposition: one hole closed, one added, net zero. It isolates
invertibility in one degree from constructing the inverse chain map.
There are no sorries left in the assigned module.
`etaleRestrictedSectionsLift_arrow` and `etaleRestrictedSectionsLift_unique`
were already proved in the repository baseline; they are unchanged and are
not counted as holes closed by this delivery. The pre-existing imported
`etaleRestrictedSections_factors` remains open and is not delivered here.

## No longer needed

No imports removed and no modules pruned. The original isIso node no longer
uses `def-weil-pbc-etale-restricted-total-construction` or
`def-weil-pbc-etale-restricted-sections-lift` as direct proof dependencies;
its proof dependency is now the new component lemma. These definitions
remain necessary in the component lemma and/or the upper statement, so
neither node is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The first report described an older baseline: the module is now present in
sheaf-dag, and the arrow and uniqueness proofs have already landed. It also
claimed the original isIso theorem remained sorry, although the delivered
code had replaced that hole. The first delivered isIso node still recorded
the old argument and dependencies. The component theorem had no explicit
source in its docstring, an incomplete proof explanation, and no separate
module. These issues are repaired. Tag 015J supplies the CE total/sections
context; the restricted finite-summand calculation is the specialization
spelled out in the new docstring, not a verbatim assertion of that source.

## New nodes

`lem-weil-pbc-etale-restricted-sections-lift-component-isIso` is the
finite-diagonal comparison in a fixed degree, stated in its own module.
Its docstring explains injectivity, the image sum, the filtration formula,
the canonical sections comparison and uniqueness of the factorization.
The node records these dependencies and renewed searches. No change record
is needed because no existing statement, definition or public import changes.

## Second reading by V2

1. PASS. Diffed every sandbox module against the repository. Removed the
   identical Factors and TotalConstruction copies from the delivery. The only
   change in the assigned module is a proof-only import and the final proof;
   every existing signature and definition body is byte-for-byte unchanged.
   Restored the original final-theorem docstring. No interface change record
   or forced adaptation is needed.
2. PASS. Both delivered modules compile locally through lcompile.py without
   errors or warnings. A scratch copy with #print axioms checked the lift,
   arrow equation, uniqueness, final theorem and component lemma: only
   propext, Classical.choice, Quot.sound and expected sorryAx occur.
   The sole delivered sorry is the named component theorem. No forbidden
   declarations or hollow definitions occur. The lift's unproved factorization
   property determines its data uniquely by monic cancellation.
3. PASS. Read the component statement against the actual secondFiltration
   finite image-sum definition and the mapped-total construction. It is a
   fixed-degree statement; the upper proof supplies the compatible inverse
   chain map using Mathlib. Checked empty diagonals n < q, arbitrary negative
   bounds, zero summands, and n = q (the single resolution-degree-zero term).
   Its full docstring proof and node agree. Repeated Loogle, LeanFinder and
   grep searches with different queries, plus library searches; generic
   component/isomorphism and direct-sum lemmas do not close this comparison.
   The recorded unavailable LeanSearch attempt is retained transparently.
4. PASS as a decomposition, not net progress. The upper proof uses the shortest
   Mathlib component criterion. Factors is needed publicly by the exposed
   lift definition; the new helper import is proof-only. The helper needs
   Factors publicly to state its factorization. Both old direct dependencies
   are accounted for above. Read dag/units/sk-prop-h2.json: its realized fields
   contain no entry for these auxiliary nodes; no unit statement or step is
   bypassed and that record is unchanged.
5. PASS after repair. Updated the original node's proof, proof_deps and
   proof_origin to the actual component criterion. The new node has all
   required fields, a verbatim Lean signature, the new module path, matching
   statement/proof dependencies, source, creation record and searches.

Changes made in this reading: moved the new degreewise theorem into its own
module without an import cycle, expanded its source/proof docstring, restored
the original theorem docstring, corrected DAG routes and metadata, removed
unchanged delivery copies, and rewrote the report to state the exact baseline
and net hole count. Local axiom checks and both module compiles passed.
