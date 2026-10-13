## What changed

KInjectiveSectionCycleComparison now proves its public theorem from a constructed
cycle-quotient isomorphism and the canonical bottom-comparison cycle formula. The
private section_cycles_cokernel_iso is fully proved: map the kernel, identify the
induced boundary map, use the actual cokernel as left homology data, and check its
cycle formula. The parent then identifies the displayed cokernel.desc with a
composite of isomorphisms by cancelling cokernel.pi. Its signature and all existing
public imports are unchanged. One proof-only import was added:
Sheaf.AlgebraicGeometry.DerivedLowerTruncationCycleFormula.

## Proved and sorry left

Closed: AlgebraicGeometry.kInjective_section_cycle_comparison
(lem-sc-kinjective-section-cycle-comparison), 1 of 1 original holes.
The private section_cycles_cokernel_iso is proved without sorry.
Added and left: AlgebraicGeometry.derived_lower_truncation_cycle_formula
(lem-sc-derived-lower-truncation-cycle-formula), in its own new module.
This is a decomposition, not a net reduction of holes: one closed, one added.
Both delivered modules compile together through lcompile.py --all without warnings.
The remaining statement has neither K-injectivity nor the parent's invertibility
hypothesis, and asserts a normalized bottom comparison on arbitrary complexes.
It does not assert invertibility of the cycle quotient. The parent's proved kernel
calculation and use of its two invertibility hypotheses are necessary to obtain
that conclusion. No data definition is extracted from an unproved existence theorem.

## No longer needed

No imports or modules pruned. The planned new-qcoh-sections-left-exact-bottom
is no longer a direct dependency of the parent, but remains a planned dependency
of the new canonical normalization node; do not prune its module. The K-injective
comparison dependency remains, supplied by the imported right-derived unit instance.
The unit's realized lists are empty, and no unit statement or route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned bottom lemma rightDerivedFunctor_truncated_bottom supplies a natural
isomorphism but no compatibility with rightDerivedFunctorUnit or the actual cycle
quotient. Using an arbitrary isomorphism would not identify the canonical map.
The new node isolates exactly this normalization requirement. The other planned
K-injective comparison is already implemented by the instance in the source
RightDerivedFunctor.Defs module.

Read the official Stacks pages for Tags 05TC, 0AVW and 08D4; the local literature
bodies are absent on this machine. 05TC gives upper-truncation invariance and
negative vanishing, while 0AVW explicitly omits the canonical cohomology detail.
The new node marks the expanded normalization argument as agent-written.
Searches also read HypercohomologyLeftEdgeCanonical: its natural-index and
Grothendieck hypotheses prevent direct use for this arbitrary abelian statement.

Edge cases checked for the new statement: F the identity or an exact functor
reduces the formula to the usual homology quotient; I=0 gives the unique zero
maps; a single object in any integer degree reduces to the canonical R^0F
comparison. General complexes may have a noninvertible edge map: the new theorem
makes no claim that it is invertible. No changes or forced adaptations elsewhere.

## New nodes

lem-sc-derived-lower-truncation-cycle-formula records the normalized bottom
comparison and its formula on arbitrary cycles. It has its own module, named
sorry theorem, verbatim Lean signature, source, complete proof in words, and
logged LeanSearch/LeanFinder/grep searches. The parent node's proof, proof_deps,
and proof_origin now follow the compiled reduction. No change records needed.

## Second reading by S3

1. Compared the delivered parent module and node with the repository using diff.
   The existing public theorem signature, hypotheses, conclusion, visibility,
   definitions and public imports are unchanged. The only new parent import is
   proof-only. No change record or forced adaptation is needed. Restored the
   original whitespace immediately before the theorem proof.
2. Compiled both modules in dependency order with lcompile.py. Inspected every
   proof, including the explicit mapped-kernel/cokernel construction: no hollow
   definitions, arbitrary chosen data, forbidden declarations or hidden holes.
   The sole new sorry is the reported public theorem
   AlgebraicGeometry.derived_lower_truncation_cycle_formula. Scratch-copy axiom
   probes passed: the private helper uses only propext, Classical.choice and
   Quot.sound; the parent and remaining theorem additionally use sorryAx.
   No other axioms occur.
3. Read the new theorem, its node and full docstring argument. Its bottom
   isomorphism exists without K-injectivity; the equation is the canonical
   normalization of that isomorphism, not invertibility of the edge map.
   Checked the zero complex, identity/exact functors, a single object in an
   arbitrary integer degree, and complexes with nonzero incoming boundaries.
   The latter require a quotient by F(boundaries), exactly as the proved helper
   constructs; no preservation of cokernels is assumed. Left exactness and the
   bounded-below lower truncation suffice for the bottom calculation, even when
   I itself is unbounded. Re-read Stacks Tags 05TC, 0AVW and 08D4 online. The
   normalization argument is correctly marked agent-written. Independent
   LeanFinder, Loogle and grep searches (logged in searches.jsonl), plus local
   searches for derived-unit/homology and cycle/truncation compatibility, found
   only component formulas. HypercohomologyLeftEdgeCanonical has stronger
   Grothendieck hypotheses and natural indices. The remaining lemma is a
   strictly smaller compatibility problem, not a renamed parent conclusion;
   it could not be closed by an existing theorem in a short pass.
4. Read the parent from its conclusion downward. Cokernel epimorphism
   cancellation identifies the actual map with the composite of isomorphisms;
   K-injectivity and the parent's IsIso hypothesis are both used. The kernel
   calculation is fully proved using Mathlib universal properties. No unused
   added proof import was found; existing public imports retain the interface.
   No longer needed lists the removed direct DAG dependency
   new-qcoh-sections-left-exact-bottom, retained in the new node's plan. No
   modules are pruned. Checked dag/units/sk-thm-picard-duality.json: its realized
   statement and step lists are empty; no realized unit route was bypassed.
5. Checked the node diffs: the existing node changes only proof, proof_deps and
   proof_origin. They follow the kernel calculation, K-injective unit instance,
   cycle formula and cokernel cancellation. The new node has its source,
   complete proof steps, searches, provenance, chapter/unit and verbatim Lean
   statement. The report correctly counts one original hole closed and one
   new hole added, hence a decomposition with zero net holes closed.

Changes by this reader: restored original proof-separator whitespace and added
this independent review. No mathematical or interface repair was necessary.
