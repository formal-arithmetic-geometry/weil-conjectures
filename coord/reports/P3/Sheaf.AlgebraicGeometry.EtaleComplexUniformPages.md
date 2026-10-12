## What changed
Replaced the entire proof of `AlgebraicGeometry.Etale.exists_etaleComplex_uniform_pages`
without changing its signature. The proof constructs canonical derived pullback maps in
all degrees and checks the supplied degree-p map using `hP`. It obtains functorial
presentations with quantitative stabilization thresholds, assembles their coordinate-swapped
diagram, chooses `N = max 1 (max (q-a+2) (p-q+2))`, and composes the page and convergence
isomorphisms. The final transition and limit cokernel equations are proved by composing
the two naturality squares and using associativity.

Added three modules with matching nodes. `EtaleComplexColimitBelow` is fully proved using
preservation of zero objects by inverse image, evaluation of complex colimits, and
`IsColimit.isZero_pt`. `EtaleHypercohomologyUniformBound` isolates global quantitative
convergence. `EtaleComplexPageDiagram` isolates diagram functor laws and coordinate
transport, with no convergence or filtration assertion. The latter two remain separate
items for proof. All choices in the target are local existential elimination; no
new data definition chooses an arbitrary witness from an unproved existence theorem.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.Etale.exists_etaleComplex_uniform_pages`
(node `lem-weil-pbc-etale-complex-uniform-pages`) by decomposition into two strict parts.
This is a decomposition, not a sorry-free proof; one upper hole is closed and two holes
are added (net -1).

Proved `AlgebraicGeometry.Etale.etaleComplex_colimit_below`
(node `lem-weil-pbc-etale-complex-colimit-below`) without any direct hole.

The only delivered holes are:
- `AlgebraicGeometry.Etale.exists_etaleHypercohomology_uniform_bound`
  (`lem-weil-pbc-hypercohomology-uniform-bound`): global presentations and the explicit
  support estimate; no diagram, colimit, or coordinate swap.
- `AlgebraicGeometry.Etale.exists_etaleComplex_page_diagram`
  (`lem-weil-pbc-etale-complex-page-diagram`): diagram assembly and swap, from supplied
  functorial presentations; no stable-page or filtration comparison.

Both are public named theorem proofs exactly `:= by sorry`, with full proof plans in
their docstrings and DAG nodes. The quantitative bound handles unsupported bidegrees
as well as nonzero ones; its maximum with 1 also handles zero complexes. The diagram
construction needs no finiteness of I. The colimit lower-bound proof works for any
index category admitting the supplied colimit.

## No longer needed
Removed the target's direct proof imports
`Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`,
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`, and
`Mathlib.Algebra.Homology.HomologicalComplexLimits`, and the redundant
`Sheaf.CategoryTheory.HypercohomologyFirstPage` proof import. The first two remain dependencies
of the quantitative-convergence node and are therefore not globally pruned. The last
is already publicly imported by the presentation definition; its direct import was redundant. No original DAG node or module is
claimed globally unnecessary. The original three planned dependencies remain below
the new quantitative-convergence node.

## Where the brief, the DAG or earlier work was wrong
The previous attempt stopped after finding no direct indexed presentation theorem.
The planned construction does admit a strict decomposition into a quantitative global
presentation theorem and a diagram/coordinate transport theorem. The existing
`exists_etaleHypercohomology_pullback_functorial` gives object-dependent stabilization
thresholds; an explicit uniform estimate is additional theory, not an immediate
application. Arbitrary first-page witnesses would not suffice for the later filtration
compatibility; this delivery keeps the presentations and all page maps tied together.

The assigned node's unit is `sk-prop-h2`, whose `realized` statement and step lists are
empty. The decomposition changes no unit statement or step and keeps all three
original proof dependencies below it. LeanSearch was unavailable (Internal Server
Error); LeanFinder, Loogle and source grep were attempted and recorded.

## New nodes
`lem-weil-pbc-etale-complex-colimit-below` records the proved degreewise lower bound.
`lem-weil-pbc-hypercohomology-uniform-bound` records the global quantitative convergence
part of the original proof plan.
`lem-weil-pbc-etale-complex-page-diagram` records diagram assembly, first-page
naturality, vanishing, and natural coordinate-swap isomorphisms on every page.
No interface changes or forced adaptations are included.

## Second reading by P3
1. Compared the target module with the repository by diff and checked its entire theorem
   signature byte for byte: identical. No existing definition, statement, docstring,
   visibility or public import changed. The other three modules are new; there are no
   forced adaptations or change records. Verdict: pass.
2. Inspected every delivered proof and scanned for forbidden declarations and attributes.
   The target contains a genuine reduction: degreewise colimit boundedness, canonical
   derived maps, a common threshold, and composition of both naturality squares.
   No data definition or arbitrary global witness choice was introduced. The only direct
   sorries are the two reported named public theorems. Compilation and axiom checks
   are recorded below. Verdict: pass.
3. Read both split statements and their word proofs. The bound uses the unswapped
   differential (r,1-r): its outgoing target is unsupported when r>n-q+1, and its
   incoming source when r>q-a. The displayed bound is safely larger than both.
   Checked q<a, n-q<0, zero complexes, the bottom row q=a and resolution degree zero;
   unsupported terms and their graded pieces are zero, and the maximum with 1 gives
   a valid page. The diagram lemma requires neither colimit preservation nor convergence;
   its hypotheses provide precisely the first-page maps and the identity/composition
   laws needed for functor and cocone assembly. It is strictly a transport part of the
   target; the quantitative lemma is strictly its presentation/convergence part.
   Independent LeanFinder and Loogle searches and source searches found tools, not a
   duplicate theorem. Inspected HypercohomologyConvergence, FilteredResolutionMaps,
   PullbackFunctorial and SpectralSequence.Basic. Neither hole has a short existing proof.
   Verdict: pass as decomposition, with net holes closed minus added equal to -1.
4. All new imports needed only for the target proof are plain imports. Removed direct
   proof imports are listed above; no module is claimed globally pruned. The old direct
   dependencies lem-weil-pbc-hypercohomology-e1-pullback-functorial, thm-sp-if-e1 and
   thm-sp-spectral-object-yields are no longer direct target dependencies, and remain
   under the quantitative lemma. Checked the sk-prop-h2 unit record (its source section is absent locally):
   no realized statement or step is bypassed or changed. Verdict: pass.
5. Checked all four nodes against their Lean declarations and the actual reduction.
   Corrected the page-diagram node: the upstream existence theorem is a statement
   reference describing its hypotheses, not a proof dependency. Its proof uses the
   supplied hfirst/hid/hcomp, so removed that proof edge and marked the construction
   elementary. Its statement dependencies remain intact. New nodes include source,
   detailed proof, searches, provenance, blueprint, chapter/unit and Lean records.
   Verdict: pass after correction.

Second reading changed only DAG proof-dependency metadata, added independent search
records, and corrected the report's explanation of the redundant first-page import.
The Lean proofs and all signatures were kept.

Axiom probes for the colimit theorem list exactly propext, Classical.choice and
Quot.sound. Each new open theorem lists only those plus sorryAx. The initial full
compile and target probe hit the 60-second limit while host load exceeded 160;
the first worker's earlier clean compile took 37.2 seconds. Final delivery-tool
compilation and axiom validation are recorded by its output.

Final dry run: deliver3.py --no-push printed OK at 53954ab30c. All four modules
compiled without warnings and the tool's per-declaration axiom probes and stage-3
preflight passed. Review class CODEX because this decomposition adds modules and nodes.
The retry succeeded under the unchanged 60-second per-file limit; no timeout bypass
or proof split for compilation was used.
