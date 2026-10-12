## What changed

Completed the proof of CategoryTheory.Functor.cochainHypercohomologyLeftEdge_single_aux
from two separate parts of the single-complex argument. The new theorem
hypercohomologyLeftEdge_truncation is fully proved: it computes the spectral edge using
naturality of the truncation projection and cancellation of the truncation inclusion.
The new explicit isomorphism rightDerivedSingleDegreeComparison is the shift and
classical degree-zero part of the existing target isomorphism, with concrete data.

The original module constructs the canonical morphism to the degree-n single object,
proves its homology normalization, transports the mapped cycle representative through
extension by zero, applies the remaining unit normalization, and cancels the homology
comparison isomorphisms. All original signatures, section hypotheses and public imports
are preserved. Two proof-only imports were added to the item. The remaining unit module imports the
already proved degree-zero unit comparison for its documented proof plan. There are no forced adaptations.

## Proved and sorry left

Closed one original hole:
CategoryTheory.Functor.cochainHypercohomologyLeftEdge_single_aux
(node lem-pc-hypercohomology-left-edge-single-aux).

Fully proved the new theorem CategoryTheory.Functor.hypercohomologyLeftEdge_truncation
(node lem-pc-hypercohomology-left-edge-truncation). The definition
CategoryTheory.Functor.rightDerivedSingleDegreeComparison has no hole
(node def-pc-right-derived-single-degree-comparison).

Added one hole, the only sorry in this delivery:
CategoryTheory.Functor.rightDerivedFunctorPlusUnit_single_degree
(node lem-pc-right-derived-unit-single-degree,
module Sheaf.CategoryTheory.RightDerivedUnitSingleDegree).
Its proof is exactly `by sorry`; its docstring and node contain the complete argument.
This is a decomposition, not a claim of a net decrease in reachable holes:
one original hole closed and one strictly smaller unit-normalization hole added.
The latter has no spectral object, edge or truncation maps. It works for any supported
integer-indexed complex and any identification inducing the identity on its sole homology.
The spectral calculation, the normalization of the constructed identification, and the
extension transport are proved here, rather than moved into that hole.

The support and normalization assumptions were checked on the zero coefficient and on
n=0: all comparisons remain defined, the identity of a zero object is zero, and the
shift in degree zero is the canonical zero shift. No acyclicity of the coefficient is
required. Compiler checks use the project's lcompile.py, in dependency order.

## No longer needed

No original imports, nodes or modules are pruned. The existing dependency
 def-pc-hypercohomology-left-edge remains needed. The new unit module and comparison
module do not import HypercohomologyLeftEdge or any spectral-object module: their
interfaces use only the bounded-below derived functor and ordinary homology comparisons.
The proof-only imports of the original module are both used.

## Where the brief, the DAG or earlier work was wrong

The previous attempt did not compile: the mapExtendIso component calculation needed
the explicit mapExtendX_hom_eq lemma; the homology transport needed mapCochainComplexPlus
unfolded; the final inverse cancellation needed the local embedding abbreviation unfolded.
These three errors and a long-line warning have been repaired.

The original single-aux plan compressed two separate computations into one step:
truncation-edge factorization and normalization of the derived unit. The former is now
proved in Lean; the latter is the remaining item. Merely knowing a comparison is an
isomorphism does not prove its compatibility with the derived unit.

The local literature/stacks-project/derived.tex file is absent on this machine. The
cited source was read at https://stacks.math.columbia.edu/tag/015J and
https://stacks.math.columbia.edu/tag/015N. The explicit comparison equations are an
agent-written expansion of the single-complex specialization, not verbatim statements
of those tags. LeanSearch returned HTTP 500; that search is recorded as unavailable,
without a verdict of absence. LeanFinder, Loogle and local source searches were usable.
The earlier search overlooked the proved
CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison in
Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison
(node lem-sbc-right-derived-single-unit-homology-comparison). The remaining unit lemma
now cites and imports it: only its transport to a normalized supported complex and a
nonzero degree remains, rather than a second degree-zero computation. It is a closed
tool from another unit and does not replace this unit's route. The unit record has no
realized statement or step nodes to bypass.

The inherited auxiliary node has incomplete blueprint ancestry; the new nodes name the
existing ultimate ancestor recorded by the left-edge definition and preserve the unit.

## New nodes

- def-pc-right-derived-single-degree-comparison:
  lean/Sheaf/CategoryTheory/RightDerivedSingleDegreeComparison.lean; concrete natural
  isomorphism obtained by shifting the existing degree-zero comparison.
- lem-pc-hypercohomology-left-edge-truncation:
  lean/Sheaf/CategoryTheory/HypercohomologyLeftEdgeTruncation.lean; the spectral part,
  fully proved for any nonnegative object bounded above in the edge degree.
- lem-pc-right-derived-unit-single-degree:
  lean/Sheaf/CategoryTheory/RightDerivedUnitSingleDegree.lean; the remaining derived-unit
  normalization on integer-indexed supported complexes, with no spectral edge.

No existing interface changes and no change records.

## Second reading by A3

1. Compared the delivered original module and existing node with the repository using
   diff. The existing theorem signature is byte for byte identical, including all section
   hypotheses; only its proof, a local elaboration option, and two plain proof imports
   changed. No definition or existing public interface changed. The existing node changes
   only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all four modules in import order with lcompile.py: no errors or warnings.
   A scratch import module printed the axioms of all four delivered declarations.
   The truncation theorem and concrete degree comparison use only propext,
   Classical.choice and Quot.sound. The original theorem and remaining unit theorem
   additionally use sorryAx, exactly as expected for the documented decomposition.
   A textual scan found only the named unit theorem's sorry and no prohibited commands.
   The comparison data is a concrete composite, with no arbitrary existence witness.
   Verdict: pass; not a completed sorry-free proof of the original item.
3. Read the split-off unit statement, docstring, node, degree-zero comparison theorem,
   full faithfulness of single functors, and commShift_rightDerivedFunctorPlusUnit.
   Support makes every differential zero and both cycle and homology identifications
   invertible. The normalization fixes f uniquely by faithfulness on pure objects;
   a is fixed by the mono cycle inclusion. Shifting transports the equation to the
   already proved degree-zero unit comparison, then the inverse/hom of R^0G ≅ G cancel.
   This covers n=0, a zero coefficient, and arbitrary non-injective coefficients.
   The statement is true and strictly isolates the unit part: no spectral edge,
   truncation or extension transport is hidden in it. Independent LeanFinder/Loogle
   searches with shift/compatibility terminology, and rg over the library, found no
   duplicate full statement. The shift and normalized-identification transport require
   substantial formal work; the hole is not a quick application of the degree-zero lemma.
   Read Stacks Tags 015J and 015N online; the precise normalization is correctly marked
   as an agent expansion of the canonical construction. Verdict: pass.
4. Read the proof downward: the truncation helper is an explicit naturality calculation;
   hf proves normalization, hc and hex prove the extension transport, and hu is used only
   for the remaining unit computation. All original proof dependencies are retained;
   no node or module is pruned. Both new plain proof imports are used. New public imports
   supply signature or definition ingredients; the unit comparison import is plain.
   dag/units/sk-thm-picard-rr.json has empty realized statement/step lists; its unit and
   chapter route are unchanged. Verdict: pass.
5. Checked all four node records against their Lean declarations and construction,
   proof dependencies, origin, source, ancestry, unit, and searches. The existing node's
   three steps match normalization, truncation/extension, and unit/cancellation in Lean.
   Each new node has the required creation and Lean metadata. Verdict: pass after the
   search-record correction below.

Changed only review metadata: corrected the three new nodes' stale grep results, which
had claimed no degree-zero unit compatibility existed despite the already reused proved
comparison, and recorded the independent second-reader searches. Added this review.
No Lean proof, signature, definition, import or hole count was changed by this reading.
