## What changed

Proved `ModuleCat.localizedTensorComparisonProperty_triangle_core` from a new
exact-diagram construction and Mathlib's five lemma, without changing its signature.
A proved private helper constructs K-flat representatives using the source library's
functorial flat resolution, and converts K-flatness to the explicit acyclic-tensor
hypothesis. Existing model existence supplies models for these representatives.
The proof evaluates h1 and h2 in degrees i and i+1, transports their four IsIso proofs
through arrow isomorphisms, applies the five lemma, and transports the middle result
back to the prescribed mU. All proof imports are non-public.

The new module `Sheaf.Algebra.Homology.LocalizedTensorComparisonTriangleFiveTermDiagram`
states the missing construction for arbitrary fixed representatives and models.
It assumes neither h1 nor h2 and asserts no vertical-map invertibility. Its docstring
and node explain the cone construction, connecting-map signs and model transport.
The parent node's proof and proof_deps now follow the actual Lean reduction.

## Proved and sorry left

Closed the only original hole:
`ModuleCat.localizedTensorComparisonProperty_triangle_core`
(node `lem-pc-localized-tensor-comparison-closure-triangles-core`).
No sorry remains in the original module; its private representative helper is proved.

Added one hole:
`ModuleCat.exists_localizedTensorComparison_triangle_five_term_diagram`
(node `lem-pc-localized-tensor-comparison-triangle-five-term-diagram`).
This is a decomposition, not a complete proof of triangle closure: one upper hole
is replaced by one construction hole. The remaining statement is strictly a part of
the argument: it constructs the exact diagram independently of the vertex comparison
hypotheses; all four outer isomorphism arguments and the five-lemma deduction are
implemented in the original module. No definition, axiom or target signature changed.

Both modules compile together via lcompile.py. All Lean lines are at most 100 characters.
The construction was checked conceptually on zero rings and complexes, split triangles,
arbitrary t (including zero), arbitrary degrees and unbounded Q and N: it asks only for
exact rows and commuting squares, never invertibility for arbitrary t. Flatness is used
only to extend the source exact sequence; the target uses scalar extension of K-flat
representatives, so it adds no flatness or K-flatness assumption on N.

## No longer needed

Removed the original module's direct proof import
`Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator`; its use belongs to the diagram
construction, which retains this import and node in its proof plan. This is not global
pruning: no original dependency module or node is claimed to leave the target closure.
The original core now depends directly on the new diagram node and the existing
Mathlib leaf `lem-weil-pbc-five-lemma` as well as the defining/model nodes.
No separate shift-property lemma is needed: h1 and h2 already quantify over all degrees.
The unit's realized lists are empty; no prescribed unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node says to tensor the distinguished triangle with U; the fixed second
factor is Q. U represents only the third vertex. The proof route now makes this explicit.
The original dependency list gives models and an associator but no Lean declaration
constructing their exact comparison diagram. This is the construction split off here.
The Stacks text of 0DJA(1) uses tensor transitivity; 09PB explains the localizing-property
argument. The five-lemma closure argument is the project's expansion of that route,
not a literal five-lemma proof in Tag 0DJA. The source tags were read on the Stacks site
because literature files are absent from this read-only clone.

`LocalizedTensorComparisonRepresentativeSquare` is present in the source tree but its
compiled artifact was unavailable during the attempted import. It is recorded as a
planned dependency of the remaining construction; it is not imported for the currently
proved reduction and was not duplicated or modified. No other module was adapted.

## New nodes

`lem-pc-localized-tensor-comparison-triangle-five-term-diagram`:
constructs two exact five-term rows and their morphism, identifying the five vertical
arrows with the prescribed model comparisons. It removes all isomorphism hypotheses
and conclusions from the parent's construction subproblem. One new public statement,
one new module, one sorry, complete cone-and-transport proof in words. Its searches
found the general five lemma but no specialized comparison diagram.
No change records are needed because all existing statements and definitions are unchanged.

## Second reading by M1

1. **Existing interfaces: pass.** Diffed the core against the repository version:
   both public imports, the universes and shared variables, the existing docstring,
   and the complete signature of
   `ModuleCat.localizedTensorComparisonProperty_triangle_core` are unchanged.
   The only additions are non-public proof imports, a private proved helper and
   the theorem body. No existing definition or target changed; no change record
   is required. The new diagram has its own module and node.

2. **Proof and axioms: pass as a decomposition.** Compiled both modules together
   with `lcompile.py --all`, without errors or warnings. Read the representative
   helper and each of the four arrow-isomorphism transports: h1 supplies degrees
   i and i+1 of vertex 1, and h2 supplies those degrees of vertex 2. Mathlib's
   `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` supplies the middle component;
   the component-2 arrow isomorphism transports it to precisely the original goal.
   A scratch copy with `#print axioms` showed only propext, Classical.choice and
   Quot.sound for the private representative helper. The core and diagram theorem
   additionally show sorryAx, as expected from the sole remaining construction
   hole. No forbidden declaration, holed definition or additional sorry occurs.
   The resolution choice occurs locally in a proof of existence, not in a new
   definition choosing arbitrary data from an unproved existence theorem.

3. **Split statement: pass.** Read the diagram signature, docstring and node,
   the full model definition, the representative-square theorem, the derived
   second-factor functor and K-flat associator. Independently consulted
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6),
   [0BYJ](https://stacks.math.columbia.edu/tag/0BYJ) and
   [0DJA](https://stacks.math.columbia.edu/tag/0DJA).
   The new statement constructs exact rows with five specified comparisons as
   their vertical maps; it assumes neither vertex comparison property and
   concludes no invertibility. Thus it is a proper construction subproblem,
   not the original isomorphism claim under a new name. For a split triangle
   the rows are split exact; for zero complexes and zero rings they are zero;
   for t=0 the vertical morphism is zero, which the statement permits. For
   arbitrary unbounded N, K-flatness of the extended first factors, not flatness
   or K-flatness of N, computes the target. Source exactness uses precisely hC.
   The connecting-map argument uses cone inclusion/projection and their matching
   tensor-shift signs; representative squares then transport to the arbitrary
   prescribed models. These are the obligations of the open construction, not
   claims that its Lean proof is complete. Independent msearch queries used
   `natural transformation derived tensor exact functors connecting homomorphism
   long exact cohomology sequence` (leanfinder),
   `HomologicalComplex.HomologySequence` (loogle: identifier unavailable), and
   `localizedComparison.*Exact|comparison.*homologySequence|exists_kFlat_iso`
   (grep: no hits); direct rg additionally found the upstream representative
   theorem and general homology-sequence machinery, but no specialized diagram.
   The remaining construction cannot be completed in a few minutes.

4. **Route and pruning: pass.** Checked the shortest existing five-lemma route
   and `DerivedCategory.exists_kFlat_iso` in the upstream Monoidal.Shift module.
   That theorem returns a homotopy-category representative and needs its generic
   monoidal/derivability structures; it would still require the quotient-to-cochain
   conversion and acyclic-tensor conversion here. Retained the direct reduced
   resolution helper and its narrower imports. Public imports are needed by the
   statement. The diagram's non-public imports retain the stated construction
   plan; its representative-square dependency is recorded in the DAG but was
   unavailable as a compiled import during the first worker's work. Of the old
   core proof_deps, the model node remains directly used and the associator node
   is now used in the diagram's construction rather than directly in the core.
   This is exactly the removal recorded under No longer needed; no module is
   globally pruned. Opened `dag/units/sk-thm-picard-semicon.json`: its realized
   statement and step lists are empty, and no unit record or prescribed route
   is changed.

5. **DAG agreement: pass.** Parsed both node files. Their proof_deps are exactly
   the union of their step uses, all referenced nodes exist, and both recorded
   Lean signatures occur verbatim in their modules. The existing node changes
   only proof, proof_deps and proof_origin. The new node has the required source,
   searches, creation, blueprint ancestry, chapter/unit and Lean records.
   Its five construction steps account for exactness, comparison compatibility
   and representative/model transport; the parent records the actual six-step
   Lean reduction. No new node duplicates a result found by the independent search.

Second reading changed: added a source-and-proof docstring to the private proved
representative helper and this independent review. No mathematical statement or
proof body needed repair. One original hole closed, one construction hole added:
net zero, explicitly a decomposition, with no global pruning.
