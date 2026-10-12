## What changed

Proved `AlgebraicGeometry.Etale.exists_etale_complex_class_eq_zero` without changing its
signature. The proof inducts through the image filtration, composes the successive arrows,
uses cocone naturality to maintain limit vanishing, and cancels the stage cohomology
isomorphism at the final step. The integer bound also handles `p < a` without a separate
case or a nonempty-stage choice.

Added `EtaleHypercohomologyFiltration` with a real definition of membership in the image
filtration: an image from any complex supported above the filtration degree. Maps from such
complexes factor through the stupid truncation, so this is the usual first-spectral-sequence
filtration. Added `EtaleComplexFiltrationDeepening` for the one-step graded comparison.
These are strict pieces of the original argument, rather than its conclusion renamed.
The original node now records the actual induction and its two inputs. The high-filtration
vanishing input is proved directly from existing tools, leaving just one new sorry.

All three modules compile without warnings using `lcompile.py --all`. New statements were
checked on zero complexes, negative degrees, `q > p`, and the boundary `q = p`: the zero
lemma requires strict inequality, and deepening advances exactly one step. The terminal
bound is `a + (p-a+1).toNat > p`.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.exists_etale_complex_class_eq_zero` (the only original
sorry). No sorry remains in the assigned module.

Also proved: `AlgebraicGeometry.Etale.eq_zero_of_inEtaleHypercohomologyFiltration`.
It uses a bounded-below injective replacement with the same support bound, K-injectivity,
and the source-library computation of the total right derived functor on that replacement.

New remaining sorry:
- `AlgebraicGeometry.Etale.exists_etale_complex_class_in_next_filtration`, node
  `lem-weil-pbc-etale-complex-filtration-deepening`.

The remaining sorry is a public named theorem in its own module, with a source citation
and complete proof in its docstring. The filtration definition contains no postponed data or proof.

## No longer needed

Removed these direct proof imports from the assigned module:
- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.KInjectiveBridge`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`

Their associated original proof dependencies are needed by the new one-step theorem,
whose proof imports retain them. Thus no original node or module is globally pruned;
they have moved below the new intermediate step. No public import of the assigned module was removed. In the new deepening module,
`Mathlib.Algebra.Homology.HomologicalComplexLimits` is a plain proof import: its
termwise-colimit facts do not occur in the statement.
The original node directly needs only the two new nodes; its original nine direct
proof dependencies now occur below these nodes. No blueprint unit statement or step is
bypassed (`sk-prop-h2` does not mark this node as realizing one of its steps).

## Where the brief, the DAG or earlier work was wrong

The available spectral-sequence statements do not directly expose the one-step
image-filtration lifting interface needed for the original elementwise vanishing proof.
The gap is isolated as the deepening theorem. The general comparison theorem includes
surjectivity and the full finite-filtration argument; importing the full complex-continuity
module would create an import cycle because it already uses this theorem.

The Stacks source file named by the node is absent from this clone. Read the official
[0EZM](https://stacks.math.columbia.edu/tag/0EZM) and
[015J](https://stacks.math.columbia.edu/tag/015J) pages instead. The former omits the
finite-term details; the new theorem docstrings expand those details. No mathematical
error in the original statement was found, and no existing definition or signature changed.

## New nodes

`lem-weil-pbc-etale-hypercohomology-filtration-zero` records the explicitly defined
image filtration and its proved vanishing above total degree, in
`lean/Sheaf/AlgebraicGeometry/EtaleHypercohomologyFiltration.lean`.

`lem-weil-pbc-etale-complex-filtration-deepening` records a single graded comparison
step, in `lean/Sheaf/AlgebraicGeometry/EtaleComplexFiltrationDeepening.lean`.
It retains the original termwise continuity, directed reindexing and functorial
spectral-sequence route. No change record is required.

## Second reading by D2

1. Compared every delivered module with the repository. The two helper modules are new;
   the original module differs only in its private proof imports and theorem body. Its
   complete original theorem signature is byte-for-byte identical. No existing definition,
   public import or target signature changes, and no change record is required. Verdict: pass.
2. Compiled all three modules locally in import order without errors or warnings. Inspected
   every declaration and scanned for forbidden constructs: exactly one `sorry`, the named
   deepening theorem listed above; no hollow definition or forbidden declaration. Scratch
   `#print axioms` checks gave only `propext`, `Classical.choice`, `Quot.sound` for both the
   filtration definition and its zero theorem. The assigned theorem and the open deepening
   theorem additionally use `sorryAx`; thus this delivery closes the original proof body
   conditionally on the named open step, rather than completing the target closure.
   Verdict: pass for a partial stage-3 delivery.
3. Read the split-off statement against [0EZM](https://stacks.math.columbia.edu/tag/0EZM)
   and [015J](https://stacks.math.columbia.edu/tag/015J). The witnesses define precisely
   the image of the stupid truncation: maps factor through it, including the boundary
   complex-map equation, and its inclusion supplies the converse. The new open theorem
   advances a single graded step; it does not conclude eventual zero. Its source, complete
   natural-language proof and node are present. Checked zero complexes/classes, all integer
   q, the identity system, q>p (already zero), q=p (one genuine final step), and p<a
   (the induction uses zero steps). The zero theorem correctly requires p<q; a complex
   concentrated in degree p rules out replacing this by p≤q. Repeated searches using
   LeanFinder for graded-colimit injectivity, Loogle for stupid truncation, and Mathlib grep
   for brutal/stupid truncation and filtration steps, plus source-library searches for
   derived connectivity and existing image filtrations. Found truncation infrastructure and
   ordinary filtered-colimit injectivity, but no existing etale one-step theorem. The
   upstream hypercohomology filtrations use canonical truncation and a different E2 route.
   The remaining step requires construction and functorial comparison of the spectral
   sequences, so cannot be closed by a few-minute application. Verdict: pass.
4. Read the induction from the original conclusion downward: initial identity witness,
   cocone naturality, canonical vanishing via hB, one-step deepening, arrow composition,
   the integer bound, proved high-step vanishing, and inverse-isomorphism cancellation.
   No shorter existing theorem found; the full complex-continuity module imports this
   item and would be circular. Proof-only imports in the new deepening module are private,
   including the termwise-complex-limit import corrected during this reading. The unit
   `sk-prop-h2` has empty realization lists, so this item realizes no fixed unit step and
   none is bypassed. All nine old direct proof dependencies are no longer direct inputs:
   `def-sp-etale-dictionary`, `def-sp-kinjective-bridge`,
   `def-weil-pbc-etale-cohomology`, `lem-weil-pbc-complex-spectral-sequence-comparison`,
   `lem-weil-pbc-etale-cohomology-limit-of-schemes`,
   `lem-weil-pbc-filtered-category-directed-cofinal`,
   `lem-weil-pbc-hypercohomology-e1-pullback-functorial`, `thm-sp-if-e1`,
   `thm-sp-spectral-object-yields`. They remain in the route of the new open deepening
   node; the dictionary is a convention node, and derived cohomology is supplied by
   the public source imports. No old node or module is globally pruned. Verdict: pass.
5. Compared all Lean declarations with their node records. Original proof metadata
   faithfully records the induction and two helper inputs; new records have the required
   source, creation, blueprint, chapter, unit, search and Lean fields, with verbatim
   theorem signatures. Dependency lists equal the unions of step uses. Corrected the
   deepening node to record explicitly the etale dictionary and derived-cohomology
   identification omitted from its earlier route. Verdict: pass after that repair.

Second reading changed only the deepening module's termwise-limit import from public
 to private, the deepening node's two missing route dependencies and their explanation,
 and this report. No proof body, signature or definition needed repair.
