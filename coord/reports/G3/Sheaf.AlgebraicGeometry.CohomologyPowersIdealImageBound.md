## What changed

Replaced the original sorry in `AlgebraicGeometry.cohomology_powers_ideal_image_bound`
by a reduction from Rees finiteness. The proof cancels the monic image inclusion on
sheaves to prove transition/product compatibility, applies cohomology and the degree-zero
scalar formula, and uses homogeneous generation with d = max(c,n) and k = n+m-d.
A span/comap argument proves the range containment; natural-number arithmetic gives
the original exponent. The existing theorem signature and docstring are unchanged.

Added `Sheaf.Algebra.FiniteReesModuleGeneration` with the abstract algebraic
single-degree generation theorem. It has no scheme, properness, coherence,
transition maps, cohomology, or image-bound conclusion. Its import is proof-only.
Removed the proposed `CohomologyPowersIdealImageBoundAux` and `ReesFiniteData`:
the earlier proposal merely repeated the target with a redundant hypothesis.
No existing definition or statement changed; no change record is needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.cohomology_powers_ideal_image_bound` (one original hole).
Added: `AlgebraicGeometry.finite_rees_module_single_degree_generation`, the single
remaining named sorry, node `lem-weil-pbc-finite-rees-module-single-degree-generation`.
Its full informal proof and source are in its docstring and node.

This is a decomposition, not a completed proof: one hole closed and one added, net
zero holes before import pruning. The remaining algebraic generation argument is
strictly part (1) of the source argument; transition compatibility and the image
estimate, part (2), are formalized in the original module.

Both delivered modules compile locally without warnings (about 1.5 and 6 seconds).
Scratch-copy `#print axioms` for both declarations shows only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. No other axiom or hollow definition
is introduced.

## No longer needed

Removed proof-only import `Sheaf.Paper.PQFCohomology`, which was added to the
repository baseline during this reading. Removed old proof dependency
`pqf-def-cohomology`: the proof uses the actual ringed-space module cohomology
functor, recorded instead as `def-sc-ringed-space-module-cohomology`, already
publicly imported for the unchanged statement. All other old proof dependencies
remain used. Whether the removed module becomes unreachable globally is for
the maintainer's import-closure ledger to determine.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary theorem had exactly the target conclusion and all
its hypotheses plus Rees finiteness. The target was then just an application of
that unproved restatement. That fails the required real-reduction criterion.
Its short docstring and non-verbatim node signature were also insufficient.
The second reading removed it and implemented the actual transition and span
arguments, leaving only the abstract homogeneous-generation step.

The old proof-dependency node `pqf-def-cohomology` names a different Lean module
from the ringed-space module cohomology used by this statement and proof; the
proof dependency now records the actual declaration's node. The mathematical
statement and its statement dependencies are unchanged.

## New nodes

`lem-weil-pbc-finite-rees-module-single-degree-generation` states that a finite
Rees module with the convolution action is generated from every sufficiently
high degree, exactly the remaining algebraic step. Its node contains the
verbatim Lean signature, full proof, source, and leanfinder/loogle/grep searches.
LeanSearch was also attempted and returned Internal Server Error; its unavailability
is recorded without a mathematical search verdict.
Searches found filtration stability for submodules of a fixed module, finite
graded algebra generators, and finite direct sums, none with this conclusion.
The library's finite homogeneous generator theorem is for k[x0,x1] over a
field, so does not supply this general Rees-module statement.

## Second reading by G3

1. Compared the delivered original module with the repository by diff and
   checked the entire original declaration prefix through its signature byte
   for byte. Verdict: unchanged signature, visibility, and docstring. There
   are no changed existing definitions or other modules requiring adaptation.
2. Compiled both delivered files in import order with lcompile.py and checked
   both declarations with scratch-copy #print axioms. Verdict: no errors or
   warnings, one reported named theorem sorry, only the allowed axioms and
   sorryAx. No forbidden declarations or data definitions were introduced.
3. Checked the split-off theorem independently: homogeneous generators can be
   extracted from finite generators; projecting to degree c+k and factoring
   I^(c+k-d)=I^k I^(c-d) proves the claimed span equality. Zero modules, zero/unit
   ideals, k=0, and c=0 satisfy the same argument. Convolution only constrains
   nonzero coefficient monomials; zero monomials contribute nothing. The
   potentially extra images of L(k,n,0) cannot invalidate the span equality.
   The docstring and node explicitly account for this edge case. Verdict: true and strictly
   smaller than the image estimate. Searched Mathlib and both library roots
   using independent terms; no exact existing theorem was found.
4. Read from the target down through Rees finiteness and its section/scalar
   formulas. Verdict: the reduction now proves the nontrivial transition and
   image steps and retains the unit route. Checked sk-thm-p1.realized: this
   subordinate item is not a realized unit statement or step, and none of
   those nodes or imports is bypassed. Imports needed for signatures remain
   public; the new generation import is proof-only. The removed old import
   and old proof dependency are completely listed above.
5. Checked both DAG records against Lean. Verdict: the original proof now
   records Rees finiteness, actual cohomology, monic image inclusions, and the
   generation lemma. The new node has the source, complete argument, three
   searches, created/blueprint/chapter/unit/lean fields, and verbatim signature.

Changes made during second reading: replaced the rejected auxiliary restatement
by one abstract generation lemma and a real proof of transition compatibility,
span containment, and exponent arithmetic; removed its redundant abbreviation;
reduced the generation module's imports; corrected both proof records and the
report, explicitly classifying the result as a decomposition.
