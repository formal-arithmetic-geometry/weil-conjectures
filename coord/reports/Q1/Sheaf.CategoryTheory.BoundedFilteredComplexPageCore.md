## What changed

Replaced the original hole of `CategoryTheory.boundedFilteredComplex_pageCore` by a
compiling reduction to two strictly smaller theorems in separate modules:
`BoundedFilteredPageConstruction` constructs the page functor, natural comparisons,
representative maps and associated exact couple, without convergence or stabilization;
`BoundedFilteredCoupleAbutment` proves finite convergence for a supplied exact couple
whose alpha and initial gamma are the filtration inclusion and quotient maps.
The assembly uses the same `S`, `e₁`, `eI`, `X`, `eD` and `eC` throughout.
The original theorem signature, visibility and docstring are unchanged.

Proved stabilization directly in the item, with four proved private helpers:
`pageCore_subobjects_stabilize`, `pageCore_quotient_iso`, `pageCore_graded_zero`, and
`pageCore_differentials_stabilize`. Antitonicity fixes the whole and zero filtration
tails. Equal successive filtration steps give a zero graded complex, hence zero page
components through the supplied cycle/boundary quotients. This kills both distant
differentials. Taking a common bound and transporting the stabilized quotient gives
the stationary page isomorphism. This proof does not choose an unrelated spectral sequence.

All three delivered modules compile through lcompile.py. The new statements were checked
at r=1, at the zero complex, for a filtration with one nonzero graded piece, and with
whole and zero indices in either order. No first-quadrant or nonzero-complex hypothesis
was added. All constructions in the abutment theorem are determined by their image or
universal-property equations; no data definition chooses an arbitrary existence witness.

## Proved and sorry left

Closed the original hole in `CategoryTheory.boundedFilteredComplex_pageCore`
(node `lem-sp-bounded-filtered-page-core`). Its proof contains no sorry.

Added exactly two holes:

- `CategoryTheory.boundedFilteredComplex_pageConstruction`
  (`lem-sp-bounded-filtered-page-construction`), in
  `lean/Sheaf/CategoryTheory/BoundedFilteredPageConstruction.lean`.
- `CategoryTheory.boundedFilteredComplex_coupleAbutment`
  (`lem-sp-bounded-filtered-couple-abutment`), in
  `lean/Sheaf/CategoryTheory/BoundedFilteredCoupleAbutment.lean`.

Each remaining hole is the entire proof of a public theorem with a source, complete
proof in words, and a matching node. This is a decomposition: one original hole
closed, two lower holes added, net minus one. The finite-tail stabilization and
vanishing-differential arguments themselves are fully proved, using Mathlib only.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`.
- `Sheaf.CategoryTheory.ExactCoupleMorphism`.
- `Sheaf.CategoryTheory.ExactCouple`.
- `Sheaf.CategoryTheory.Filtration`.

The first two remain needed in the construction node's plan, so they are not claimed
as globally pruned modules. ExactCouple and Filtration remain available through the
unchanged public statement imports. The item no longer uses
`lem-sp-filtered-complex-ZB-description` for stabilization: its finite-tail proof is
direct. The parent node now lists the two new argument parts and the definitions
used by its direct proof, rather than the old unspecialized construction plan.
No whole module is established to leave the targets' import closure in this delivery.
No unit-realizing statement or proof step was bypassed (`realized` is empty for these nodes).

## Where the brief, the DAG or earlier work was wrong

The earlier attempt proved an unused helper about a separately existentially supplied
page-zero spectral sequence while leaving the assigned theorem's sorry intact.
That was correctly refused as an incomplete delivery. The helper is replaced by
proofs about the actual page-one functor obtained in the construction reduction.

The existing ZB-description theorem supplies an objectwise spectral sequence and
representative comparison, but not the required functor with all exact-couple
structural equations and finite abutment. The existing half-plane convergence
interface assumes negative first-index vanishing; the reindexing here supplies a
finite strip in the second index instead. Neither declaration can simply be applied
to obtain the full package. This interface gap is what the two new nodes isolate.

LeanFinder returned mapping-cone, homology exactness, and AB5 candidates; none has
these interfaces. Loogle had no hit for CohomologicalSpectralSequence. LeanSearch
was unavailable (Internal Server Error), recorded without a match verdict.
Source and Mathlib rg searches found abstract spectral-object page constructions
and first-quadrant convergence, but no matching finite filtered-couple theorem.

WANTED: Stacks Project, Homology, Section 12.24, Lemmas 12.24.2--12.24.4 and
12.24.11, for independent source checking of the two new nodes. This checkout
contains the literature lists but not the source text. The new proofs in words
make precise the recorded DAG plan and are marked agent-origin.

## New nodes

`lem-sp-bounded-filtered-page-construction`: canonical functorial page construction,
representative comparisons and exact-couple structure, excluding finite abutment
and stabilization. The proof follows construction and representative steps 1--4.

`lem-sp-bounded-filtered-couple-abutment`: convergence of a supplied couple identified
with filtration homology, including the image filtration, normalized alpha-colimit
cocone and infinite-page graded comparison. It does not construct pages or prove
the finite-page stabilization clause. Its hypotheses expose exactly the alpha and
gamma equations used by the abutment argument.

No statement/interface change and no change record; no forced adaptations.

## Second reading by Q1

1. I compared `BoundedFilteredComplexPageCore.lean` with the repository version. The
   original theorem signature and all existing declaration signatures are unchanged;
   only imports, private proof helpers, and the theorem proof differ. The two added
   public theorem signatures are represented verbatim in their new DAG nodes.
   Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`. The only remaining
   `sorry`s are the two named public split-off theorems, with no `sorry` in a definition
   and no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` construct.
   Verdict: pass.

3. I checked the two split-off statements against their docstrings and node records.
   They are strictly smaller construction and abutment interfaces, respectively, and
   the item assembles them without weakening or strengthening its original statement.
   The finite-tail helpers were tested by the zero and one-step filtration edge cases
   described above. Verdict: pass.

4. I checked the proof route from the top downward. The item uses the two construction
   and abutment nodes, then direct Mathlib/order and subobject arguments for stabilization;
   obsolete direct imports and dependencies are listed under `No longer needed`.
   The unit route remains represented by the construction, abutment, and parent nodes;
   no unit step is bypassed. Verdict: pass.

5. I checked that the parent node proof, proof dependencies, and proof origin follow the
   Lean proof, and that each new node has source, proof steps, searches, Lean declaration,
   chapter, and unit metadata. Verdict: pass.

I changed only this report section after the first worker delivery; no Lean statements or
proofs were changed during this second reading.
