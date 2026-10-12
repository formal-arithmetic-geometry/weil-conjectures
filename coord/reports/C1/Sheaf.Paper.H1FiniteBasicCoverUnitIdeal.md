## What changed

Replaced the original proposal's equivalent coefficient-existence restatement with a genuine
reduction in `Sheaf.Paper.H1FiniteBasicCoverUnitIdeal`. The proof constructs the finite free
sheaf morphism from the covering family, proves it epimorphic by the stalk-span criterion,
uses the full long exact sequence to lift global sections once the kernel's H¹ vanishes,
and computes the image of the lifted section in finite free coordinates to put 1 in the
span. The global lifting argument is a proved private helper.

Added `Sheaf.Paper.FiniteFreeKernelH1Vanishing`, isolating only the finite-kernel filtration
and its H¹ induction. Its theorem concerns arbitrary finite free maps to the structure
sheaf, without assuming any cover or surjectivity and without asserting ideal generation.
The helper's proof-dependency imports record the existing quasi-coherent kernel/image and
long-exact-sequence tools needed for that remaining proof. Existing public imports,
declarations, signatures, visibility, and definitions are unchanged. Only proof imports
change in the item, so no interface change record is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero` (one of one
original holes). Its body now proves the stalkwise epimorphism, the long-exact-sequence
lifting step, and the finite-sum ideal calculation.

Added one hole:
`AlgebraicGeometry.finite_free_kernel_h1_zero`, node
`lem-pqf-finite-free-kernel-h1-vanishing`, in
`Sheaf.Paper.FiniteFreeKernelH1Vanishing`. Its complete filtration proof and source are in
its docstring and node. This is a decomposition: one original hole closed, one lower hole
added, net zero declaration holes before any import-closure effects. The target still
depends on `sorryAx`; it is not claimed to be axiom-free or a net hole-count proof.
The private helper `AlgebraicGeometry.globalSections_surjective_of_kernel_h1_zero` is
proved, with no added hole. The previous unsubmitted
`AlgebraicGeometry.finite_basicOpen_cover_has_global_coefficients` and its auxiliary module
and node were removed from the proposal, not counted as closed library holes.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.Coherent`: neither its separate coherent
notion nor its theorem is used. Removed `pqf-def-coherent` from this node's old `proof_deps`;
it remains a statement dependency and the quasi-coherence notion remains in the new lower
node's statement. Retained the old long-exact-sequence dependency, now used explicitly by
the proved private helper. No unit statement or realized step was removed. No claim is
made that the coherent module is globally unreachable from all project targets.

Removed the unsubmitted `Sheaf.Paper.H1FiniteBasicCoverUnitIdealAux` restatement import,
module and node. A trial import of
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` was also unnecessary and was
removed after compilation confirmed that the public Mathlib stalk API suffices.

## Where the brief, the DAG or earlier work was wrong

The first worker's coefficient-existence lemma has the same hypotheses and a conclusion
equivalent to the unit-ideal conclusion by finite ideal-span membership. Moving the whole
cohomological argument into that lemma was not a strict reduction. The first worker also
did not update the existing node's proof and dependencies. Both faults are repaired.
The original mathematical proof route is valid and is retained. Stacks Tag 01XF was read
at https://stacks.math.columbia.edu/tag/01XF because the local literature text is absent.
The kernel-filtration paragraph applies also when the map is not surjective. No new
hypothesis about quasi-compactness or affineness is required for this part of the argument.
LeanSearch returned HTTP 500; its search is recorded as unavailable, not as evidence of
absence. LeanFinder, Loogle, Mathlib grep and local library searches found no duplicate
of the remaining kernel-H¹ statement.

## New nodes

`lem-pqf-finite-free-kernel-h1-vanishing` states only H¹ vanishing for kernels of maps from
finite free sheaves to the structure sheaf. Its proof constructs the coordinate filtration,
identifies successive quotients with quasi-coherent ideals, and inducts using the long exact
sequence. It inherits the item's chapter and unit and carries the exact Lean signature,
source, full proof steps and actual search results. It replaces the discarded unsubmitted
`lem-pqf-h1-finite-basic-cover-unit-ideal-aux`. No change records are delivered.

## Second reading by C1

1. Compared the delivered item with the repository using `diff -u`. The original theorem's
signature is byte for byte identical. Existing public imports and visibility are unchanged;
no definition or target statement changed. The only new public declaration is the named
kernel-H¹ theorem in its own module. Verdict: pass after replacing the restatement.

2. Compiled both delivered modules locally, in import order, exclusively through
`lcompile.py`; compilation is clean. Scanned the files: exactly one `sorry`, in the named
new theorem; no forbidden axiom, unsafe code, opaque declaration, external implementation,
or data chosen from an unproved existence theorem. The sheaf map is constructed using
`freeHomEquiv` and actual restriction-compatible sections. The lift obtained by `obtain`
is used only in a proposition proof, never in a data definition. Scratch axiom checks and
the delivery tool's all-declaration probe verify the allowed axioms with the reported
remaining `sorryAx`. Verdict: pass as a decomposition.

3. Checked the new lemma against Stacks 01XF and tested its mathematical edge cases:
empty index type has zero kernel, singleton has an ideal kernel, the zero map has a free
kernel filtered by copies of O_X, and the empty scheme gives zero modules. Kernel/image
quasi-coherence and affine ideal identification justify all successive ideal quotients.
Repeated searches with different words using LeanFinder, Loogle, Mathlib grep and local
`rg`; no theorem already states this kernel-H¹ vanishing. Unlike the rejected coefficient
lemma, it covers only the filtration step and does not supply the global lifting or the
unit-ideal conclusion. Verdict: true, needed, and strictly part of the argument; still open.

4. Followed the proof downward and reused the existing proved stalk-span and finite free
coordinate theorems, and the existing full long exact sequence. Removed the unused coherent
import and recorded the obsolete dependency. Read
`dag/units/sk-prop-av-pqf-finite.json`: its statement, step and `realized` fields are untouched;
this reduction stays within the original kernel-filtration/lifting route. Verdict: pass.

5. Updated the item's node to match the constructed map, stalk-span epimorphism, kernel-H¹
lemma, long exact sequence and final coordinate computation. Its `proof_deps` is exactly
the union of step uses. The new node has its own self-contained statement, exact Lean
signature, full docstring proof, source, search records, inherited chapter/unit and matching
proof dependencies. Verdict: pass.

Second reading changed the equivalent restatement into the actual stalkwise and
cohomological reduction, removed the obsolete auxiliary module/node and unnecessary change
record, pruned the coherent import, and repaired both the DAG and progress accounting.
