## What changed

Completed the earlier sandbox proof of
`ModuleCat.exists_bounded_finite_free_resolution`, preserving its full signature.
The zero-bound case uses the length-zero projectivity theorem, Mathlib's
`Module.free_of_flat_of_isLocalRing`, and the self resolution. The positive-bound
case uses `IsLocalRing.exists_finite_free_resolution_data`, proves its leftmost
kernel projective with `projective_of_exact_partial_projective_resolution`, proves
it finite by injectivity into a finite module over a Noetherian ring, and makes it
free by the same Mathlib theorem. The augmentation is transported along the given
module equivalence without changing the complex.

Added the fully proved module `Sheaf.RingTheory.FiniteFreeExactSequenceResolution`:
`ModuleCat.exists_bounded_finite_free_resolution_of_exact_sequence` explicitly
constructs a chain complex from the reversed finite sequence and verifies its
augmentation is a quasi-isomorphism. No object is chosen from an unproved mere
existence theorem inside a definition. All witnesses are assembled inside proofs.

Updated the item's node proof and dependencies to match this route. The unit
`sk-thm-p1` and all its realized steps are unchanged; this item is below that level.

## Proved and sorry left

Closed the item's one hole:
`ModuleCat.exists_bounded_finite_free_resolution`
(node `stage3-b4-bounded-finite-free-resolution`).

The new theorem
`ModuleCat.exists_bounded_finite_free_resolution_of_exact_sequence`
(node `lem-weil-pbc-finite-free-exact-sequence-resolution`) is fully proved.
There are no sorries left in either delivered module, and no holes added or split off.
This is a proof from existing library declarations, not a decomposition into new holes.

## No longer needed

Removed direct proof imports:

- `Sheaf.RingTheory.FiniteProjectivePrimeLocalFree`: node
  `lem-weil-pbc-finite-projective-prime-local-free` is unnecessary for this proof;
  Mathlib directly proves finite flat modules over local rings free.
- `Sheaf.RingTheory.FiniteFreeResolution`: replaced its direct use by the already
  available finite-sequence construction in
  `Sheaf.RingTheory.CohenMacaulayFreeResolutionConstruction`. Its node
  `lem-weil-pbc-finite-free-resolution-noetherian` remains needed transitively by
  that construction and is not claimed to be pruned from the targets' closure.

Retained `Sheaf.RingTheory.ProjectiveResolutionKernelProjective` and the
Noetherian submodule-finiteness dependency. No other original proof dependency is
pruned. The public statement imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained complete proof text but lacked delivery metadata
and a report. Its main proof had an unnecessary explicit index-proof argument
that produced a `No goals to be solved` error, and a redundant congruence tactic
that generated warnings; both are repaired. The finite-sequence helper was
already a genuine construction, and its proof has been retained and checked.

The DAG's prime-localization detour is unnecessary: Mathlib's
`Module.free_of_flat_of_isLocalRing` supplies freeness directly (projective modules
are flat). The existing finite-sequence interface avoids repeating the infinite
resolution truncation construction. No statement or definition was changed.

Read Stacks Tag 0CXF at https://stacks.math.columbia.edu/tag/0CXF, including its
finite-free-resolution conclusion and finite-projective-to-free argument; the
local literature source is absent in this clone. Mathlib search found only general
unbounded projective-resolution constructors. LeanSearch returned HTTP 500, which
is recorded as unavailable, not as a negative match.

## New nodes

`lem-weil-pbc-finite-free-exact-sequence-resolution` records the fully proved
categorical packaging helper. It assumes an already exact sequence with finite
free terms, does not assume Noetherianity, locality, or a projective-dimension
bound, and does not restate the main theorem. Its explicit complex uses S_0 above
the bound, so it is zero there. The cases d=0, d=1, and the zero module are included:
at d=0 both endpoints enforce that the augmentation is an isomorphism; at d=1
exactness with the left endpoint makes the top differential monic; in every case
zero terms are finite free. The three search kinds are logged, including the
unavailable LeanSearch request. There are no change records or forced adaptations.

## Second reading by G4

1. PASS: diffed the existing module against the repository. Its declaration
   signature, visibility, public imports, and docstring are byte-for-byte
   unchanged; only the proof and private proof imports differ. The helper
   module is new. No definitions or target statements changed, and no change
   records or forced adaptations are needed.
2. PASS: compiled both files in import order through lcompile.py, without
   errors or warnings. Neither contains sorry or forbidden declarations.
   A scratch copy with #print axioms for both delivered theorems reported
   exactly propext, Classical.choice, and Quot.sound, with no sorryAx.
   The helper explicitly constructs ChainComplex.of; the main theorem
   assembles existential witnesses inside its proof. No definition chooses
   data from an unproved existence assertion.
3. PASS: no statements were split off with sorry. Independently read the
   fully proved helper and checked d=0, d=1, and zero modules: degree d+1
   uses the zero left endpoint; the augmentation is epic by the right
   endpoint, and exactness at degree zero includes d=0. The helper assumes
   the exact sequence already exists and proves only its categorical
   packaging, strictly a part of the main argument. Independent LeanFinder
   and grep searches and rg over the project found no replacement; the
   first Loogle query was unsupported, not a negative search result.
   Retried with CategoryTheory.ProjectiveResolution: 12 generic matches,
   including self already used in the zero-bound case, and no replacement.
4. PASS: the zero-bound proof uses the existing length-zero theorem and
   Mathlib freeness, while the positive-bound proof uses the existing
   finite-sequence and projective-kernel theorems before the helper. No
   shorter applicable bounded constructor was found. Imports supply the
   statement or used construction, exactness, finiteness, and projectivity
   interfaces. The No longer needed section accounts for both removed
   dependencies, including the still-transitive finite-free construction.
   Read sk-thm-p1.json: no realized step is bypassed or changed.
5. PASS: compared old and new item nodes. Only proof, proof_deps, and
   proof_origin change; their steps agree with the code and their uses
   have exactly the recorded union. The new helper has its source, full
   docstring argument, matching Lean signature, search records, provenance,
   chapter, and unit. Augmentation transport uses the inverse equivalence
   for the assumed resolution and the forward equivalence for the result.

Second reading changed no Lean proof. Removed duplicated search records
from the new node and recorded independent reuse searches and this review.
