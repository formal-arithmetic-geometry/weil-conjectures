## What changed

Proved the unchanged theorem `IsLocalRing.kollar_local_dichotomy` in
`Sheaf.RingTheory.KollarLocalDichotomy` by explicit case analysis and depth exclusion.
Added private, fully proved helpers for extracting regular elements from depth, producing
positive depth from a regular element, killing the kernel, killing the cokernel, stabilizing
maximal-ideal torsion, and building the universe-lifted quotient extension.
Added the proof import `Sheaf.RingTheory.KollarRegularElementAlternatives` and Mathlib proof
imports for the Artinian/nilpotent equivalence and universe lifting. Existing public imports
and the theorem signature are unchanged. Updated the parent DAG route to match the Lean.

The only unfinished branch is when x is regular in the maximal ideal and the maximal ideal
is associated to R/xR. The new module isolates precisely the integral-subalgebra versus
principal-maximal-ideal alternatives in the source's fourth and fifth proof paragraphs.
This is a decomposition, not a proof independent of new holes: one upper hole is closed and
one strictly smaller lower hole is added. The torsion and depth-exclusion arguments are
written and checked in Lean, rather than moved into that new hole.

## Proved and sorry left

Closed: `IsLocalRing.kollar_local_dichotomy` (one of one original holes).
No sorry remains in the item's module. Added exactly one sorry:
`IsLocalRing.kollar_regular_element_alternatives`, node
`lem-weil-pbc-kollar-regular-element-alternatives`, in
`Sheaf.RingTheory.KollarRegularElementAlternatives`.
The pre-existing `IsLocalRing.depth_in_short_exact` and
`exists_mem_maximalIdeal_smul_injective` remain used from their existing modules; their
proofs are not altered here. Net holes closed minus added for this decomposition: zero.
Both delivered modules compile in import order with no non-sorry warnings.

## No longer needed

No original Lean import was removed: DepthInSES and NonzerodivisorIfMaximalNotAssociated
are both genuinely used. The direct torsion construction uses Mathlib's
`isArtinianRing_iff_isNilpotent_maximalIdeal`, so the parent no longer needs
`lem-weil-pbc-noetherian-local-quotient-artinian-local` for this proof. That node is a
Mathlib leaf; it has no Sheaf module to remove.
Parent dependency edges moved down into the new branch (these are NOT globally pruned):

- `lem-weil-pbc-endomorphism-finite-module-monic`
- `def-weil-polynomial-ring`
- `def-weil-ring-localization-away`
- `lem-weil-pbc-finite-of-integral-generators`
- `lem-weil-pbc-noetherian-local-dimension-le-generators`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-noetherian-minimal-prime-associated`
- `def-weil-regular-scheme`

The remaining parent dependency `def-weil-pbc-exact-sequence` is unnecessary as a separate
proof edge: Mathlib supplies `LinearMap.exact_map_mkQ_range` and quotient surjectivity.
The exact-sequence module was not imported by the original file.
No unit statement or unit proof step is bypassed: the parent is not a realized unit step,
and the source's regular-versus-integral-extension branch remains explicitly required.

## Where the brief, the DAG or earlier work was wrong

The brief is usable. The DAG marked construction of the stabilized torsion ideal elementary;
it needs real Noetherian chain stabilization, supplied by Mathlib here. No statement is
changed or disputed. The checked-out `literature/stacks-project/algebra.tex` is absent on
this machine; the recorded Stacks Tag 0BHZ was read at
https://stacks.math.columbia.edu/tag/0BHZ, and the existing node's complete source proof was
also read. LeanSearch returned an HTTP Internal Server Error; it is recorded as unavailable,
not as a successful search with no match. LeanFinder, Loogle and grep completed.

## New nodes

`lem-weil-pbc-kollar-regular-element-alternatives`: assumes a specific regular element x in
m and that m is associated to R/xR, and concludes only regular dimension one or the finite
extension alternative. It removes the Artinian branch, the torsion construction, the
second-regular-element branch and all depth exclusion from the original task. Its source
proof uses the determinantal trick and the principal-maximal-ideal argument of Tag 0BHZ.
The docstring and node give a complete proof sketch. Edge checks: in a field no regular
x lies in m; in an Artinian local ring no element of m is regular; in a regular local ring
of dimension at least two, m is not associated to a regular-element quotient. In a DVR
the regular-dimension-one alternative applies. No change record is needed: all existing
statements and definitions are preserved.

## Second reading by Q2

1. I compared the delivered parent module and node with the repository version. The target theorem
signature and all existing declarations are byte-for-byte unchanged; the new declaration has its
own module and node. Verdict: pass.

2. I compiled both modules in import order with `lcompile.py --all`. The parent proof has no
`sorry`; the only new sorry is the explicitly named split theorem. No forbidden declarations or
hollow definitions occur. The axiom probe shows only standard axioms for the private proved
helpers; the remaining `sorryAx` comes from the split theorem and pre-existing imported holes.
Verdict: pass.

3. I checked the new statement against Tag 0BHZ and its edge cases (field, Artinian local ring,
DVR, and regular local rings of dimension at least two). It is strictly smaller than the parent:
it assumes the regular element and associated-prime branch and concludes only the two remaining
alternatives. Its docstring gives the source and proof route, and the DAG node matches its Lean
signature. Searches found no existing declaration. Verdict: pass.

4. The proof follows the source route: the Artinian case, stabilized torsion ideal and quotient
extension, regular-sequence depth branch, and depth exclusion are all explicit. The regular-element
subcases remain represented by the split theorem. The direct Mathlib colon stabilization replaces
the old Artinian quotient dependency, and the unused exact-sequence edge was removed from the
DAG proof dependencies. Verdict: pass.

5. The unit route is preserved: this item is not a realized unit step, and no unit statement or
realized step was bypassed. The report records the one decomposition and the removed proof edges.
Verdict: pass.

I changed only this report by adding the second-reading record. No Lean proof or statement was
changed during review.
