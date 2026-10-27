## What changed

Replaced the proof hole in
`AlgebraicGeometry.AdmissibleModificationSystem.admissibleModificationSystem`
without changing its signature, public imports, or any existing definition.
All supporting constructions and proofs in the item are private.

The proof constructs the filtered preorder using products and the existing ideal-factorization
criterion for blowup domination. It compares the specified affine blowup with the global
ideal-sheaf blowup over the terminal affine open, and uses the invertible exceptional ideal to
prove the required schematic density. Finite generation makes the preserved open quasi-compact,
which gives injectivity on sections over every open.

For completion, the proof establishes extension/contraction for ideals containing a power of I,
finite generation of their contractions, and approximation modulo each power. These prove the
index equivalence and reflection of domination. It constructs the additive power-quotient maps
and proves their bijectivity. Coefficient and monomial linear maps characterize the ideal
extended to the Rees ring; this proves bijectivity of the canonical Rees-quotient ring map.
All comparisons have the prescribed formula on representatives.

Added `Sheaf.AlgebraicGeometry.BlowupClosedFiberOfReesReduction`, containing only the remaining
geometric passage from canonical residue/Rees reductions to the closed-fibre isomorphism and its
two projection identities. Updated the item's DAG proof to match this reduction.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AdmissibleModificationSystem.admissibleModificationSystem`
(node `lem-per-admissible-modification-system`). There are no `sorry`s in the item module.

Added one hole:
`AlgebraicGeometry.AffineBlowup.exists_closedFiberIso_of_reesReduction`
(node `lem-per-blowup-closed-fiber-of-rees-reduction`). Its complete body is `by sorry`, with
source, natural-language proof, and matching DAG node. It is strictly the last geometric step:
it says nothing about completion, admissible indices, filtration, schematic density, ideal
descent, domination, or construction of the quotient isomorphisms. Those are proved in the item.
Thus this delivery is a decomposition (one hole closed, one added), not a net hole reduction or
an assertion of an axiom-free proof. The existing imported ideal-factorization theorem remains
an upstream proof obligation; this delivery does not modify it.

Validation: `lcompile.py --all` compiled both delivered modules with no errors or warnings;
the item took 21.4 seconds, below the 60-second limit. Original definition bodies and the
main theorem signature/docstring were compared with the shared source and are identical.
All Lean lines fit the 100-character limit.

The constructions cover exponent zero in the auxiliary quotient arguments, degree zero in the
Rees ring, unit ideals, nilpotent centres, and the zero ring. Henselianity is retained in the
statement but is not needed by these algebraic comparisons.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange` from the item: its abstract
`PullbackData` interface is not directly applied by the completed proof. Its node
`lemma-nagata-relative-proj-base-change-arbitrary` is removed from the item's direct
`proof_deps` and obsolete top-level tool approval, but remains needed in the new geometric
sublemma's proof plan. It is not globally pruned or withdrawn. The new node declares that
inherited generic tool use for review.

The other original dependencies remain needed, except that the exact global complement theorem
`thm-nagata-global-blowup-complement` replaces
`lemma-nagata-admissible-blowup-over-open` in the proof dependencies. The latter remains a
statement dependency of the unchanged node; it is not withdrawn or globally pruned. The radical-power and completion-mod-power
leaves are used directly from Mathlib; the domination criterion is imported from its existing
Sheaf module. Principalization and the blowup complement supply density; the existing proved
invertible-ideal complement lemma records its final injectivity step. No existing Lean module
or DAG node is withdrawn, and no adopted source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing mathematical hypothesis was found. The original final step
suppressed the Lean bridge between the concrete Rees-ring quotient and the abstract
coefficientwise graded-algebra pullback used by relative Proj. That bridge and its two
projection identities are the new smaller obligation. The algebraic steps of the original
plan have been implemented, rather than replaced by renamed versions of the original theorem.
The unit's route and all target statements stay unchanged. There are no shared-interface changes
and no forced adaptations.

## New nodes

`lem-per-blowup-closed-fiber-of-rees-reduction` is the final Proj step of ILO XX 4.4's Note.
It assumes canonical isomorphisms on residue rings and reduced Rees rings for an arbitrary
ring map, then concludes the isomorphism of the two closed fibres with both projections.
The representative formulas force the Rees map to preserve degrees. Its node records the
homogeneous-quotient, Proj-base-change, and chart-naturality argument, all required search kinds,
and the same blueprint ancestor and unit as the item. The zero-ring, zero-quotient-Rees and
unit-centre cases do not require any additional hypotheses. No change record is necessary:
existing signatures and definitions are unchanged.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
