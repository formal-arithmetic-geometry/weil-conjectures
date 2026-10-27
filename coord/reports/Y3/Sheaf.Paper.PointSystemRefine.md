## What changed

Restored the complete proof of `CategoryTheory.pointSystemRefine` from M3's
commit 4993207a069, recovered at `af2f412b751^`, as explicitly requested in the
2026-10-25 dedicated repair handoff in `coord/returns/Y3.md`.
The earlier batch was taken out because of an unrelated missing module; this
packet restores the actual proof rather than rebasing the unfinished statement.

The restored implementation constructs the directed disjoint-union index and
pullback diagram explicitly. A finite common upper bound and sheaf separatedness
select one covering member on which the two section representatives remain
unequal. Filtered-colimit equality then proves distinctness after refinement;
the pullback projection supplies the requested factorization. The finite cover
is reindexed through a lifted finite ordinal, preserving all original universes,
including the arbitrary covering-index universe and the empty-cover case.

The theorem's entire signature is textually identical to the current source.
All added helpers and instances are private and proved; there are no new public
declarations or modules. The node copy changes only `proof`, `proof_deps`, and
`proof_origin`, restoring M3's description of this implementation while preserving
all current attachment and review metadata. The unit route is unchanged.

The unused public finite-limit comparison import is replaced by the public
`Mathlib.CategoryTheory.Limits.Types.Colimits` required by the statement, with
`Mathlib.CategoryTheory.Limits.Types.Filtered` imported privately for the proof.
Change record: `coord/changes/Y3-point-system-refine-restoration.md`.
The unused `set_option warn.sorry false` is removed as in the restored version.

Validation: the restored module compiled cleanly through `lcompile.py` in 4.8 s.
The original theorem signature and 100-column limit were checked mechanically.
A temporary `#print axioms CategoryTheory.pointSystemRefine` probe reports exactly
`[propext, Classical.choice, Quot.sound]` (module compile: 6.6 s).
The unchanged direct consumer `Sheaf.CategoryTheory.PointSystemRefineAll` compiled
against the restored module in the sandbox import-order check (5.1 s).
The temporary axiom command and unchanged consumer copy were removed from the packet.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.pointSystemRefine`
(node `lem-trf-point-system-refine`). Added 0 holes, split off 0 statements.
There are no remaining `sorry` declarations in the delivery. This is a restoration
of a previously completed proof, not a new mathematical proof or decomposition.

## No longer needed

Removed the public import
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` and the proof
dependency `lem-weil-pbc-filtered-colimits-commute-finite-limits` from this node.
The selected finite-product consequence is proved elementwise by the private
helper `finite_persistent_ne` using `IsFiltered.wideSpan` and naturality.
No claim is made that this Mathlib module or node is unused elsewhere.
No project module is withdrawn. The site axioms and elementwise filtered-colimit
node remain needed; all four source proof steps remain realized.

## Where the brief, the DAG or earlier work was wrong

The current restoration handoff identifies the earlier batch take-out as unrelated
to this proof. Its requested completed implementation is present in the specified
history and has been restored against the current library. The current source had
reverted to the original single `sorry`, and the node had reverted to the general
finite-limit-comparison route. Both are repaired in this delivery.

No mathematical statement or definition needs correction. The original DAG's
finite-limit comparison is a valid route, but its finite-product consequence has
a shorter elementwise implementation in the restored proof. Empty coverings need
no extra hypothesis: joint injectivity over the empty family would force equality,
contradicting the distinct original germs.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
