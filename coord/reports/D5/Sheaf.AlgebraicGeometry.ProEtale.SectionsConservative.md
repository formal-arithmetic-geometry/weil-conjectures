## What changed

Completed the proof of `AlgebraicGeometry.Scheme.ProEt.sections_conservative`.
The proof establishes exactness detection through local lifting and the weakly
contractible affine cover, then derives degreewise acyclicity, isomorphism detection,
and the mapping-cone characterization of quasi-isomorphisms. Added a proof-only import
for the closed source weak-contractibility theorem; retained the existing proof-only
imports for the cover, module-sheaf colimit/limit facts, and mapping-cone criterion.
Updated the existing DAG node's proof and proof dependencies to match this argument.
Validation: `lcompile.py` compiled the proof cleanly against the current build in 3.1 seconds. The existing theorem
signature is textually unchanged. None of the five direct importing modules calls the
removed equivalence theorem; no consumer adaptation is required. All five compiled
cleanly against the changed module in the scratchpad consumer overlay.
The public-import removal is recorded in
`coord/changes/sections-conservative-public-imports.md`, with every downstream module.

## Proved and sorry left

Closed the sole `sorry`, `AlgebraicGeometry.Scheme.ProEt.sections_conservative`
(node `det-pe-sections-conservative`): 1 hole closed, 0 added, 0 left.
The private helper `exact_sections_iff` is proved completely.

## No longer needed

Removed the unused public import `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences`;
the proof uses the existing source theorem `isWeaklyContractible_of_iso` directly and does not
use the equivalence theorem from that module. Removed
`det-pe-weak-contractible-equivalences` from the proof dependencies, replacing its final
affine assertion by the already closed
`lem-weil-pbc-source-affine-wcontractible-evaluation`. The former remains an unchanged
statement dependency recording the mathematical terminology; its theorem is not imported.

Removed `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective` from the proof dependencies
and its obsolete tool approval: the proof applies `IsWeaklyContractible` directly to
the locally surjective underlying set-sheaf map. It needs no set-sheaf epi conversion.
The general abelian-sheaf epi criterion is still used. The degreewise and mapping-cone
arguments still use the existing derived-category, cone, and sectionwise-limit nodes.
No other imports or nodes are pruned; the cover/local-lifting route of the unit is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier draft omitted the explicit source imports needed by its proof and left typeclass
inference unable to identify the mapped mono and epi. Supplying the existing source modules and
explicitly passing the mapped morphisms resolves these issues without changing the theorem
statement. The retained report had not updated the DAG after pruning the full equivalence
theorem and the set-sheaf epi conversion; this delivery corrects those records. Isomorphism
detection uses exactness of the zero/f and f/zero short complexes, followed by the abelian
mono-and-epi criterion, rather than a second sheaf-gluing argument.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
