## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_local_section_of_epi` in
`Sheaf.AlgebraicGeometry.Modules.LocalSectionOfEpi`, preserving its signature and visibility.
The proof follows the existing finite-basis lifting plan: extract a trivializing open from
finite locally free generators data; lift the finite basis simultaneously; form the sum of
coordinate projections followed by the lifted basis morphisms; and transport the splitting
from the localized site to the open subscheme using `overFunctorEquiv`.

Added two proved private helpers, `finite_free_neighborhood` and `finite_local_lifts`.
The first extracts the same trivialization as the proved upstream
`exists_mem_over_iso_free`, without importing its broader affine-module theory. The second
adapts the proved private finite-lifting argument in
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` from `Fin s` to an arbitrary finite
index type; its naturality calculation uses Mathlib directly. Neither helper has a hole.

Added proof-only imports of the upstream free-sheaf coordinate API, the proved preservation
of colimits by the underlying abelian-group sheaf functor, and Mathlib's local-surjectivity
and abelian-category APIs. All original public imports remain. No definitions, existing
statements, instances visible to importers, or other modules changed.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.exists_local_section_of_epi`
(node `new-sbc-local-section-of-epi`). Added zero holes; no `sorry` remains in the delivery.
Both private helpers are proved. This is a proof, not a decomposition.

The empty family retains the trivializing open because the common neighbourhood is
`U ⊓ ⨅ i, V i`; the empty finite sum is handled by the existing free-sheaf identity
decomposition. The empty scheme has no point to consider. No quasi-coherence assumption
on the source is introduced.

Single-file compilation was checked using `lcompile.py`; the delivery dry run also checks
the axioms of all added declarations.

## No longer needed

No original import, planned dependency node, or planned dependency module is removed.
The four existing proof dependencies still describe the notions used by the argument.
No new proof obligation or import of a holed Sheaf module is needed.

The broader `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine` import used during
exploration is absent from the final proof. Its trivialization is obtained directly from
`IsFiniteLocallyFree.exists_localGeneratorsData`. The exterior-tensor module used as a
reference for the private lifting argument is also not imported. These are avoided
exploratory imports, not claims of pruning modules from the existing target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing node's finite-basis plan is fully realized,
so its proof, proof dependencies, and proof origin remain unchanged. The unit record
`sk-prop-input-spreading` has no realized statement or step nodes here; its route is preserved.

The general `overMap` functor lacks an automatically synthesized additive instance in this
context. Its additivity is proved locally by sectionwise extensionality and reflexivity.
No public interface change is required. Keeping the local generators data inside the
private trivialization theorem avoids exposing its dependent projections throughout the
main elaboration.

## Second reading by J2

1. **Interface comparison.** Compared the delivered module with the repository version. The
existing theorem signature and visibility are byte-for-byte unchanged; only proof text and
proof-only imports were added. No definition or public instance was changed. Verdict: pass.

2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly.
The delivery contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
The two helpers and the target theorem are ordinary proofs; the delivery preflight checks
axioms. Verdict: pass.

3. **Statements and split-offs.** No statements were split off and no new DAG node was
added. The target theorem is exactly `new-sbc-local-section-of-epi`; its finite-basis and
simultaneous-lifting argument proves the stated local section, including the empty finite
index case. The private helpers are strictly intermediate constructions and introduce no
public claim. Verdict: pass.

4. **Route and pruning.** The proof uses the finite locally free trivialization, local
surjectivity of an epimorphism, finite intersection of neighbourhoods, free-sheaf
coordinate identities, and `overFunctorEquiv`, matching the node's proof plan. All four
planned proof dependencies remain relevant; exploratory affine and exterior-tensor imports
were not added. The unit `sk-prop-input-spreading` has no realized statement or step for
this node, so no unit route is bypassed. Verdict: pass.

5. **DAG agreement.** The node's proof, dependencies, and origin already describe the
finite-basis lifting route implemented here. No node or unit record required editing, and
no change record is needed. Verdict: pass.

Changed after review: added this second-reading record only; no Lean code or DAG metadata
was altered during the review.
