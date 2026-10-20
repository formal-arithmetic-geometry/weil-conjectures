## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations in favour
of the proved official twin, following retire-items.tsv row 920 and the human
hand-off of 2026-10-20. The duplicate is listed in deleted.txt. Its existing node
now attaches to the official declaration with its exact exteriorPower signature.

Adapted the sole direct consumer, DeterminantWedgeQuotientFactor, without changing
its public signature, attributes or public imports. The proof-only import now
names the official twin. A fully proved private tensor comparison helper is moved
from the retired copy into the consumer. Tensor the canonical exteriorSheafPowerIso
maps to conjugate q and precompose ψ, check the two generator formulas, and apply
the official kernel theorem. Pull back the vanishing along kernel.lift and cancel
the inverse comparison. The original Abelian.epiDesc argument then applies.
The consumer node records this argument. No upstream source or target changed.

Validation: lcompile.py compiled the adapted consumer, the withdrawn empty stub,
and unchanged immediate consumers DeterminantLiftWedgeKernel and
DeterminantWedgeMorphismLocalAt together in import order, without errors or
warnings (10.7, 0.3, 22.4 and 23.5 seconds respectively). Temporary validation
copies are not delivered. The consumer signature and public imports were checked
byte-for-byte against the original and are identical.

Change record: coord/changes/E5-retire-exterior-tensor-kernel-relations.md.

## Proved and sorry left

This is a zero-hole retirement repair: 0 holes closed of 0 original holes, 0 holes
added, 0 split off, 0 left in the delivered Lean code. The current assigned module
was already proved when this session started. The official
AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_eq_zero_of_relations is
already proved and is reused; it is not moved to a new holed declaration.
The consumer determinant_wedge_quotient_factor remains fully proved. Its new
comparison and kernel transport are complete Lean proofs.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations.
Its sole proof import in DeterminantWedgeQuotientFactor is replaced with
WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations.
The retired copy's comparison helper is retained privately where it is needed;
its degree-zero helper and duplicate sheaf-local proof are unnecessary because
the official theorem already proves the complete generator criterion.

The node no longer needs lem-sc-exterior-sheaf-power-comparison in its own proof:
its official proof uses exteriorPower directly. That dependency is still needed
and recorded at the consumer, which performs the comparison. The official node
uses def-sc-sheaf-exterior-power, lem-sc-exterior-tensor-lift-hom-ext and
lem-sc-exterior-tensor-kernel-locally-spanned. These nodes and their upstream
modules remain needed; none is withdrawn. No unit statement or route is removed.
DAG parents retain the criterion node, now attached to its proved official twin.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open hole and six earlier splits, but the
current assigned module has zero holes. The current retirement row is applicable:
the official twin already proves the statement for the canonical alternative
exterior-power construction. The two types differ syntactically, so an import
swap alone is insufficient; the explicit comparison and kernel lift above are
required. No false statement, definition repair, new node or added assumption
was needed. Source scans of both Lean roots and quarantine found just one direct
importer; downstream.py lists ten downstream users, all protected by the unchanged
consumer public interface. No adapted module is claimed by another group.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
