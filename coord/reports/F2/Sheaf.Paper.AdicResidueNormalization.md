## What changed

Proved `AlgebraicGeometry.Scheme.sfbResidue_normalization` in
`Sheaf.Paper.AdicResidueNormalization`, preserving its public signature verbatim.
The canonical projection identity and constant-section compatibility give the
ordinary scalar-restriction square. Exact derived transport and the inverse mate
under the scalar adjunctions give the extension comparison. Explicit localization
factorizations remove all three chosen representatives.

The proof uses the already proved
`IntegralConstantCompletion.derived_scalar_adjunction`, the fixed-scalar small-site
coordinate theorem, the completed scalar adjunction, and the inverse-mate theorem.
Small proved private helpers construct the ordinary transport equivalences and
restriction squares. The fixed-scalar derived category retains the smaller
localization universe in the original statement; the final composition comparison
specifies that intermediate universe explicitly.

Added only proof imports: private access to SfbCompletionNormalization,
IntegralConstantCompletion, ConstantCompletionEquivalence and
ConstantScalarRestrictionTensor; FixedScalarSmallCoordinates,
BoundedConstructibleTower and InverseMateEquivalence. All original public imports
are needed by the statement and retained. The local sheafification witnesses now
use the explicit coefficient-universe witnesses to avoid ambiguous universe
inference. No shared module or public interface was changed.

Updated the item's DAG proof, proof dependencies and proof origin. No other DAG
fields changed. The complete proof compiled through lcompile.py in 17.2 seconds;
the final delivery checks compile the cleaned file again.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.sfbResidue_normalization`
(node `lem-sfb-adic-residue-normalization`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off statements, axioms, or definitions containing holes were added.

## No longer needed

The planned dependency `lem-sf-ringed-site-equivalence-tensor`, module
`Sheaf.CategoryTheory.RingedSiteEquivalenceTensor`, is unnecessary for this proof.
Derived scalar extension is compared as a left adjoint to exact scalar restriction,
so no new tensor, flatness or K-flat transport argument is needed.
`lem-sfb-constant-scalar-restriction-tensor` is still used for its ordinary
restriction equivalence and cancellation API; its derived tensor comparison is
unused. Every original statement dependency remains.

No original import was removed: each supplies objects in the public statement.
No module is withdrawn, and no claim is made that another consumer no longer needs
the ordinary tensor-equivalence theorem. The blueprint unit statement and route
are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's K-flat-transport step is longer than necessary. The existing library
already supplies the scalar adjunctions and invertible inverse mates; these prove
the comparison from an explicit ordinary restriction square.

During work, IntegralResidueModelComparison and
IntegralModelsCompleteSectionPredicate were quarantined (coord/rework.tsv,
2026-10-26T10:20:36Z). Their proved generic helper constructions were useful to
read, but the delivery imports neither module. The small categorical constructions
are proved privately here from the remaining APIs. Both quarantine archives and
their DAG attachments are untouched.

Searches through msearch.py: LeanFinder found pushforwardCongr and ordinary
ModuleCat scalar-extension composition, not this derived comparison; Loogle did
not resolve the short query Adjunction.leftAdjointUniq; grep found the Mathlib
adjunction-uniqueness and scalar-extension APIs. Local searches then found the
existing adjunction and coordinate constructions used here. No source error or
statement correction was needed. The argument does not use completeness,
Noetherianity, nonzero coefficients or points, and applies equally to I=0 and I=A.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
