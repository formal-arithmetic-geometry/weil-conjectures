## What changed

Proved the normalized right shift, normalized left shift and covariant
triangulatedness in `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
The chain maps are unsigned target reindexing and signed source reindexing by
`(-1)^(s*k)`. Product extensionality proves the chain identities, naturality,
inverses and target shift coherence. Localization through the fixed K-injective
augmentation gives the exact normalization equations and uniqueness. An explicit
Hom-cone triangle comparison, including its boundary arrow, descends exactness.
All existing public declaration signatures and public imports are preserved.

`RightFormula` and `LeftFormula` omit the canonical identity degree maps and now
name the source library's fixed `homComplexπ` directly. That projection selects
the same existence specification as the original coefficient projection;
`homComplex_projections_exists` is `Classical.choose_spec homComplex_exists`.
There is no different Hom complex, projection choice or weakened normalization.
The projection API is added as a public import because these predicates use it.
Changes are recorded in:

- `coord/changes/S6-ringed-hom-RightFormula.md`
- `coord/changes/S6-ringed-hom-LeftFormula.md`

Private imports supply localization/shift APIs, the K-injective derivability
structure, independent-universe quasi-isomorphism invariance, cone APIs and
abelian-group tactics. The proof specializes the abstract arguments directly to
the native Hom functor and its projection lemmas. The concrete proof-bearing
Hom-data wrapper from the returned packet is removed; profiling identified its
expansion as expensive. Every helper is private and proved.

The return identified the consumer `Sheaf.Paper.DerivedAutomorphismHomEvaluation`
as quarantined after the old delivery base. Its archive, current rework row,
current node and dependencies were read, and its requested rework claim was
accepted. Restoring the retained adaptation was refused by the delivery tool
because six direct imports were also quarantined; their transitive restoration
would involve 49 modules. The repair instead eliminates the reason for that
adaptation: the shared `coefficientHomComponent` definition is no longer changed.
The consumer adaptation and its coefficient-definition change are removed from
this delivery. The quarantined module, archive, Lean attachment and dependencies
are preserved. No withdrawal or deletion is requested. This is a substantive
change to the proof implementation and local normalization definitions, not an
unchanged re-push of the returned packet.

Validation: the complete revised module compiled against the published library
from a separate clean sandbox in 58.4 seconds, with no warnings and no holes.
Diagnostic prefix compiles were used only for profiling; the delivered module
remains one file. The delivery command runs its normal compile and axiom checks.
All Lean lines are at most 100 characters.

## Proved and sorry left

Closed all three original holes, with complete Lean proofs:

- `CategoryTheory.RingedHomUniverses.rightShift_existsUnique`
- `CategoryTheory.RingedHomUniverses.leftShift_existsUnique`
- `CategoryTheory.RingedHomUniverses.hom_isTriangulated`

All belong to `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
Zero holes remain in the item, zero holes are added, and zero statements are
split off. The proof uses existing declared dependencies as permitted in stage 3.
No quarantined module or its existing holes is added to the live tree by this
revised packet.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft`
- `WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Homology.HomComplexMappingCone`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The independent-universe proof does not use the small-universe derived shift
lemmas or the existing small-universe Hom-cone theorem. It establishes the
projection and cone identities generically and specializes them. It needs no
K-flat representative, Hom-tensor currying or restriction to a localized site.
The shared node also describes other clauses, so their dependencies are retained;
none of these modules is claimed globally pruned or withdrawn.

The returned packet's adaptations of
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation` and
`Sheaf.Paper.DerivedAutomorphismHomEvaluation` are no longer needed. Their change
records and the coefficient node adaptation are omitted from this packet. Neither
module is deleted, emptied or detached from its DAG node.

## Where the brief, the DAG or earlier work was wrong

The small-universe shift and cone statements do not directly give these normalized
independent-universe comparisons. The ordinary product calculation followed by
localization supplies them, preserving the unit route. No mathematical statement
was found false, and no target statement was changed.

The previous packet unnecessarily changed the shared coefficient projection to
use its named API, requiring a consumer adaptation that subsequently became a
quarantine restoration. The API can be used directly in this module instead.
Fresh compilation also exposed the cost of the concrete Hom-data wrapper; direct
specialization of the existing projection lemmas removes it. The final packet
therefore needs neither that shared definition change nor the consumer restore.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
