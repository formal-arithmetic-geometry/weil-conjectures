## What changed

Repair of the return for reviewed head `4ada08f3dec` (reviewer C-4ada0).
Retain the reviewed proof packet and deliver it on current `sheaf-dag`.
The landing returned the status check for
`coord/changes/coefficient-total-tensor-sharing.md`. The current
`tools/stage3_delivery.py` checker requires delivered records to start with `open`;
the diagnostic describes that required value. The named record now has exactly
`open` in its Status section, with the lifecycle explanation moved into Reason.
All six delivered change records use `open`; no unperformed landing or global
verification is asserted. The delivery tool fetches and creates the delivery
commit on current `sheaf-dag`. No quarantined module is withdrawn.

Compared all 13 retained Lean files with the current shared source. The two
consumer copies are unchanged; the packet closes the item's one original hole
and the adapted etale tensor-instance hole, and adds five proved helper modules.
This status repair adds no Lean edits or holes.

Proved `finiteHomNuTensor_existsUnique` by tensor-model descent. The proof constructs
and compares the representative square in an abstract category, converts the square
back to the specified normalization, and uses fully faithful restriction for uniqueness.
The assigned theorem's signature is unchanged.

The retained definition repairs share category, tensor and normalization data
before coefficient specialization. This avoids repeated endpoint conversions in
the source presentation, intrinsic chain comparison and K-flat reflection proof.
The six change records describe the constructors and their users. This repair
preserves those reviewed changes.

Added the resolving K-flat representative and reflection lemmas, the source localization
presentation, the natural chain tensor comparison, and their combined presentation.
The resolving representative and reflection proofs use existing flat-resolution,
localization and exact-comparison declarations. The source presentation uses the
K-flat invertibility of the localization tensorator and the existing normalizations.
The chain naturality proof lifts the existing normalized ordinary tensor natural
isomorphism to total complexes and identifies its components by chain-normalization
uniqueness. The comparison is assembled over an arbitrary finite ring before
specialization; `FiniteHomChainTensorNaturalityAux` shares its functor data.
The component equation is packaged as heterogeneous equality. The final
normalization retains the same square with a pointwise native source model map
and isomorphism certified equal to the specified maps; substitution gives exactly
the old equation. Equality certificates for native maps and isomorphisms are converted to
ordinary equality only in the abstract uniqueness proof.

The definition changes share the same internal Hom, total tensor, localization map,
pure-tensor generators and representative-square predicate before coefficient
specialization. The explicit source total-tensor constructor uses a preadditive monoidal category,
a zero object and small colimits. They avoid expensive repeated definitional conversions. Their complete
bodies and consumer checks are recorded in the change records. The two unclaimed
intrinsic comparison modules also share the same ordinary tensor-comparison type
before site specialization; their constructions and normalization equations are retained.
The chain-isomorphism type, its unique normalized choice, and the target total-tensor
constructor are also shared before coefficient specialization. The finite-level
chain comparison specializes exactly that unique source choice. Review of the
meaning of every target using these definitions is reopened. Definition bodies and
displayed types of existing declarations do change (listed in the change records); each
new form is definitionally the old one.

Reviewer correction (cc, 2026-10-22, heads ee26d713db5, 4ada08f3dec5 and 91a912d96cae): the delivered
rewrite of `coefficientTotalTensor` in `Sheaf.Paper.CoefficientRingedTensorHomModel` breaks the importer
`Sheaf.Paper.IntegralTensorReductionTowerComparison` (line 122:12, a `rw` after unfolding
`coefficientTotalTensor` no longer matches, because the unfolded term is
`coefficientTotalTensorGeneral …`). The module is restored to its published text, and its node to the
live record. `coefficientTotalTensorGeneral` now lives in `Sheaf.Paper.FiniteCoefficientSiteTensorNaturality`,
its only user; see `coord/changes/coefficient-total-tensor-sharing.md` (withdrawn, status `open`).
This correction was lost twice at landing; a re-delivery must keep it.

## Proved and sorry left

The item has one original hole, `WeilConjectures.finiteHomNuTensor_existsUnique`;
its proof is complete. The existing `WeilConjectures.finiteHomEtaleHasTensor` hole
is also closed by the published tensor instance.

All five new helper modules contain no holes. They prove
`finiteCoefficientKFlatRepresentativesFullyFaithful`, `finiteHomNuKFlatReflection`,
`finiteHomEtaleKFlatTensorPresentation`, `finiteHomNuChainTensor_naturalIso`, and
`finiteHomNuTensorPresentation`. No holes are added or split off. The complete packet and its two existing direct consumers compile together.
Fresh verification for this repair: `LCOMPILE_NO_LOCAL=1 lcompile.py --all`
compiled all 13 sandbox modules on the project server without diagnostics
(exit code 0, 2026-10-22). The initial default run timed out in the adapted etale
module; the script's new local-mirror default was then disabled for the required
server run. No compilation limit was changed.
The normalization retains its shared isomorphism type through specialization;
no compile limit is raised. Delivery performs the required server preflight.

The six pre-existing holes retained unchanged in the adapted étale module are:
`finiteHomEvaluation_naturality`, `finiteHomDerivedBraiding_existsUnique`,
`finiteHomEtaleClosed_existsUnique`, `finiteHomEtaleData_existsUnique`,
`finiteHomQuotient_comp`, and `finiteHomEtaleRepresentativeData_existsUnique`.
The two adapted intrinsic comparison modules, the coefficient tensor-Hom model,
and the finite-level chain module retain zero holes.
All six holes belong to `def-sf-etale-finite-coefficient-hom-arrow`. No definition contains
an unfinished proof.

## No longer needed

Removed the item's redundant direct public import of the K-flat module, which is
still available through its public dependency. Removed redundant direct étale proof
imports from the representative and reflection modules. The presentation's public
naturality import supplies its definition dependency and replaces its redundant
direct public site-chain import; the site-chain module remains needed transitively. The direct generator
extensionality route in the new naturality node is no longer needed: ordinary tensor naturality and the total-bifunctor comparison suffice. Its
earlier direct dependencies `def-sf-finite-coefficient-site-scalar-arrow`,
`def-weil-pbc-proetale-modules`, and
`lem-sf-proetale-sheafification-tensor-comparison` remain needed transitively by
other declarations. No node or module is withdrawn; the unit's own statement and
proof route remain. No adopted source declaration or proved dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The descent step requires a natural chain comparison and a resolving representative
presentation, not merely the existence of the pointwise chain isomorphisms. The new
nodes make these required parts explicit. The large concrete monoidal structures also
require sharing before specialization; the change records describe the identical
constructions and predicates used to do that.

## New nodes

`lem-sf-finite-coefficient-kflat-representatives` proves fully faithful restriction
along the resolving subcategory of complexes whose inverse images are K-flat.

`lem-sf-finite-coefficient-kflat-reflection` reflects intrinsic K-flatness using exact
faithful inverse image and its tensor comparison.

`lem-sf-etale-kflat-tensor-presentation` restricts the localization tensorator to K-flat
representatives and transports it to the chosen closed tensor and specified map.

`lem-sf-finite-coefficient-site-tensor-naturality` assembles the specified pure-tensor
chain comparisons into a natural isomorphism.

`lem-sf-finite-coefficient-site-tensor-presentation` combines these results into the
three inputs to generic tensor-model descent.

Change records: `coord/changes/finite-etale-internal-hom-sharing.md`,
`coord/changes/finite-etale-representative-model-sharing.md`,
`coord/changes/finite-hom-nu-tensor-normalization-sharing.md`, and
`coord/changes/finite-ordinary-tensor-comparison-sharing.md`,
`coord/changes/finite-chain-comparison-sharing.md`, and
`coord/changes/coefficient-total-tensor-sharing.md` (withdrawn by the reviewer).

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
