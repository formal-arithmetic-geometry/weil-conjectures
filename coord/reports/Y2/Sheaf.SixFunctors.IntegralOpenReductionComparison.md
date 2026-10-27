## What changed

Extracted the unchanged definitions through IntegralOpenReduction.Comparison into
Sheaf.SixFunctors.IntegralOpenReductionDefinitions and publicly re-exported them from
the item. This breaks the cycle between the item and its intended proof dependencies.
The extracted declarations were compared byte-for-byte with the original before adding
local elaboration attributes. Their statements and bodies remain unchanged.
The existing definition nodes now attach to its new owner; the theorem retains its
original name and signature. The two existing definition nodes own all relocated declarations.

The item assembles the evaluation calculi, normalized semilinear tensor model and
actual reconstruction units. The canonical restriction-model theorem supplies the
mate of the inverse extension comparison. Only this isomorphism and its mate equation
are needed; its extra representative data are discarded. Restriction completeness
is the existing theorem. Proved private generic adjunction helpers construct the
inverse-unit realization isomorphisms and establish reductionD. The mate identities,
unit naturality and triangle identities prove the strict system and realized
unit/counit equations. StrictModel retains the original simultaneous tensor witnesses.
The residue-field invertibility instances come from evaluating the global units.

NormalizedOpenSections uses the identity-block normalized open localization at every
open. IntegralOpenExtensionComplete proves the independent-universe completeness bridge:
quotient projections and finite constant sections identify the actual uniformizer
under slice transport; linearity of the open adjunction unit gives scalar preservation.
Quasi-compact open extension preserves countable products. The proved private principal
completion helpers of CompletedDirectImagePreservesCompleteness then give the original
quotient completeness, with no boundedness requirement and no new hole.

Three dependent modules redirect their public definition import to the new owner:
OpenSemilinearTensorModelData, CanonicalOpenRestrictionModel and OpenRestrictionCompleteness.
The shared OpenSemilinearTensorModel proof is retained verbatim. No transport module
or source-library module is changed. The direct realization argument avoids the unused
RestrictionModel and CompletionModel clauses of SfOpenReductionAdjunctionTransport.

## Proved and sorry left

Closed the original hole
WeilConjectures.IntegralOpenReduction.integralOpenReductionComparison
(node lem-sf-integral-open-reduction-comparison). The item now has zero sorries.

Added two proved theorems, with zero holes:
- WeilConjectures.IntegralOpenReduction.normalizedOpenSections
  (node lem-sf-normalized-open-section-existence), by the existing identity-block
  normalized open localization.
- WeilConjectures.IntegralOpenReduction.integralOpenExtensionComplete
  (node lem-sf-integral-open-extension-complete), by actual scalar preservation,
  exactness, countable product preservation and principal-completion transport.

Holes closed: 1. Holes added: 0. No unfinished statement is split off.
The adapted canonical-model dependency retains its existing hole:
WeilConjectures.CanonicalOpenRestriction.canonicalOpenRestrictionModel.
This is an existing stated dependency, not an added obligation.
E2 proved openRestrictionComplete while this delivery was checking. Its current
complete proof is preserved verbatim, with only the required import redirect. The current shared
OpenSemilinearTensorModel proof is retained; its old sandbox sorry is not reintroduced.
There is no sorry in a definition or private helper.

The scalar/product/principal-completeness argument compiled in 23.9 seconds;
the assembled item compiled in 34.9 seconds. The first delivery check correctly
rejected a stale holed copy of E2's newly proved restriction-completeness theorem;
the packet now preserves the current proof with only its forced import redirect.
The packet is checked in import order and by the delivery axiom probe and preflight.

## No longer needed

The original item's following private imports are removed from its direct proof imports:
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.Algebra.Homology.KFlat
- Mathlib.Algebra.Homology.BifunctorShift
- Sheaf.Paper.AdicCoefficientDatum
- Sheaf.Paper.IntrinsicCompletionCompleted
- Sheaf.Paper.CompletedOpenExchangeTransport
- Sheaf.Paper.NormalizedDVREffectivity
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Paper.SfImmersionCompletedPullbackComparison
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.Paper.CompletedConstantSheafReduction
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.Paper.KoszulReconstruction

The private import Sheaf.Paper.SfOpenReductionAdjunctionTransport is also unnecessary:
the proof uses its canonical restriction and completeness dependencies directly and
proves the needed generic realization identities. Its larger representative and completion
models are not required. Its node remains in the library for other consumers.

Their constructions are encapsulated by the tensor and reconstruction interfaces and
the direct generic adjunction argument. This does not withdraw their declarations or claim their DAG nodes are globally
unused. The direct dependency lem-sf-open-quotient-koszul-completeness is replaced by its
principal Koszul/Roos argument already proved in CompletedDirectImagePreservesCompleteness
and the independent-universe open product theorem. Its separate arithmetic and existential
coefficient-model package is not needed by this proof. This does not assert it is globally unused. No blueprint unit route is bypassed,
and no adopted-source declaration or file is removed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned direct imports were cyclic because the intended proof dependencies
imported the item to obtain its definitions. They use those definitions, not its
existence theorem. Separating the definition owner resolves this without changing data.

The published openQuotientKoszulCompleteness interface requires the scheme and
coefficient universes to coincide and chooses a different open-operation presentation.
The item has independent universes and fixed normalized operations, so that theorem
cannot simply be applied. The new, proved bridge fills this interface gap using
the existing principal-completion implementation, including its actual scalar map.

The tensor-model theorem requires a section-identity hypothesis not included in the
sections existence conclusion. The existing normalized block-repeat open-localization
clause supplies it; its identity-block special case at every open avoids assuming such an equation
for arbitrary evaluation isomorphisms. No false statement is alleged.

## Forced adaptations

The original imports cause an import cycle once the item uses the intended proof lemmas:
IntegralOpenReductionComparison → OpenSemilinearTensorModel →
OpenSemilinearTensorModelData → IntegralOpenReductionComparison,
and the analogous path through SfOpenReductionAdjunctionTransport and its two model lemmas.
An attempted compile with stale original-owner artifacts reported:
“environment already contains WeilConjectures.IntegralOpenReduction.extensionSection
from Sheaf.SixFunctors.IntegralOpenReductionDefinitions”. The redirected imports
avoid loading the old owner and preserve every referenced definition.

Only import lines change in the three dependent modules. CanonicalOpenRestrictionModel
and OpenSemilinearTensorModelData are unclaimed. OpenRestrictionCompleteness is held
by E2; its sole edit replaces the original item import by the unchanged definition
owner, breaking the cycle through the item's proof import. Its signature and proof
remain verbatim. The change record lists downstream users and holders. No adopted
source module changes.

## New nodes

lem-sf-normalized-open-section-existence attaches the proved identity-block localization
specialization to NormalizedOpenSections. It supplies exactly the extra hypothesis
needed by the existing simultaneous tensor-model theorem.

lem-sf-integral-open-extension-complete attaches the proved completeness bridge to
IntegralOpenExtensionComplete. It retains the universe independence and the specified
coefficient-normalized operation presentation; its proof is complete from existing
project declarations, with no new sorry.

Change record: coord/changes/integral-open-reduction-definitions.md.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
