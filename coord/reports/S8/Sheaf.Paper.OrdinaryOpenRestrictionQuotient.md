## What changed

Replaced the sole hole in Sheaf.Paper.OrdinaryOpenRestrictionQuotient by an ordinary
adjunction argument. The proved openScalarTransitionCompatibility assembles the
extension tensor comparison into a natural isomorphism of strict systems. The right
mate of its inverse is the restriction map, already compatible with every transition.
A proved generic counit calculation identifies its finite evaluations with the actual
finite mates, retaining all the prescribed coefficient-equivalence units and counits.
The proved natural assembly helper is isolated in SemilinearNaturalIsoAssembly, and
its open-extension specialization in OrdinaryOpenTensorSystemAssembly, to keep each
self-contained construction within the per-file compile limit. This adds no hole.
Finite invertibility and joint faithfulness of ordinary evaluations give the system
isomorphism and exactly the original normalization formula.

Added OrdinaryOpenFiniteRestrictionMate, constructing the finite mate and proving its
component formula, and OrdinaryOpenRestrictionFiniteComponents, proving transport of
restriction evaluation and the generic mate equation. Only finite-level invertibility
remains as a named geometric obligation. There is no new transition hole.

Repaired SemilinearSections.OpenSystems by adding restrictionSections, the identity
on every underlying section. Its two constructors in SemilinearOperationsExistence
and BlockOpenExtensionAssembly supply the field using the already proved
openRestrictionEvaluationSections.choose_spec. The existing tensor evaluation uniqueness
proof reuses one named private inverse and its triangle identity to reduce checking
cost. Local unfolding controls export no changes; generation of unused injectivity
and size lemmas is disabled locally for Data to reduce compilation cost. The direct
consumer SemilinearTensorReductionCochain keeps the same selected comparison locally
irreducible and unfolds it explicitly only for its section law; its original compile
against the repaired interface took 64 seconds. No signature or exported attribute
changes in that consumer. The change record is
coord/changes/S8-open-restriction-evaluation-sections.md. No definition contains sorry,
and no arbitrary data are chosen from an unproved existence theorem.

Validation through lcompile.py passed for the shared definition and 35 consumer
modules: all 30 current direct importers and five importers from an earlier source
snapshot. The clean cochain consumer compiled in 57.1 seconds. The item and all four new support modules also compile within the enforced
per-file limit. Profiling options and traces were removed before delivery. All 32
unchanged importer copies have been removed from the sandbox.

## Proved and sorry left

Closed the item's one hole:
WeilConjectures.CanonicalOpenRestriction.ordinaryRestrictionQuotient
(node lem-sf-open-restriction-ordinary-quotient). The system construction, transition
compatibility, naturality, evaluation calculation and final normalization are proved.

One hole added:
WeilConjectures.CanonicalOpenRestriction.finiteRestrictionMate_isIso
(node lem-sf-ordinary-open-finite-restriction-mate-invertible). This asserts
invertibility at one coefficient level, independently of strict systems and both
OrdinaryModels. It is strictly part of the original argument, rather than a new
existential formulation of that argument. This is a decomposition: one upper hole
closed, one lower hole added, net zero holes closed.

The item has zero holes. OrdinaryOpenRestrictionFiniteComponents, SemilinearNaturalIsoAssembly and
OrdinaryOpenTensorSystemAssembly have zero holes;
the shared definition repair, its constructor adaptations and the private tensor
comparison refactor add zero holes.

## No longer needed

No existing public imports are removed and no module is withdrawn. The old broad
proof-plan dependencies lem-sf-open-tensor-normalization
(Sheaf.SixFunctors.OpenTensorNormalization), lem-coef-semilinear-derived-sections
(Sheaf.Paper.SemilinearDerivedSections), and
lem-trf-completion-unit-ordinary-adjunction
(Sheaf.Paper.CompletionUnitOrdinaryAdjunction) are not directly invoked by this proof:
tensor and both ordinary models are supplied as inputs. These dependencies remain
needed elsewhere and some are transitive statement imports. The actual proof uses
the existing open scalar transition compatibility, system isomorphism assembly and
open-system counit evaluation, the proved mate calculation, and finite mate
invertibility. The first draft's separate transition obligation was eliminated before
delivery by assembling the extension comparison and taking its right mate.

## Where the brief, the DAG or earlier work was wrong

The claimed section-normalized operations were not fully normalized. OpenSystems
allowed restrictionEvaluation to be twisted independently at each finite level;
twisting extensionEvaluation by the inverse mate retained both specified adjunction
identities. For the identity open, l = 3 and the coefficient ring module tower, use
+1 at level zero and -1 at level one. The item's formula forces the inverse signs as
components of f, which do not commute with reduction modulo 3. Thus the old interface
admits data for which the item is false. The new restrictionSections field records
the literal section identification intended by Stacks 03DJ and already constructed
by both existing constructors. The definition node records the correction and its
67 DAG citers. Targets using this interface require renewed statement review.

The existing openScalarTransitionCompatibility already exposes precisely this
normalization as its hrestriction hypothesis. Once supplied, its proved extension
square removes the need to prove restriction transition compatibility separately.
The unit route sk-thm-sf-compatibility is retained. The item statement and every
Challenge target signature stay verbatim.

## New nodes

lem-sf-ordinary-open-finite-restriction-mate-invertible, module
Sheaf.Paper.OrdinaryOpenFiniteRestrictionMate, isolates finite mate invertibility.
Its docstring gives the complete pure-tensor/slice/sheafification proof and checks
level zero, zero modules and the empty open. Local search also found the proved private
SheafOfModules.scalarOverIso in Sheaf.Algebra.Homology.LocallyFreeDerivedScalars:
it handles the raw slice/change-of-rings comparison, but the remaining obligation
still has to transport it through the supplied coefficient equivalences and identify
it with the generator-normalized mate.

lem-sf-ordinary-open-restriction-evaluation-mate, module
Sheaf.Paper.OrdinaryOpenRestrictionFiniteComponents, records the proved categorical
transport and counit calculation. It contains no sorry. All new nodes include actual Mathlib searches. Change record:
coord/changes/S8-open-restriction-evaluation-sections.md.

lem-coef-natural-system-iso-assembly, module Sheaf.Paper.SemilinearNaturalIsoAssembly,
proves natural assembly from the existing objectwise assembly and sectionwise joint
faithfulness. It has no holes. Splitting this proved categorical helper follows
profiling of its type matching and keeps it independently reusable.

lem-sf-ordinary-open-tensor-system-assembly, module
Sheaf.Paper.OrdinaryOpenTensorSystemAssembly, proves the open-extension step from
the existing scalar transition comparison and the proved natural system assembly.
It has no holes. Its separate check avoids accumulating the large coefficient
interface conversions in the restriction-mate module.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
