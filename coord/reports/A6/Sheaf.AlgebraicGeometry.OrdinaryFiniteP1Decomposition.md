## What changed

Repair of C-cb404, returned head cb40407402 (2026-10-21): the independent
review passed, but landing failed while opening the unrelated quarantined module
StandardSingleUnionSESPresentation. Its current rework row preserves the source at
quarantine/Sheaf/AlgebraicGeometry/StandardSingleUnionSESPresentation.lean; this
packet neither imports nor changes that module. Its archive, node attachment and
dependencies remain untouched. The retained packet is reapplied to current
sheaf-dag by deliver3.py, which fetches the delivery base before creating its commit.
The existing item theorem signature was compared with the current shared source
and is byte-for-byte identical. Existing node changes remain confined to their
Lean attachments and proof-route fields; their mathematical statements are unchanged.

Fresh server validation for this return: lcompile.py --all compiled all six packet
modules without warnings: Maps 1.1 s, ExchangeIso 1.1 s, EvaluationPullback 1.2 s,
KummerBaseChange 1.2 s, Untwist 1.0 s, item 1.2 s. Actual hole counts remain zero
in the item, one in finiteTwistDerivedEvaluation_pullback, and one in
ordinaryFiniteP1_components_baseChange. This repair introduces no further lemma,
hole, definition change, or pruning beyond the independently reviewed packet.

Repair of reviewer C-0f23c, returned head 0f23cccac4:
R1 removes the duplicate uniqueness module/node and cites F1's existing uniqueness
node in the evaluation lemma. Its signature was compared with the duplicate and
is identical. R2 repoints the existing def-sp-p1-decomposition-arrows Lean location
to OrdinaryFiniteP1DecompositionMaps and retains its ownership of
p1DecompositionTwist and p1DecompositionMap. The new helper definition node owns
only the other helpers. Both untwist and Kummer base-change nodes now cite the
existing arrow definition in stmt_deps; the evaluation node does too. The advisory
removes statement-unused plain imports from the two named-hole modules. No theorem
statement, definition body or completed proof changes in this repair. This repair
adds zero further holes; the original decomposition still adds the two listed below.

Proved `AlgebraicGeometry.Etale.ordinaryFiniteP1Decomposition` from the existing
same-unit positive projective-line adjunction, proper exchange, and two separate
compatibility lemmas. Its statement is unchanged. The final argument assembles the
component squares by the biproduct universal property, proves the source comparison
invertible, and cancels it to obtain the splitting over every base change.

Added complete proofs of invertibility of the exact-mate projective-line exchange
and cancellation of the positive twist. Positive-transport uniqueness reuses F1’s
already landed theorem and node; the duplicate proposed module and node are dropped.
The untwisting proof tensors the given biproduct isomorphism, applies the canonical
proper projection map, and identifies both components by taking their adjoints.

Moved the explicit canonical arrows into OrdinaryFiniteP1DecompositionMaps so that
independent compatibility lemmas can use them without an import cycle. Reused the
existing fully normalized twist data, cached the shift/adjoint/biproduct composites,
and proved the negative-product evaluation equation. The definition change and all
consumer checks are documented in coord/changes/ordinary-finite-p1-canonical-maps.md.
The original item publicly re-exports all its old arrow names. No source-library file
or Challenge declaration is changed.

Current R1/R2 validation: lcompile.py --all compiled all six packet modules
without warnings: Maps 32.3 s, ExchangeIso 9.2 s, EvaluationPullback 22.1 s,
KummerBaseChange 21.0 s, Untwist 33.1 s, item 29.5 s. The effective DAG overlay
has exactly one owner for each of p1DecompositionTwist, p1DecompositionMap and
ordinaryFiniteTwistTransport_unique. The item's theorem signature remains exactly
identical to the current shared source. All proof_deps equal the unions of the
corresponding proof-step uses.

Prior repair validation (before the present R1/R2 repair): lcompile.py --all
recompiled all seven then-proposed packet
modules successfully without warnings; each file took at most 42.2 seconds. A
source-level declaration comparison found no missing original declarations and no
changed original signatures.
GeoP1Cohomology, ProEtaleProjectiveLineTraceSystem and SpP1NormalizedFamilyCore
compiled unchanged against the refreshed packet in 36.1, 43.2 and 56.4 seconds,
respectively, without warnings. The two consumers named in the return therefore
need no source adaptation. Consumer copies used only for these checks remain in
the scratchpad and are not delivered.

Earlier validation: lcompile.py --all compiled all seven packet modules without warnings.
Four downstream modules compiled unchanged against the packet: GeoP1Cohomology,
PurityFrameKummer, PurityFramePrincipalBoundary, and PurityFrameClass. The exact
AmbientDiagonalPurityBaseChange transport-record construction compiled unchanged in
23.3 seconds. Its compact record and all projections are byte-for-byte unchanged.
The generic SupportedTwistMultiplication construction, including both signed
pullbacks, compiled unchanged in a diagnostic prefix in 47.6 seconds. Profiling
shows 29 seconds of kernel checking and 38 seconds of concurrent module linting;
the same baseline prefix exceeded 60 seconds.

Validation limits: the unchanged whole AmbientDiagonalPurityBaseChange and
SupportedCupFunctoriality already exceed 60 seconds against the published baseline.
The whole SupportedTwistMultiplication took 56.8 seconds against that baseline and
exceeded 60 seconds against the packet. Whole-file passes for those three are not
claimed. Their open rework entries, attachments and sources are preserved. No
consumer source is changed and no forced adaptations are present. The change
record lists all ten consumers, including these three and both consumers named
in the return for cd03cf5612.

Repaired the return for cd03cf5612: added ProEtaleProjectiveLineTraceSystem and
SpP1NormalizedFamilyCore to the change record's `## Users` table. Both directly use
p1DecompositionTwist and p1DecompositionMap with their preserved signatures. Their
existing Lean sources and node attachments are retained. Both are unclaimed in the
current shared snapshot. Also listed the archived LocalizedFlagProduct consumer found while checking
quarantined sources; its source and Lean attachment are preserved. This repair
changes the record and report only.

## Proved and sorry left

Original hole closed:

- AlgebraicGeometry.Etale.ordinaryFiniteP1Decomposition
  (thm-amb-p1-decomposition): complete Lean proof from the named dependencies.

New proved declarations:

- AlgebraicGeometry.Etale.isIso_ordinaryFiniteP1Exchange
  (lem-asd-ordinary-finite-p1-exchange-iso).
- AlgebraicGeometry.Etale.isIso_p1DecompositionMap_of_twisted
  (lem-asd-ordinary-finite-p1-untwist).
- AlgebraicGeometry.Etale.p1DecompositionSheafProduct_hom
  (def-asd-ordinary-finite-p1-decomposition-maps).

Every new sorry, each in its own module with source and complete proof in words:

- AlgebraicGeometry.Etale.finiteTwistDerivedEvaluation_pullback
  (lem-asd-finite-twist-derived-evaluation-pullback): compatibility of the actual
  shifted dual-line evaluation and right unit with arbitrary inverse image. This
  has no splitting, direct image, properness, or finite-coefficient hypothesis.
- AlgebraicGeometry.Etale.ordinaryFiniteP1_components_baseChange
  (lem-asd-ordinary-finite-p1-kummer-base-change): the actual Kummer class and the two
  component squares under arbitrary base change. This has no splitting or
  invertibility assertion and no Noetherian hypothesis.

There are zero sorry occurrences in the item, two added elsewhere, and none in any
definition. One original hole is closed and two lower holes are added: this is a
DECOMPOSITION, not a net proof gain. Both retained results are separate parts of the
source argument; neither restates the item. Existing imported holes, including the
positive adjunction and supported Kummer construction, remain existing dependencies.
The proof of untwisting was completed in this session; the two compatibility results
remain deferred after attempts to derive the concrete comparison identities from the
existing monoidal and supported-class APIs.

## No longer needed

No module is withdrawn and no source-library declaration is removed. The original
public imports OrdinaryFiniteP1Arrows, FiniteEtaleTwistLine, and
UpperStarMonoidal.Comparison now occur in the common maps prerequisite and remain
publicly available through it; they are not pruned from the closure.

The parent now needs only OrdinaryFiniteP1Adjunction, the maps prerequisite,
OrdinaryFiniteP1Untwist, OrdinaryFiniteP1ExchangeIso, and
OrdinaryFiniteP1KummerBaseChange directly. Its former tensor-projection, twist,
properness, proper-exchange, supported-Kummer, mate-unit, mate-counit, and inverse-image
monoidal proof dependencies are recorded on the corresponding new lemmas. They are
still needed, not silently discarded.

The extra Noetherianity check using pqf-lem-locnoeth-lft is unnecessary for the
untwisting projection formula: the proved finite-coefficient proper projection
formula in the source library works over arbitrary schemes. The parent's new proof
does not use that step; existing non-proof bookkeeping is preserved. The positive
adjunction still retains its own existing
Noetherian-base hypothesis and dependencies. Consequently this is no claim that the
local-Noetherianity module can be globally withdrawn.

Dropped the unlanded duplicate OrdinaryFiniteTwistTransportUnique module and
lem-asd-ordinary-finite-twist-transport-unique node from the proposed packet.
The evaluation proof plan now cites the already landed
lem-amb-ordinary-finite-twist-transport-uniqueness, with declaration
AlgebraicGeometry.Etale.ordinaryFiniteTwistTransport_unique in
Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness.
Neither compatibility proof currently uses any proof import, since both are still
named holes. Following the advisory, removed all plain imports from them:

- FiniteTwistDerivedEvaluationPullback: OrdinaryFiniteTwistTransportUnique,
  DerivedPullbackTensorSymmetry, UpperStarMonoidal.TensorShiftIso, and
  Purity.Smooth.RegularImmersionReduction.
- OrdinaryFiniteP1KummerBaseChange: OrdinarySupportedCartierKummer,
  OrdinaryFiniteTwistTransportUnique, DerivedPullbackTensorSymmetry, and
  Mathlib.CategoryTheory.Adjunction.Mates.

Their documented proof dependencies remain in the DAG for the future proofs;
no globally pruned modules are claimed. No deleted.txt entry is needed for the
unlanded duplicate, whose file and node do not exist on the shared main branch.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated F1's already landed normalized transport uniqueness
and overlooked the existing owner of p1DecompositionTwist/p1DecompositionMap.
Both issues are repaired as requested; no duplicate is delivered or claimed as new.

The DAG's application of proper projection unnecessarily checks Noetherianity of P.
The actual source declaration
isIso_rightDerivedLowerStarProjectionMap_of_finite only requires properness and a
finite coefficient ring. The new untwisting theorem uses that stronger proved API.

The listed Sheaf.ProperUnboundedBaseChange attachment is private under its _sheaf
name. The source library exposes the proper torsion-ring theorem publicly. Also,
ordinaryFiniteP1Exchange uses the exact termwise mate, whereas the source theorem is
stated for the left-derived mate. The new exchange lemma proves the necessary
transport equivalence rather than treating these maps as definitionally identical.

The stated finite-twist theorem normalizes sheaf-level evaluation and supplies the
unbounded tensor comparison, but it does not itself state the concrete shifted
evaluation/right-unit square needed by the old proof's identification sentence.
That separate coherence statement is made explicit. Likewise the Cartier/Kummer
base-change steps are isolated without importing an unrelated projective-line
integration result from another blueprint unit. The same-unit adjunction route is
preserved.

The canonical-arrow definition repair changes the implementation of transport
construction and categorical composites. The compact transport record and its projections
retain their original signatures. It therefore reopens statement review of targets depending on these
definitions, even though their normalized mathematical maps and all theorem signatures
are preserved. See the change record.

## New nodes

The existing def-sp-p1-decomposition-arrows node is additionally updated only in
its Lean attachment to follow the moved declarations; it is not a new node.
The helper node below explicitly excludes the two declarations owned by it.

- def-asd-ordinary-finite-p1-decomposition-maps:
  Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps.
- lem-asd-ordinary-finite-p1-exchange-iso:
  Sheaf.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso.
- lem-asd-finite-twist-derived-evaluation-pullback:
  Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback.
- lem-asd-ordinary-finite-p1-untwist:
  Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist.
- lem-asd-ordinary-finite-p1-kummer-base-change:
  Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange.

These five new nodes inherit sec-smooth-purity/sk-prop-sf-cbc and specify their source paragraph,
mathematical proof, Lean statement, and three kinds of Mathlib search. The existing
parent's proof route and Lean attachments are updated to match the actual imports.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
