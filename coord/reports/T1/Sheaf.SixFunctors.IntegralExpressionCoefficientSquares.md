## What changed

Repaired D1 from reviewer C-a23e8 (returned head a23e8b02118). The quarantined item's
statement and all three conclusions are preserved. The clause-1 completion proof,
including expression_completion_isIso and expression_integral_domain, is retained.

IntegralCanonicalRealizationSquare now proves its theorem by induction on CanonicalPair.
Identity and composition use functoriality. Proper image uses comparison naturality.
Pull and tensor cancel the images of the actual normalized counits, apply RecursionLaws,
and use the child squares. The tensor case uses both children in the product category.
Open extension uses the smaller openRealization naturality statement and its child
square. Compact support composes the open and proper calculations. The smaller open naturality theorem is also proved, by cancelling the images of the
actual counit and the reconstruction unit in the two openNormalization equations.
Only the basic constructor remains as a separate obligation.

IntegralSupportCounitProjection now proves its theorem from the compactification
component of integralBasicRealization, namely integralSupportTowerNormalization.
A proved helper transports Good (including the retained Origins.transitionSquare)
through an isomorphism. The general domain_of_realization lemma gives constructibility
of H. Another proved helper derives the exact open comparison from openNormalization,
unit naturality, openReduction naturality, and the prescribed counit normalization.
Proper comparison naturality then compares the displayed composite with d_H.
SfQcqsCompactSupportRealizationSpec transports the finiteReductionIso, coefficient
comparison, finiteImageIso and input finiteReductionIso factors. The existing tower
projection and counit_projection evaluate the scalar-adjunction mate. Naturality of
that evaluated counit and supportEvaluation supplies exactly the final rho factor.
No finite-evaluation faithfulness is assumed.

Updated the proof fields of the item and its two retained helper nodes; added two
smaller statement modules and their nodes. No existing library interface is changed.
The SfP1ChartExchange sandbox adaptation and change record have been removed because
that fix is already on main. There are no forced adaptations in this packet.

Validation: lcompile.py compiled all five final modules successfully, with no warnings.
The mandatory deliver3.py run performs the packet preflight and axiom/dependency checks.

## Proved and sorry left

The original sorry in
WeilConjectures.IntegralSystemRealization.integralExpressionCoefficientSquares
is removed by decomposition. Its clause 1 is proved from existing declarations.
The returned whole-clause helper sorries are replaced by proofs:

- WeilConjectures.IntegralSystemRealization.integralCanonicalRealizationSquare.
- WeilConjectures.IntegralSystemRealization.integralSupportCounitProjection.

Exactly one sorry remains in the packet, as a whole public theorem body:

- WeilConjectures.IntegralSystemRealization.integralBasicGeneratorSquare,
  node lem-sf-integral-basic-generator-square. This is only CanonicalPair.basic;
  it has no identity, composition or outer-context closure. The existing
  generatorReductionCoherence theorem supplies finite-word squares; this remaining
  obligation translates the expression generators and their prescribed comparison
  and completion maps to that finite-word interface.

WeilConjectures.IntegralSystemRealization.integralOpenRealizationNaturality is proved.
This primitive open-extension theorem has no expressions, generators or finite projections.

The returned packet had one hole closed and two holes added, hence hole count net +1,
not the reported -1. This repaired packet closes the original hole and adds one smaller
hole: net zero against the original item, and one fewer hole than the returned packet.
This is a decomposition, not a claim of a complete independent proof. The two
whole-clause holes are now proved; the sole new hole is the strictly smaller basic case. No sorry occurs in a definition or private helper, and no
arbitrary data is chosen from an unproved existence statement.

## No longer needed

The completed CanonicalPair induction replaces the proposed use of
lem-sf-expression-contextual-intertwining / Sheaf.CategoryTheory.ExpressionContextualIntertwining.
Its direct import is absent. GeneratorReductionStatement and ringed exchange/tensor
coherence are needed only by the smaller basic-generator node, not by the context
induction. IntegralBasicRealization is not imported by the support proof: its precise
compactification component IntegralSupportTowerNormalization is used directly.

The original direct IntegralCompactSupportCoefficientComparison import is redundant
through the unchanged assembly-data public import. The larger coefficient-comparison
coherence theorem is not used by the support transport; the scalar-adjunction
projection and the definition of the prescribed realization suffice.

lem-cbc-compactifiable-compatible-tower / Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
is removed from the item's proof dependencies. The proof uses the specified
compactification throughout and does not choose a compatible compactification tower.
No module is withdrawn and no claim of global unreachability is made. The unit's
statement and realized proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

The returned helper statements carried all of clauses 2 and 3; removing the single
original sorry by those two sorries was not the requested reduction. This repair
writes the actual context induction and the actual comparison/finite-projection
transport. The sole remaining hole is the basic-generator step of that argument.

The old report's net -1 was incorrect: the hole count was net +1. The stale build
failure history and duplicate Forced adaptations text have been removed. The
SfP1ChartExchange fix already on main is not part of this repair.
The launcher supplied a fresh repair reference clock for returned head a23e8b02118
(repair depth 1); its budget metadata was not modified.

The rework archive was quarantine, not withdrawal. Current main has restored the
original one-hole item; its signature agrees verbatim with this packet. Both retained
helper signatures also agree verbatim with the returned packet. Zero objects, empty opens and repeated tensor
inputs use the same functorial and adjunction calculations; the tensor induction
uses both child squares, and Origins transport checks actual quotient transitions.

## New nodes

lem-sf-integral-canonical-realization-square and
lem-sf-integral-support-counit-projection retain their returned statements and now
have complete proofs. Their proof dependencies describe the actual induction and
the explicit compactification projection transport respectively.

lem-sf-integral-basic-generator-square, module
Sheaf.SixFunctors.IntegralBasicGeneratorSquare, isolates the basic generator case
before any context or composition induction. Its docstring and node give the
primitive generator proof using the already declared reduction coherence lemmas.

lem-sf-integral-open-realization-naturality, module
Sheaf.SixFunctors.IntegralOpenRealizationNaturality, isolates naturality of the
normalized comparison for one quasi-compact open immersion. Its proof in words
uses openNormalization, the actual unit and counit, and openReduction naturality.
The open naturality statement is proved in this packet, rather than left as a new hole.
Both new nodes record LeanFinder, Loogle and Mathlib source searches. No change
record is needed: all existing signatures and definitions are preserved.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
