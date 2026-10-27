## What changed

Reduced finiteAdjunctionTransition to the coefficient square, input naturality, and
finiteDualizingCoefficientComparisons for the étale trace conjunct. The first two
are stated as separate proper-part theorems about the defined finiteHorizontal.
The parent proof substitutes the given gamma equations and combines all three.
The naturality statement drops all transition hypotheses; both new statements drop
the isomorphism hypotheses and the unrelated finite-dualizing realization eQ.

Moved the existing H, restrictedTau, HTransition, C, J, JTransition, alpha, scalarHom
and finiteHorizontal construction block verbatim to FiniteAdjunctionTransitionData,
publicly re-exported from the original module. This avoids cyclic imports without
changing any construction, public name or theorem signature. Change record:
coord/changes/N3-finite-adjunction-constructions-relocation.md.

The attempted full tower-pairing calculation is preserved only in scratch/FullProof.lean
and is not part of the delivery. Profiling found expensive kernel comparisons of
nested derived-tensor instance proofs (28–41 seconds for horizontal factorization
alone); generic categorical helpers and proof-sharing attempts did not make the
whole proof fit. This partial packet isolates the two genuine mathematical steps,
rather than splitting proved code to evade the compiler limit.

## Proved and sorry left

The original hole in
WeilConjectures.FiniteAdjunctionTransition.finiteAdjunctionTransition
is decomposed into two strictly proper parts. Its trace conjunct is supplied by the
existing finiteDualizingCoefficientComparisons theorem. No sorry remains in the
item or data module.

Added holes:

- WeilConjectures.FiniteAdjunctionTransition.finiteAdjunctionSquare
  (lem-coef-finite-adjunction-square): coefficient transition compatibility only.
- WeilConjectures.FiniteAdjunctionTransition.finiteAdjunctionNaturality
  (lem-coef-finite-adjunction-naturality): naturality in the input only, with no
  coefficient-transition hypotheses.

Closed 1 original hole by decomposition; added 2 holes. Net -1, not a net proof gain.
No sorry occurs in a definition. The previous unlanded tensor/projection drafts
were removed from this proposed packet, so they add no holes.

## No longer needed

Removed the following direct proof-only imports from the item:

- Sheaf.Paper.ExchangeProjectionSuppliedDomains
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
- Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
- Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
- Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
- Sheaf.Paper.DirectImageChangeRingTranspose
- Sheaf.Paper.RingedExchangeTensorCoherence
- Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
- Sheaf.Paper.ProjectionMateExact
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.PointProEtaleSectionsExact

The parent now needs only lem-coef-finite-adjunction-square,
lem-coef-finite-adjunction-naturality, and lem-coef-finite-dualizing in its proof.
All 15 original top-level tool_uses approvals are withdrawn from that parent,
because its proof no longer applies those tools directly. The proper-part nodes
record the actual underlying tower-pairing and projection dependencies. This is
not a claim that every former dependency is globally unused: statement and
transitive dependencies remain. No module or declaration is withdrawn; no source
library module is edited. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan expands each scalar/projection mate separately. The current
IsSpecified interface supplies a simultaneous pairingEvaluation and
pairingDinaturality equation, giving the shorter proof plan in the new nodes.
coefTowerNaturalCurrying produces some witness M; it cannot directly prove the
statement for the arbitrary supplied M. The arbitrary limitComparison field must
not be used to replace the actual Roos projections.

## New nodes

lem-coef-finite-adjunction-square: the defined coefficient square, before gamma
isomorphisms are substituted. Its proof sketch normalizes evaluation of the same
beta, uses the actual projection cone and trace/Hom transition equations, and curries.

lem-coef-finite-adjunction-naturality: input naturality at one level. Its proof uses
pairingDinaturality and naturality of the composite actual projection; it needs no
coefficient-transition or finite trace-comparison hypotheses.

def-coef-finite-adjunction-transition-data: relocation of the existing construction
block, preserving it verbatim. It adds no new mathematical choice or definition.

Change record: coord/changes/N3-finite-adjunction-constructions-relocation.md.
Validation: lcompile --all compiled all four Lean modules successfully. The first
delivery preflight found a truncated finiteHorizontal signature in the data node;
the record is repaired to match the complete Lean declaration.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
