## What changed

Restored Sheaf.Paper.ContinuousLatticeFiniteCoproduct from the precise quarantine
path in coord/rework.tsv. The archived complete proof compiles against the current
library. Replaced its private recollement helper at the two open-unit uses with
Adjunction.unit_isIso_of_L_fully_faithful and the public module extension-by-zero
Full/Faithful instances from the adopted source library. No source-library file,
public signature, public import, construction, or target statement changed.

Updated the existing DAG proof, proof_deps, and proof_origin to match this route.
The source-library full-faithfulness node is already Lean-closed. Its categorical
lift to internal modules is the existing public fullyFaithfulOpenImmersionLowerShriek
construction, combining fullyFaithfulMapModLeft with the coefficient comap equivalence.

Validation: archived restoration compiled cleanly in 7.6 seconds; the revised
module compiled cleanly in 8.5 seconds. The original finite-affine-lattice assembly
step from the quarantined ContinuousEtaleLocalLattices consumer also compiled
against the revised interface (4.3 seconds; the extracted scratch module has only
private declarations). The actual consumer remains quarantined and is not changed
or withdrawn. Both the empty-index case and zero-rank modules remain covered by
the same general construction and cover-conservativity argument.

Change record: coord/changes/C2-continuous-lattice-finite-coproduct-restoration.md.

## Proved and sorry left

Zero local holes before restoration and zero after it; zero holes closed and zero
holes added. No decomposition and no split-off result.

The complete proofs are restored for
AlgebraicGeometry.ProEtale.CondensedRing.continuousLattice_finite_coproduct_of_coefficients
and AlgebraicGeometry.ProEtale.CondensedRing.continuousLattice_finite_coproduct
(node lem-weil-pbc-continuous-lattice-finite-coproduct). Every private helper is
fully proved. No sorry remains in the delivered module or is added elsewhere.

## No longer needed

Removed the direct proof import of Sheaf.Paper.CondensedOpenClosedRecollement and
the proof edge to lem-weil-pbc-condensed-open-closed-recollement. This item only
needs invertibility of an open-extension adjunction unit; public full faithfulness
and the generic adjunction API supply it. This does not withdraw the recollement
module or assert that it has no other consumers.

All other archived imports and dependencies remain needed: the raw free-pullback
composition helper from CondensedFieldLfpLocalTriviality, the local-freeness
transport API, the profinite module forget/pullback comparison, open-cover
conservativity, integral coefficient objects, and scheme coproducts. No new node,
no deleted module, and no bypass of a blueprint unit.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine restoration with a complete archived proof, rather than
a fresh sorry. Its absence from lean/ did not make it redundant: the quarantined
ContinuousEtaleLocalLattices module and its DAG parent still use the assembly
result. The archived recollement-helper dependency was unnecessary given the
existing public source-library full-faithfulness API; this delivery removes that
private coupling. No mathematical statement defect was found.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
