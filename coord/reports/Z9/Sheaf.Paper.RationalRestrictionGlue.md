## What changed

Proved AlgebraicGeometry.ProEtale.CondensedRing.rationalRestrictionGlue with its
existing statement and both restriction functor definitions unchanged. The proof
follows the unit's local affine factorization, finite-cover gluing, compact-support
preservation, and restriction of the supplied adjunction.

The finite-open gluing assertion reuses bounded_finiteOpenDescent and
cohomology_finiteOpenDescent. Despite their integral namespace, these proved lemmas
accept arbitrary condensed commutative coefficients, including empty schemes and
empty covers. Isomorphism closure transports between the canonical derived open
pullback models. The Dctf = Dbc equality comes from localizingClosure_ctf_equals_bc
for exactly the finite-extension or finite-subextension-valued Qbar coefficient.

The local preservation clause of restrictionLocal requires auxiliary adjunctions
for the projection and closed immersion in each chart. The proof supplies them
from exists_localizingExceptionalAdjoint and compactificationOverField, after
transporting the affine charts to their open ranges and establishing finite-type,
separatedness and quasi-compactness instances. The final Hom equality is checked
by unfolding the full-subcategory restriction of the original adjunction.

Updated det-thm-restriction-glue's proof and proof dependencies to this route and
aligned the theorem's proof docstring with it. No new modules or definitions.

The earlier sandbox coefficient repair was independently landed by A4 as
20261019T154003-L-3023734. The shared admissible-coefficient predicate now contains
exactly the missing alternative; RationalExceptionalRestriction already has the
required injection. Removed the superseded copies, definition-node update and
change record from this packet; their earlier work is archived under scratchpad.
This delivery uses the landed interfaces and changes only the assigned Lean module
and its proof-route node.

Validation: the retained three-module packet compiled cleanly on resumption
(0.1 s, 35.1 s and 3.6 s). The final single-module packet is checked again against
the current shared coefficient interface by lcompile.py and deliver3.py. The exact
theorem signature and public import list are textually identical to the baseline.

## Proved and sorry left

Closed one hole: AlgebraicGeometry.ProEtale.CondensedRing.rationalRestrictionGlue
(node det-thm-restriction-glue). The assigned module now has zero sorry occurrences.
Added zero holes and split off zero statements. Existing dependencies, including
restrictionLocal, localizingClosure_ctf_equals_bc and compactification_localizing,
retain their existing holes; this delivery adds none and does not claim their proofs.

## No longer needed

Removed proof imports Sheaf.Paper.CoefficientHeart,
Sheaf.Paper.CartesianCoefficients,
Sheaf.Paper.CoefficientHeartCommonStratification,
WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme,
Mathlib.AlgebraicGeometry.Morphisms.Immersion,
Sheaf.Paper.CondensedConstantConstructibility,
WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic, and
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible.
Definitions needed from these last modules remain available through the retained
public interfaces; no public import was removed from the assigned module.

The proof no longer directly uses sk-lem-coefficient-heart,
det-lem-coefficient-heart-common-stratification,
lem-weil-pbc-reduced-induced-closed-subscheme, or
sk-prop-sfb-cartesian-coefficients. Their four old tool_uses approvals are withdrawn.
The generic descent lemmas already provide the boundedness and actual scheme-stratum
gluing, and the Dctf = Dbc theorem gives the Tor comparison. These modules need not
be direct proof dependencies of this item. This is direct-dependency pruning;
other existing proofs may still import them.

The explicit import of Sheaf.Compactification.BoundaryRefinement remains for the
unit-route boundary compactification convention required by preflight. The unit's
steps remain: local affine factorization and its local constructibility theorem;
gluing cohomological bounds and constructible strata on a finite open cover;
compact-support preservation; the same adjunction restricted by fullness.

## Where the brief, the DAG or earlier work was wrong

The former admissible-coefficient predicate omitted the finite-subextension-valued
Qbar object required by the item. A4 has now repaired the shared interface, retaining
the separate all-continuous-map coefficient. No coefficient repair remains in this
delivery.

restrictionLocal does not immediately return a finite cover of bounded constructible
restrictions: its universal local clause requires auxiliary projection and closed
immersion adjunctions. These are supplied from the existing Brown existence theorem;
no new preservation hypothesis is assumed. Its Fin n cover must also be used at its
own universe rather than at the public assertion's arbitrary Type w.

The upstream BrownHypotheses dependency already marks its arbitrary-field compactness
claim STATEMENT-DISPUTED because the base need not have finite cohomological dimension.
This delivery uses the existing exists_localizingExceptionalAdjoint declaration for
auxiliary chart adjunctions, as the stage-3 plan requires. It does not resolve that
upstream dispute or claim independence of existing sorry axioms. The assigned
theorem's hypotheses and conclusion are unchanged.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
