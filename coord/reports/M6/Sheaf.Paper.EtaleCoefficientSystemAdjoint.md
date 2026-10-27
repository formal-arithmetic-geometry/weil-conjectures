## What changed

The main existence theorem `AlgebraicGeometry.etaleCoefficientSystemAdjoint` is assembled
from the stated Brown-construction, evaluation-bound and quotient-normalization results.
Its finite-level adjoints are transferred along the recorded Brown realization equivalences.
A private exactness/faithfulness argument for restriction to constant scalars transfers the
uniform finite-coefficient amplitude bound. The exchange-mate cube transfers invertibility
of finite-coefficient quotient mates to the strict-system encoding. The remaining fields
are the Brown and evaluation-bound coherence equations.

The abstract inverse-word cancellation and exchange-cube invertibility arguments are
proved private helpers. They keep concrete realization definitions out of rewrite and
typeclass searches. All work stays in this module; no proof is split for the compile limit.

The new proof imports are private. Existing public signatures and definitions are unchanged.
No new public declaration or module is introduced.

Validation: the complete item file compiled cleanly through `lcompile.py` in 56.7 seconds,
with no warnings or errors. The delivery adds no axioms or new holes.

## Proved and sorry left

Closed one of the five original holes: `AlgebraicGeometry.etaleCoefficientSystemAdjoint`.
No holes are added or split off.

The four original holes retained in this packet, all attached to
`lem-pur-etale-coefficient-system-adjoint`, are:

- `AlgebraicGeometry.etaleCoefficientSystemAdjoint_scalar`;
- `AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal`;
- `AlgebraicGeometry.strictEtaleExceptionalTransport_identity`;
- `AlgebraicGeometry.strictEtaleExceptionalTransport_comp`.

## No longer needed

Removed unused private imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`;
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`;
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts`;
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`;
- `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`;
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`;
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`;
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`;
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`;
- `Sheaf.Paper.SemilinearDerivedSections`;

No module is withdrawn. The unfinished transport clauses retain their planned dependencies.
The main existence proof uses the coefficient projection data already supplied by the Brown
record, so it does not separately invoke `etaleSystemCoefficientProjection`.

## Where the brief, the DAG or earlier work was wrong

The scalar-mate and cofinal-mate dependencies are stated using the ringed sequence-site
presentation `Etale.SystemProjection`, whereas this item uses `StrictEtaleCoefficientTransport`
and its representative-normalized exact descent. Their use requires a comparison of those
presentations and their canonical maps, beyond applying the final mate equations. The four
transport holes are retained unchanged; no assertion about their truth is disputed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
