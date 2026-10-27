## What changed

Replaced the proof hole of `AlgebraicGeometry.Scheme.integralResidueStratum_lift`
without changing its statement, its original public imports, or its docstring.
The proof chooses the existing DVR coefficient datum and normalized coefficient
model, uses the already proved coefficient completeness theorem, and applies
`residue_lisse_perfect_lift` to the stratum. The final local isomorphisms are
transported back by fully faithful scalar restriction on each slice. The private
helpers prove the comparison with representative-based derived restriction and
reflection of slice isomorphisms along a coefficient-ring isomorphism. Two proved private lemmas, registered as local
instances, fix the additive module universe in the generic slice helpers; their
proofs reuse the existing site instances and export no new instance attributes.

Added `IntegralResidueStratumInput` with actual definitions of the coefficient
comparison and stratum pullback, and `IntegralResidueStratumConstant` with the
constant-model comparison. Their two theorem holes isolate the remaining
normalization work. No existing shared definition or statement was changed.
The item node now records this argument and its actual dependencies.

Added `IntegralResidueCoefficientModel`, a narrow structure containing just the
five finite and completed coefficient-comparison fields needed here. Its existence
theorem is fully proved by reusing the existing private coefficient construction.
This avoids a dependency on the larger open-completeness assembly node, which also
covers unrelated open-operation data and leads back to the current item in the DAG.

## Proved and sorry left

This is a decomposition, not an axiom-free closure of the original obligation.
One original hole is closed: `AlgebraicGeometry.Scheme.integralResidueStratum_lift`.
Its composition proof, three private comparison helpers and two private site-instance
lemmas are complete. All four delivered modules compile: coefficient model 17.8 seconds, input
comparison 47.0 seconds, constant comparison 45.4 seconds, and item 57.2 seconds.
Each is within the 60-second per-file limit.

Two holes are added, each exactly a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.integralResidueStratum_input`
  (`lem-weil-pbc-integral-residue-stratum-input`): transport intrinsic completeness
  and the supplied finite-coefficient residue models to the concrete completed
  DVR presentation. It concludes only the hypotheses of the existing lifting
  theorem; it does not produce integral models or a pro-etale covering.
- `AlgebraicGeometry.Scheme.integralResidueStratum_constant`
  (`lem-weil-pbc-integral-residue-stratum-constant`): transport a perfect constant
  complex from the unlifted valuation ring to the original coefficient universe.
  It involves no arbitrary complete input K, residue model, or cover.

The original module has zero remaining holes; the two comparison modules have one
each. `AlgebraicGeometry.Scheme.integralResidueCoefficientModel_exists` is fully
proved and the new coefficient-model module has zero holes.
Net hole change for this packet is +1. No definition contains a hole or obtains
arbitrary data from an unproved existence theorem.

## No longer needed

No module or import is withdrawn, and no global pruning is claimed. Both original
public imports are retained. The DVR completeness calculation is reused from
`Padic.coefficientIntegers_complete` instead of repeated in this module; its
arithmetic dependencies remain transitive dependencies of that existing proof.
The old stratum-restriction and finite-realization normalization work is confined
to the input and constant comparison nodes, rather than falsely marked unused.
The existing residue lifting theorem and the proper-base-change unit route stay.
The full `lem-sf-open-quotient-koszul-completeness` assembly is not used. Its module
remains a private proof import of the new coefficient-model module solely to reuse
`dvrCoefficientModel_exists`; that declaration and the adopted source library are
preserved. The narrow model omits the module equivalence and every completion/open
operation field, which the lifting proof does not require.

## Where the brief, the DAG or earlier work was wrong

The existing `residue_lisse_perfect_lift` uses coefficients in Type u and modules
in Type u, while the target uses ULift integral coefficients in Type (u+1).
Consequently it cannot simply be applied to `pbcIntegralDatum l E`. The proof uses
the existing small DVR datum and projection-normalized coefficient-ring model;
the two remaining comparisons state precisely the necessary universe and
presentation transport. The first delivery preflight also exposed a DAG cycle
when the proved coefficient helper was cited through its larger assembly node.
The helper's proof constructs only finite constants and limits and does not use
that assembly. The new proved coefficient-model node records this precise argument
instead. This is a compatibility gap in the planned direct
application, not a change in the mathematical statement. Empty strata and zero
complexes satisfy both new statements; neither asserts an arbitrary object is
constant without the residue/completeness hypotheses used by the lifting theorem.

## New nodes

`lem-weil-pbc-integral-residue-stratum-input`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-residue-stratum-input.json`,
records the two input comparisons for the existing residue lifting theorem. Its
module also constructs the actual normalized coefficient comparison and derived
stratum inverse image. The proof in words explains the projection squares,
Koszul-unit transport, residue comparison, and generated etale covering sieve.

`lem-weil-pbc-integral-residue-stratum-constant`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-residue-stratum-constant.json`,
records only the perfect constant realization comparison. Its proof in words
uses a bounded finite-projective representative and the normalized adjunction
comparison, with no lifting or completeness theorem hidden in its conclusion.

`lem-weil-pbc-integral-residue-coefficient-model`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-residue-coefficient-model.json`,
records only the normalized coefficient structure and its proved existence. The
private source proof was read in full: its finite comparisons come from constant
sections, its completed comparison from the isomorphism of inverse diagrams, and
its projection identity from the limit universal property. No open-completeness
or lifting result is used in that construction.

No change record is needed: no existing declaration signature or definition was
changed and no other existing module was adapted. The two instance attributes
inside the item are explicitly local; the scanner's advisory about `attribute`
commands does not represent an exported instance or a change for importers.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
