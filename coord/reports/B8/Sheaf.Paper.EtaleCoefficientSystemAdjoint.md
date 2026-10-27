## What changed

Reduced `AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal` without changing its
signature. The proof obtains the ramification exponent from
`Padic.local_field_coefficient_stages`, identifies its integer-ring homomorphism with
`strictEtaleIntegerMap` on field representatives, and proves the exact positive-index
ideal equality, including index zero. The canonical quotient equivalences supply the
bijective coefficient-stage maps.

Added a geometric bridge module,
`Sheaf.Paper.StrictEtaleIsomorphicStageProjection`, containing normalized quotient
projection faces, a compact-support projection record, and one remaining geometric
existence theorem. Its records contain no exceptional right adjoints or exceptional
comparison maps. No existing definition or public signature is changed.

The private `exceptionalTransportOfProjection` lemma constructs the actual exceptional
comparison as the right mate of inverse projection. It proves the evaluation equation
using `exchangeMate_cube`; componentwise invertibility and joint detection give its
system invertibility. A second application of `exchangeMate_cube` proves the mixed
quotient equation from the two fixed exceptional quotient-mate normalizations. The
finite-level mates in the cofinal specialization are invertible by the existing mate
lemma along equivalences. Thus the combination of the remaining geometric premise
with the arithmetic and exceptional adjunction data is a complete Lean argument.

The identity-transition proof now delegates its unit cancellation to the proved
private categorical lemma `identityUnitSquare`; its sheaf-level statement is unchanged.
A proved local instance wrapper supplies inverse-image additivity directly. The two
new public proof witnesses `strictEtaleProperInverseAdditive` and
`strictEtaleProperDirectAdditive` specialize the existing proper-image additive fields;
they are used as local instances when elaborating the public records. Public witnesses
keep private helpers out of those signatures, and add no hypotheses or data.

The file now respects transparency at its top level. The Brown-realization proof
registers its already-known additivity, exactness and faithfulness explicitly at the
local functor type. The finite-free proof supplies torsion-freeness directly from
injectivity of the field embedding, avoiding a repeated instance search. Derived-type
comparison respects transparency in the public-record and Brown-realization scopes;
explicit evaluation reductions and isomorphism witnesses replace the broad unfolding
previously used by the identity-transition, inverse-image and projection proofs.

The timing repair uses local irreducibility for the private quotient projection and
identity-comparison constructions, with their proved equations retained as the API.
The new mate and cofinal arguments respect transparency and keep the constant-sheaf
and tensor constructions folded. These are local elaboration settings; existing
public definitions, attributes and signatures are unchanged.

Validation: `lcompile.py --all` accepted both delivery modules with exit code 0,
including the per-file compile-time check. The temporary diagnostic module and all
profiling options have been removed.

## Proved and sorry left

Original item: 2 holes. Removed the hole in
`AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal`
(node `lem-pur-etale-coefficient-system-adjoint`).

Untouched item hole:
`AlgebraicGeometry.etaleCoefficientSystemAdjoint_scalar`
(node `lem-pur-etale-coefficient-system-adjoint`).

Added 1 hole:
`AlgebraicGeometry.strictEtaleIsomorphicStageProjection`
(node `lem-pur-strict-etale-isomorphic-stage-projection`).

This is a decomposition: one upper hole removed and one strictly geometric lower
hole added, with no net hole reduction. The new statement does not assert existence,
evaluation, or quotient compatibility of any exceptional adjoint. Those conclusions
are proved in the item from its left-adjoint geometric projection cubes. Every new
private helper is proved. No definition contains a hole.

## No longer needed

No original import is removed; no module is withdrawn. The direct parent dependency
`lem-pur-etale-system-cofinal-mate` is replaced by the geometric strict-stage projection
bridge and the already used local-field arithmetic and categorical mate-cube lemmas.
The old cofinal theorem works in the alternate `Etale.SystemProjection` encoding and
is not applied by this proof. It remains in the library; other consumers are unaffected.
The scalar-mate coherence dependency remains in the plan for the untouched scalar hole.
All other declared parent dependencies remain needed by the existing main, identity,
composition, and finite-free proofs or by the unchanged scalar plan.

## Where the brief, the DAG or earlier work was wrong

The original cofinal dependency is not a directly applicable strict-record theorem:
its coefficients and system categories use `Etale.SystemProjection`, whereas the
item's conclusion uses `StrictEtaleCoefficientTransport` and normalized open/proper
squares. The missing connection is geometric realization in the strict interface,
not the arithmetic ramification step or the exceptional mate calculation. This
packet exposes exactly that connection as the new item and proves the latter steps.

The latest blueprint has moved the ambient operations text to
`sec-six-functors-basics/sk-def-purity-conv/det-def-sf-operations.md`; the recorded
unit has no realized steps to bypass. This delivery retains the assigned strict
coefficient-system theorem and changes no target or unit record.

Edge cases checked in the statements and proof: e=1; n=0 (first exponent e);
positive ramification with e>1; identity selection and coefficient isomorphism;
empty schemes and zero complexes; and zero coefficient rings for the generic
geometric bridge. No claim of faithfulness of evaluation on derived morphisms is
used. Evaluation is used only to detect invertibility of an already defined map.

## New nodes

`lem-pur-strict-etale-isomorphic-stage-projection` owns the new geometric projection
records and the existence theorem in
`lean/Sheaf/Paper/StrictEtaleIsomorphicStageProjection.lean`. Its source is Zheng,
Construction 4.1, Construction 5.15 and Lemma 5.22. The parent proof and proof-dependency
list are updated to the Lean route. Search results and a full construction argument
are recorded in the new node and theorem docstring. No existing definition repair
or consumer adaptation is part of this packet, so no change record is needed. The
parent node also lists the two proved additive witnesses added for elaboration;
their proofs are the existing recorded additive fields, not new obligations.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
