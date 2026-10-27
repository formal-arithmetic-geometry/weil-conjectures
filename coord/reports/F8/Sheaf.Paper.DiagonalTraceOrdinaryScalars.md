## What changed

Replaced the proof hole of
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceOrdinaryScalars`
by a complete assembly from two smaller finite-coefficient statements and a
proved completed-coefficient square. Its statement and public import stay verbatim.
The three new modules are private proof imports of the item.

`Sheaf.Paper.DiagonalTraceCompletedScalarSquare` proves the completed square
without a new hole. The completed coefficient map commutes with the constant
structure maps: apply each finite limit projection, use its defining equation,
and apply naturality of the constant inverse-image comparison. Taking adjoints
and evaluating sheafified constants identifies the scalar actions on sections.
The proof constructs linear identity maps, proves their naturality and inverse
identities, and retains the exact sectionwise HEq normalization. No derived
comparison or localization assumption is used by this smaller theorem.

The remaining finite work is separated into a construction at one scheme
(`DiagonalTraceCoefficientRestriction`) and the varying direct-image comparison
for supplied restrictions (`DiagonalTraceVaryingScalarSquare`). The former has
no morphism or direct-image comparison; the latter constructs no restrictions,
coefficient cones or completed comparison. Neither is the original statement
under another name. The original proof applies the first twice, then the varying
comparison, and combines those with the completed square in the published order.

Only the item, its node and three new modules/nodes are included. No other
existing module, signature, instance, attribute or public import changes.

## Proved and sorry left

Original item holes: 1. Closed original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceOrdinaryScalars`
(node `lem-sfb-diagonal-trace-ordinary-scalars`). Zero holes remain in the item.
This is a decomposition: one original hole closed, two smaller holes added;
the packet net is -1. It is not a proof of the full finite-coefficient
construction free of sorry axioms.

Also proved, with no new hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTraceCompletedScalarSquare`
(node `lem-sfb-diagonal-trace-completed-scalar-square`), including all scalar,
naturality and section normalization equations. Its private helpers are proved.

Every hole added by the delivery:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceCoefficientRestriction`,
  node `lem-sfb-diagonal-trace-coefficient-restriction`: the exact finite restriction
  and normalized coefficient/root cones at one scheme.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTraceVaryingScalarSquare`,
  node `lem-sfb-diagonal-trace-varying-scalar-square`: compatibility of varying
  direct image with any supplied normalized residue restrictions.

Both have exactly `:= by sorry`, a complete proof in words and a source. No data
are defined by choosing arbitrary witnesses from these existence assertions.
The main theorem eliminates their existentials only inside a proof.

All four modules passed the prescribed remote compiler in import order. Temporary
profiling showed 29.9 ms elaboration for the coefficient statement; the completed
proof used cumulative 7.33 s tactic execution and 7.29 s typeclass inference.
The profiling options were removed. The original unused existential proof binder
`varying_sections` is preserved verbatim, with a declaration-local unused-variable
linter suppression. The delivery command runs the final compile/preflight and
records its results, including the per-file limit.

## No longer needed

No existing import is removed and no existing module is withdrawn. No global
module pruning is claimed.

The item's former direct proof dependencies are replaced by the three smaller
nodes. The finite coefficient-tower and semilinear-section dependencies are
retained in the single-site and varying nodes. The Chern and coefficient-cone
definitions are used only in the single-site node; the geometric tower data are
used only in the varying node. These are localized requirements, not pruned
mathematics. The completed square needs none of them: it uses only the actual
completed coefficient definitions and the proved constant-sheaf naturality API.

## Where the brief, the DAG or earlier work was wrong

The old plan bundled the two independent schemes' coefficient constructions and
both ordinary squares. Its declared coefficient-tower abelianness and generic
semilinear calculus do not themselves state the finite base-field coefficient
identification and its normalized cones in this presentation. Their signatures
were read before creating the two strictly smaller obligations.

The completed square does have a direct proof, with no K-injective or derived
comparison machinery. Its compatibility is an equality of the actual completed
structural maps, checked by finite projections, not an arbitrary choice of a
functor isomorphism.

Checked the statement boundaries on empty sites, identity morphisms and the
first positive quotient n=0. The single-site construction uses the coefficient
ring isomorphism for E=ULift Q_l, not local freeness of roots or invertibility of
l on the scheme. The varying statement's linearity uses exactly the residue
scalar equation already required of Restriction. The completed proof is valid
for all scheme morphisms. No statement is weakened or marked disputed, and the
blueprint unit route is preserved.

Mathlib searches were run through msearch (LeanSearch, LeanFinder, Loogle and
grep), and the existing native restriction and completed coefficient APIs were
inspected. The native sequence restriction uses different coefficient and target
presentations; it does not directly supply these normalized records. Blueprint
searches for scalar restriction, completed direct image and coefficient cones
found no duplicate of the new statements.

## New nodes

`lem-sfb-diagonal-trace-coefficient-restriction`, in
`Sheaf.Paper.DiagonalTraceCoefficientRestriction`, isolates the coefficient
construction at one scheme from original steps 1 and 2.

`lem-sfb-diagonal-trace-varying-scalar-square`, in
`Sheaf.Paper.DiagonalTraceVaryingScalarSquare`, isolates the varying part of
original step 3 for restrictions that are already supplied.

`lem-sfb-diagonal-trace-completed-scalar-square`, in
`Sheaf.Paper.DiagonalTraceCompletedScalarSquare`, states and proves the completed
part of original step 3. It needs no Chern or localization data.

All three inherit chapter `sec-six-functors-basics` and unit
`sk-prop-diagonal-tower`, and carry a source, proof steps, searches and verbatim
Lean statements. No change record is needed because no other existing module or
node changes.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
