## What changed

Proved `SheafOfModules.ToposScalarMate.topos_scalar_mate_transitivity` in
`Sheaf.Paper.ToposScalarMateTransitivity`, preserving its statement and all public
interfaces. Added proved private helpers for canonical transport between coefficient
adjunctions, the ordinary and derived tower comparisons, their pure-tensor and
cochain normalizations, exact restriction-action squares, and categorical mate
pasting. The balancing maps are the inverses of the specified coefficient mates;
the geometric mates use the given derived geometric adjunctions and their actual
counits. Updated the item's DAG proof to describe this route.

Repair of returned head `291cabbf52e`: removed the duplicate private theorem
`ToposScalarMate.scalar_pure_smul_one` and replaced all three uses with the existing
`ScalarPullback.pure_smul_one`. Added a proof-only
`import all Sheaf.Paper.KFlatScalarComparisonNormalization` to access that private
theorem while retaining the original public import. The binders of the two
lemmas agree exactly; no generalized replacement is needed.

The proof imports the existing normalization, exact restriction composition,
exact-square composition, K-flat pullback, and pasted-counit results privately.
It uses the general unit-localization helper from CokernelAdjointExchange, not
that module's specialized cokernel-exchange assertion. Local proof-valued instances
cache repeated sheaf-composition inference, and
selective transparency keeps the scalar constructions closed during categorical
calculations. Registered backward definitional equations avoid expanding the
derived comparison constructions. The action formula uses the existing `a_h_spec`
lemma, and the unused ChangeOfRings notation scope is removed. No source-library files or consumers are changed.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.ToposScalarMate.topos_scalar_mate_transitivity`
(node `lem-sfb-topos-scalar-mate-transitivity`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No intermediate statement is split off and no definition contains a hole.
The repaired proof compiled cleanly with `lcompile.py` in 46.7 seconds, with
no warnings. Enabling the registered backward definitional equations then
compiled cleanly in 49.3 seconds. The delivery tool runs the remaining preflight checks.
The original public definitions and theorem statement were checked against the
current shared source and are unchanged.

## No longer needed

The proof does not use `lem-trf-ringed-kflat-word-comparison-descent` or its
module `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`; its original
private import was removed. Its obsolete top-level `tool_uses` entry was removed.
The restriction and inverse-image functors are exact, so their action square
passes directly through ordinary derived localization. Taking coefficient mates
then supplies the nonexact scalar-extension square.

The planned separate invocation of `def-pur-sheaf-tensor-product` to check the
balancing square on local tensor generators is unnecessary. Scalar-unit
normalization and linearity determine the ordinary tower formulas, while the
balancing square follows from the restriction-action square. The underlying
tensor definitions remain in use through the existing scalar models; no tensor
module is withdrawn.

The proof no longer imports `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
or applies `lem-sfb-successive-derived-quotient-normalization`. The two elementary
constructions actually needed from its proof, the identity-on-sections restriction
compositor and identity inverse-image presentation, are constructed directly as
private definitions. No existentially chosen scalar models enter the proof.
The Mathlib adjunction-composition API is imported directly. The proof-only
`import all` of scalar normalization now supplies its existing private scalar-linearity
lemma, as requested by the return; the public action characterization still determines
the underlying action map. All original public imports are retained. No module is
withdrawn, and the blueprint unit's own statement and route are preserved.

The duplicate private helper `ToposScalarMate.scalar_pure_smul_one` is removed;
its existing equivalent in scalar normalization supplies all uses. This repair
adds no module or DAG dependency beyond those already required by the proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily repeated the existing private scalar-linearity
lemma. This repair uses that existing theorem directly.

The original first step says to apply successive-derived-quotient normalization
to the six fixed scalar models. Its Lean theorem instead existentially chooses
a family of models and adjunctions. The proof constructs the tower comparisons
for the actual fixed models by uniqueness of left adjoints, and proves
the requested representative formula by explicit adjunction transposition and
exact-compositor factorization. This also avoids the general word-descent step.
The mathematical statement requires no correction.

Invertibility of a coefficient mate is invariant under changing its scalar
adjunctions by canonical adjoint isomorphisms. This removes the need to identify
the existentially supplied adjunctions by their normalization predicates.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
