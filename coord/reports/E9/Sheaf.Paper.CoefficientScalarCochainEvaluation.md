## What changed

Replaced the proof hole in `WeilConjectures.coefficientScalarCochainEvaluation`.
The ordinary comparison is the inverse of the restriction-evaluation mate. Its
invertibility follows from the existing proved
`SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso`, specialized
to the identity site functor. The ordinary unit equation follows from the mate
unit identity.

The proved theorem `WeilConjectures.scalarCochainEvaluation_of_unit` and its
private helpers establish the exact-localization square, descend each
scalar datum's cochain unit formula from a K-flat source resolution to every
complex, and combine these formulas using the specified derived transpose
identity. The final cochain equation follows without evaluating a K-flat
resolution. The ordinary comparison is the proved theorem
`WeilConjectures.ordinaryScalarEvaluationUnit`. The item privately imports their
new modules `Sheaf.Paper.OrdinaryScalarEvaluationUnit` and
`Sheaf.Paper.ScalarCochainEvaluationOfUnit`; the former privately imports
`Sheaf.CategoryTheory.SequenceModulePullbackEvaluation`. Each new module publicly
imports `Sheaf.Paper.SemilinearDerivedCalculus` for its statement.

The existing declarations, their statements, public imports and definitions are
preserved. Updated the item's node proof, proof dependencies and proof origin, and added
two nodes for the fully proved generic lemmas. No other existing module or node
is changed.

During profiling, the combined file compiled without proof errors in 61.8 seconds.
Local irreducibility of the large constant-sheaf and chosen-adjoint definitions,
and a private cached evaluation-specialization equality, prevent repeated
unfolding in the final specialization. After those improvements the two generic
parts were moved to their own modules, each subject to the same 60-second check.
No shared definition, declaration signature or instance was changed. Remote
`lcompile.py --all` compiled all three modules cleanly: ordinary comparison
17.0 s, cochain compatibility 34.0 s, item 43.2 s (exit code zero).

## Proved and sorry left

Closed: `WeilConjectures.coefficientScalarCochainEvaluation`
(node `stage3-pur-scalar-cochain-evaluation`), one original hole.

Added holes: none. Remaining holes in the delivered module: none.
The two added public generic lemmas named above are also fully proved.
There are zero split-off holes; this is a proof, not a sorry decomposition.

## No longer needed

No existing import is removed and no module is withdrawn. The following old
proof dependencies are not used by this proof:

- `lem-pur-system-scalar-generators`
  (`Sheaf.CategoryTheory.SystemScalarGenerators`): the inverse-mate unit identity
  replaces a separate calculation on tensor generators.
- `lem-coef-semilinear-derived-sections`
  (`Sheaf.Paper.SemilinearDerivedSections`): the supplied `ScalarSystems`
  structure already includes the required derived transpose identity.
- `lem-coef-derived-system-evaluation-calculus`
  (`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`): no completion calculus or
  preservation of K-flatness by evaluation is required. The cochain unit formula
  extends along a resolution of its source before evaluation.

The statement-level public import of `CoefficientExtensionReductionData` remains
necessary; its public imports are preserved. The listed dependencies may still
be needed elsewhere in the project. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old proof plan suggested constructing ordinary tensor maps and resolving
the evaluated complex. Neither extra construction is necessary: the proved
sequence-site mate lemma constructs the ordinary comparison, and naturality
extends the normalized cochain unit formula to all complexes directly. The
existing mathematical statement and all its edge cases, including zero complexes
and n = 0, are unchanged.

Searches used the required leanfinder, loogle and grep services. Leanfinder
returned ordinary free-module/sheafification API, loogle returned `mateEquiv`
and its unit/counit identities, and grep found no Mathlib scalar-evaluation
result. Direct repository search found the proved sequence-site mate lemma and
the exact-functor localization equations used in the proof.

## New nodes

`stage3-pur-ordinary-scalar-evaluation-unit` realizes
`WeilConjectures.ordinaryScalarEvaluationUnit` in
`Sheaf.Paper.OrdinaryScalarEvaluationUnit`. It constructs the ordinary comparison
and proves its unit equation by the sequence-site mate theorem. This is the
ordinary part of the original argument and has no derived cochain conclusion.

`stage3-pur-scalar-cochain-unit-descent` realizes
`WeilConjectures.scalarCochainEvaluation_of_unit` in
`Sheaf.Paper.ScalarCochainEvaluationOfUnit`. It proves the cochain compatibility
conditional on an ordinary comparison and its unit equation; it does not
construct such a comparison. Its private helpers prove the adjunction square,
exact-localization square and descent of the scalar cochain unit formula.
Both new statements are proved without new holes. No change record is needed.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
