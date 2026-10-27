## What changed

Reduce `AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_kflat_monoidal_descent`
to the new component theorem `clopen_braided_model_normalization`. The item proves the finite
partition's derived equivalence by reindexing the existing localization equivalence; proves
the generator normalization by evaluating the total-summand formula on pure tensors; proves
uniqueness by cancelling computation/factorization isomorphisms on resolving pairs and using
the existing derived bifunctor extensionality; and assembles the component conclusions.

The new theorem contains only the coherent braided lift with its model and unit squares.
It does not assert uniqueness, pure-tensor normalization, or equivalence for a partition.
Its hypotheses are supplied by the existing tensor-detection theorem. This is a decomposition,
not a net reduction in the hole count.

Extract the existing public interface, from `modulesAbelian` through `familyBraided`, into
`Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization`. Its declarations and bodies
are unchanged and publicly reexported by the item. This permits the new component theorem
to use the normalization predicates without a circular import. It is an interface extraction
for the independently assigned remaining step, not a split to evade a compile limit.
No adopted source-library module changes. See
`coord/changes/P9-clopen-normalization-interface.md`.

## Proved and sorry left

Close the original direct hole in
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_kflat_monoidal_descent`
(node `lem-pur-clopen-kflat-monoidal-descent`) by a complete proof from the named component
step and the existing dependency declarations.

Add one hole, the whole proof of
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_normalization`
(node `lem-pur-clopen-braided-model-normalization`). There are no holes in the interface
module or in the item module. Closed 1, added 1: decomposition, net 0.
The full parent proof compiled in 51.5 seconds after controlling local unfolding and
explicitly supplying the tensor-detection theorem's universe arguments. The extracted
interface and component statement also compile. Final delivery checks run on the clean
files with all profiling and heartbeat diagnostics removed.

## No longer needed

Remove direct proof imports `Sheaf.Algebra.Homology.KFlatTotalTensorModel` and
`Sheaf.Algebra.Homology.RingedTensorComplexConstraints`. Their direct node citations
`lem-pur-kflat-total-tensor-model`, `lem-sf-ringed-tensor-complex-constraints`, and
`def-pur-sheaf-tensor-product` are unnecessary in the item's combining proof. The remaining
coherent-lift step uses native braided localization instead of a repeated coherence check.
The existing public statement imports are reexported through the extracted interface.
`SiteDerivedTensorDescentIndependentCoefficients` remains needed for model extensionality.
The native derived tensor remains needed for its computation isomorphisms.

The old direct tool approvals for tensor-complex constraints and derived symmetric monoidal
coherence are removed from the item node; those definitions remain among its unchanged
statement dependencies. No existing module is withdrawn. In particular the tensor-complex
constraint module remains a proof dependency of the existing derived symmetric monoidal
module, and no whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

An earlier retained attempt claimed a complete proof but still had the original main
`sorry` and instance errors. The immediately resumed packet already contained the
component reduction. Its required first delivery check exposed a timeout in the parent
combination proof. Retain the cancellation, extensionality, and finite-reindexing arguments;
isolate the unfinished coherent model/unit descent as a genuine strictly smaller step.
The current changes control local unfolding of the total tensor, summand inclusions,
pure-tensor construction, normalization predicates and native monoidal structures. Explicit
universe arguments on the tensor-detection theorem prevent expensive inference through the
coefficient-universe maximum. The localization proof extracts only its needed inverse,
unit and counit, leaving the large unused normalization tail untouched. A generic private
lemma checks product reindexing over abstract categories. The final componentwise
choice proof avoids nested chosen witnesses and preserves the exact original conclusion. All these changes
are local proof elaboration controls; no public definition or signature changes.


The original mathematical plan is valid. The unit `sk-def-purity-conv` has no realized
statement or proof steps that this decomposition bypasses. Edge cases were checked: the
reindexing equivalence includes the empty finite type, the resolving-model uniqueness needs
no nonzero coefficient, and the new component statement assumes neither nonempty schemes
nor nonzero coefficients. No target statement or mathematical predicate is weakened.

## New nodes

`def-pur-clopen-monoidal-normalization` records the unchanged normalization interface,
including the model square and canonical inverse tensor/unit maps, extracted from the item.
It adds no mathematical notion and no proof hole.

`lem-pur-clopen-braided-model-normalization` is the remaining component coherent-lift step.
Its docstring and node give the cochain summand comparison, K-flat resolving localization,
normalized braided descent, and cancellation arguments. It leaves uniqueness and finite
partition assembly to the item. Change record:
`coord/changes/P9-clopen-normalization-interface.md`.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
