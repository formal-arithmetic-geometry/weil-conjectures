## What changed

Replaced the proof of `CategoryTheory.discreteModules_abelian` in
`Sheaf.CategoryTheory.DiscreteModulesAbelian`. Obtain the abelian structure, additivity,
preservation of finite limits and colimits, and underlying-module detection of exactness
from `Rep.discreteRep_abelian_structure`. Register its abelian and additive instances;
Mathlib's `CategoryTheory.Functor.preservesZeroMorphisms_of_additive` supplies preservation
of zero morphisms. Use the enough-injectives clause of
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings` to finish the conjunction.
Both declarations are the existing dependencies of the node, so the DAG's proof route
and dependencies remain unchanged. No statements, definitions, visibility, or imports changed.

LeanFinder found the additive-functor zero-morphism instance, whose signature and proof
were checked in Mathlib's `CategoryTheory/Preadditive/AdditiveFunctor.lean`. Searches of
the project found the two existing dependency declarations. The final module compiled
through `lcompile.py` in 2.7 seconds with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.discreteModules_abelian`
(node `lem-exc-discrete-modules-abelian`). Added 0 holes; 0 sorries remain in the item.
No new declarations or split-offs. The proof uses the existing stated dependency theorems
`Rep.discreteRep_abelian_structure` and
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings`; their existing holes are
unchanged and are not claimed as closed here.

## No longer needed

None. Both existing proof imports are used. No node, module, or unit-route step is bypassed;
the generic abelian and injective definitions remain implicit in the dependency statements.

## Where the brief, the DAG or earlier work was wrong

None affecting this proof. The declared structural dependency already bundles the abelian
structure and all forgetful-functor properties needed here, and the injective dependency
already includes `EnoughInjectives`, so the stated two-step plan combines directly.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
