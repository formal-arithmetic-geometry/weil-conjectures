## What changed

Filled five proof bodies in `Sheaf.CategoryTheory.CondensedScalarTensor`.
The ordinary scalar lax structure reuses the explicit, proved
`Mod.restrictionLaxMonoidal` and its tensor-projection equation, via a private
`import all Sheaf.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal`.
Evaluation gives the specified pure-tensor normalization. Uniqueness follows
by cancelling the relative tensor projection and using sheaf tensor extensionality,
followed by induction on ordinary tensor sections.

`scalarSmallColimits` specializes the source library's colimit preservation of
`Mod.comap` and shrinks the indexing universes.
A proved private generic helper constructs the lax tensor map of complexes by
coproduct descent. Its chain-map equation uses the signed tensor differential
and the two lax naturality identities. The normalization determines every degree
map, proving uniqueness. This construction needs no preservation-of-coproducts
assumption on the lax functor.

`regularScalarExist` constructs the actual underlying ring map as a module morphism;
its linearity is the multiplicative law, and faithfulness gives uniqueness.
`regularScalarEquivariant` applies sectionwise injectivity of the specified
underlying scalar-action isomorphism and its action equation, with trivial source
and target coefficient actions.

All existing public statements, definitions, instance attributes and public imports
are preserved. The item node now records these arguments and the remaining derived
existence obligation. No other existing module or node is changed.

Searches used msearch LeanFinder (internal scalar restriction and colimits), Loogle
`CategoryTheory.Mod.comap`, msearch grep for lax scalar restriction, and local source
searches. The decisive existing construction was the proved private ordinary lax
structure in `ScalarExtensionMonoidal`; the general complex tensor construction
was not already available for a merely lax functor.

## Proved and sorry left

Original holes: 6. Closed: 5. Added: 0. Split off: 0.
The following declarations in namespace `CategoryTheory.CondensedDerivedRestriction`
are proved:

- `scalarTensorExist`;
- `scalarSmallColimits`;
- `scalarComplexTensorExist`;
- `regularScalarExist`;
- `regularScalarEquivariant`.

The only remaining hole is
`CategoryTheory.CondensedDerivedRestriction.derivedScalarTensorExist`,
node `def-sfb-condensed-scalar-tensor`. Its complete existing source/proof docstring
and its whole named `by sorry` proof are retained. The required canonical descent
and uniqueness for the unbounded derived scalar lax structure are still open.
The existing generic normalization node `lem-sfb-derived-scalar-lax-normalization`
has no Lean attachment, and is not imported or duplicated here.

Validation: `lcompile.py` compiled the delivered item successfully in 46.3 seconds
(exit code 0), below the 60-second limit.

The private helper `laxComplexTensor_exists` is completely proved.
These are proofs, not decompositions into new unproved assertions.

## No longer needed

None: no existing import, declaration, module, or dependency node is withdrawn.
The original public `CondensedDerivedCup` import is needed by the existing derived
tensor and coefficient definitions. The added private import is needed by the
ordinary lax construction and its proved tensor-projection formula. There were no
original proof dependencies to prune (the item node had empty proof/proof_deps).

## Where the brief, the DAG or earlier work was wrong

The item node had no numbered proof steps despite its six named theorem holes;
the existing declaration docstrings supplied their arguments. This delivery records
the five implemented arguments and the remaining derived step in the node.
No mathematical statement has been corrected or weakened. The blueprint unit and
chapter routes are unchanged. The exact external source request already recorded
for the derived normalization is retained.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
