## Owner

C8, item `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.

## Reason

The four proofs must compare canonical operations through their section and unit
normalizations without unfolding large adjoint and coefficient constructions.
Local irreducibility attributes make these proof checks finish within the
single-file compile limit. Preflight treats added attribute commands
conservatively as interface changes and requires this record, even though the
attributes are local and all existing public definitions and statements remain
unchanged. No dependent module requires adaptation.

## Old

The item had sixteen named theorem holes and no local irreducibility hints for
the canonical adjoints, derived functors, constant sheaf functor, or the
coefficient direct-image maps used by the new proofs. Unification of component
section maps repeatedly unfolded those constructions, causing heartbeat and
single-file timeouts during proof development.

## New

Four theorem holes are proved. The only new data definition is the private,
explicitly constructed `constant_diagram_square` isomorphism. Every existing
signature, public import, public definition body, and instance body is preserved.
No target or mathematical definition changes meaning.

The item uses `attribute [local irreducible]` for
`Functor.leftAdjoint`, `Functor.mapDerivedCategory`,
`Functor.rightDerivedFunctor`, and `constantSheaf`, and within its Evaluation
section for `proEtaleRingDirectImageMap`, `proEtaleConstantDirectImageMap`,
`coefficientMap`, and `VaryingRing.moduleEvalP`. These attributes have local scope;
they guide elaboration inside the item and do not install exported reducibility
attributes in its importers. The proof uses explicit normalization lemmas and
unfolds `VaryingRing.moduleEvalP` explicitly where its chosen specification is
needed. No source file of any attributed declaration is edited.

This record is required because preflight's conservative command-level check
flags added `attribute` commands as potentially changing what importers see.
It documents that flag; it does not authorize any mathematical interface change.
The complete file compiled successfully through `lcompile.py` in 42.1 seconds.

## Users

`tools/downstream.py Sheaf.SixFunctors.SemilinearProperOpenMatePasting --uses
rhoOrdinary_existsUnique evalPushOrdinary_existsUnique evalPullInv_isIso
pi_components` reports zero downstream Lean modules. Its four declaration-use
lists contain only the item itself. The table includes that sole user. DAG
parents with unfinished proofs retain the same statements and dependency route;
no node or module is withdrawn on the basis of the current importer count.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C8 | 4 proofs; interface unchanged. |

No consumer adaptation is required or included. The mathematical statements and
the definitions used by targets are unchanged, so no target statement review is
reopened by this proof-only elaboration adjustment.

## Status

landed 20261021T001113-L-1371573 2026-10-21 (merge of deliver/C8/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
