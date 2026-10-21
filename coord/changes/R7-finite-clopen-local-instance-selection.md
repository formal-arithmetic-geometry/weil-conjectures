# FiniteClopenDerivedDecomposition local instance selection

## Reason

Preflight classifies added `attribute` commands as an interface change and requires this record.
The new calculus import has maximum-universe instances for derived categories and monoidal
structures; letting inference use them leaves an unconstrained maximum. Other automatic sheafify
instances cause expensive elaboration on the large site. Select the existing fixed-universe
instances while elaborating each declaration. All removals use `attribute ... in` and are local
to that one declaration; no consumer instance table, public signature or definition changes.

## Old

The module had no local instance exclusions around its declarations. All existing public
signatures and non-theorem bodies are preserved verbatim.

## New

The following command prefixes each declaration and its docstring; each `in` restores the
previous attribute state after elaborating the following command:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
```

## Users

Direct Lean consumers found by searching both source roots for the module import:

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | No adaptation: scopes restore the instance table after each declaration. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | No adaptation: scopes restore the instance table after each declaration. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | No adaptation: scopes restore the instance table after each declaration. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | No adaptation: scopes restore the instance table after each declaration. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No adaptation: scopes restore the instance table after each declaration. |

No consumer file is edited. Transitive consumers also receive the unchanged public declarations
and restored instance table. This does not reopen a target's mathematical interpretation.

## Status

landed 20261021T194158-L-1441507 2026-10-21 (merge of deliver/R7/Sheaf.Paper.FiniteClopenDerivedDecomposition)
