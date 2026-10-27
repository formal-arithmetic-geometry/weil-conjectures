## Reason

The completed item compiles without Lean errors but takes 68 seconds, exceeding the
60-second per-file limit. Profiling shows many moderate costs throughout the file;
there is no single slow definition whose unfolding dominates. Extract the independent
already proved generic scalar-comparison block to compile it separately.

## Old

`Sheaf.Paper.RationalStratumFiniteFreeModel` contains the private `GenericScalar`
namespace, including its concrete forward and inverse constructions, generator
lemmas, inverse identities and `scalarModel_spec`. The full file takes 68 seconds.

## New

The same block is in `Sheaf.CategoryTheory.ConstantScalarTowerComparison`, with the
same private signatures and proof bodies and a source/proof docstring on its final
result. The item imports it using a private `import all`. All existing public
signatures, definitions, public imports and exported attributes stay identical.
The local irreducibility attributes inside the extracted namespace move with it;
the item retains its separate local irreducibility attributes on the imported helpers.
The declaration of `presentationModels` is proved from the other four new helpers.

## Users

The current shared source has no direct Lean importers of
`Sheaf.Paper.RationalStratumFiniteFreeModel`, and no outside use of its private
`GenericScalar` declarations. Its DAG parents retain exactly the same public
statements. There are no existing importers to adapt or compile. The item is the
only existing Lean module changed; the extracted module and item are compiled in
import order by `lcompile.py --all` and by delivery validation.

## Status

landed 20261026T235858-L-1464850 2026-10-26 (merge of deliver/F8/Sheaf.Paper.RationalStratumFiniteFreeModel)
