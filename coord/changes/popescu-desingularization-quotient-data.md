# Popescu desingularization quotient data proof imports

## Reason

The proof adds two proof-only imports and private local helpers to the item module. The
public theorem signature and existing public imports are unchanged. The two new modules
export intermediate theorem statements required by the proof and are recorded as new
DAG nodes; they retain their documented `sorry` proofs for later workers.

## Changes

- `PopescuDesingularizationQuotientData.lean` imports the substitution and inverted
  quotient intermediate modules and adds private proved helper lemmas.
- New public intermediate declarations are confined to their own new modules:
  `Algebra.exists_desingularization_substitution` and
  `Algebra.desingularization_inverted_quotient_equiv`.
- No existing declaration signature or visibility was changed.

## Users

Only the item module imports the two new modules in this delivery; no downstream module
requires adaptation.

## Old

The item had no proof-only imports for the two construction stages and contained the
single target theorem with `sorry`.

## New

The item imports the two new intermediate modules and contains the compiled proof. The
new modules expose only their separately documented intermediate theorem statements.

## Status

landed 20261012T220527-L-1395874 2026-10-12 (merge of deliver/V1/Sheaf.RingTheory.PopescuDesingularizationQuotientData)
